// Main-thread ES module client & Hakyll chapter enhancer for PLFH.
// Zero network cost on page load: the Web Worker and rootfs.tar.gz load
// only when the reader opens the chapter GHCi bar or checks a code block.

export class PlfhGhciClient {
  #worker = null;
  #workerUrl;
  #rootfsUrl;
  #nextId = 1;
  #pending = new Map();
  #progressListeners = new Set();
  booted = false;
  fromCache = false;

  constructor({
    workerUrl = new URL("./plfh-ghci-worker.mjs", import.meta.url).href,
    rootfsUrl = new URL("./rootfs.tar.gz", import.meta.url).href,
  } = {}) {
    this.#workerUrl = workerUrl;
    this.#rootfsUrl = rootfsUrl;
  }

  get rootfsUrl() {
    return this.#rootfsUrl;
  }

  onProgress(fn) {
    this.#progressListeners.add(fn);
    return () => this.#progressListeners.delete(fn);
  }

  #ensureWorker() {
    if (this.#worker) return;
    this.#worker = new Worker(this.#workerUrl, { type: "module" });
    this.#worker.addEventListener("message", (ev) => {
      const msg = ev.data;
      if (msg.type === "progress" || msg.type === "ready") {
        if (msg.type === "ready") {
          this.booted = true;
          this.fromCache = Boolean(msg.fromCache);
        }
        for (const fn of this.#progressListeners) fn(msg);
        return;
      }
      const waiter = this.#pending.get(msg.id);
      if (waiter) {
        this.#pending.delete(msg.id);
        waiter(msg);
      }
    });
    this.#worker.addEventListener("error", (ev) => {
      const errMsg = ev.message || "Web Worker failed to start";
      for (const [id, waiter] of this.#pending) {
        this.#pending.delete(id);
        waiter({ id, ok: false, status: "ERR:worker", stdout: "", stderr: errMsg, elapsedMs: 0 });
      }
    });
  }

  #call(payload) {
    this.#ensureWorker();
    const id = this.#nextId++;
    return new Promise((resolve) => {
      this.#pending.set(id, resolve);
      this.#worker.postMessage({
        id,
        rootfsUrl: this.#rootfsUrl,
        ...payload,
      });
    });
  }

  boot(chapterModule = null) {
    return this.#call({ type: "boot", chapterModule });
  }

  checkBlock({
    code,
    chapterModule = null,
    chapterPragmas = [],
    chapterImports = [],
    chapterExports = null,
    typecheckOnly = false,
    extraGhcArgs = "",
  }) {
    return this.#call({
      type: "checkBlock",
      code,
      chapterModule,
      chapterPragmas,
      chapterImports,
      chapterExports,
      typecheckOnly,
      extraGhcArgs,
    });
  }

  repl(line, chapterModule = null) {
    return this.#call({ type: "repl", line, chapterModule });
  }

  raw(mode, arg1 = "", arg2 = "") {
    return this.#call({ type: "raw", mode, arg1, arg2 });
  }
}

function formatProgress(p) {
  if (p.phase === "cache") {
    return "Loading cached Dependent GHC Wasm...";
  }
  if (p.phase === "download") {
    const mb = (p.loadedBytes / (1024 * 1024)).toFixed(1);
    const tot = p.totalBytes
      ? ` / ${(p.totalBytes / (1024 * 1024)).toFixed(1)} MB`
      : " MB";
    return `Downloading Dependent GHC Wasm (${mb}${tot})...`;
  }
  if (p.phase === "link") {
    return "Linking WebAssembly GHC libraries...";
  }
  if (p.phase === "boot") {
    return "Booting GHCi 10.1 (-XDependentTypes)...";
  }
  if (p.type === "ready") {
    const src = p.fromCache ? "cached" : "loaded";
    return `GHCi 10.1 ready (${src}, ${p.bootMs} ms)`;
  }
  return "";
}

function isModuleHeaderOnly(code) {
  const stripped = code
    .replace(/^\s*(\{-#[\s\S]*?#-}\s*|--[^\n]*\n\s*|\{-[\s\S]*?-}\s*)*/g, "")
    .trimStart();
  if (!/^module\s+[A-Za-z0-9_.]+/.test(stripped)) return false;
  // Check whether every non-comment, non-blank line after `where` is an `import` (or continuation).
  const whereIdx = stripped.search(/\bwhere\b/);
  if (whereIdx === -1) return true;
  const afterWhere = stripped.slice(whereIdx + 5).split("\n");
  let inImport = false;
  for (const line of afterWhere) {
    const t = line.trim();
    if (!t || t.startsWith("--")) continue;
    if (/^import\s+/.test(t)) {
      inImport = true;
      continue;
    }
    if (inImport && /^\s+/.test(line)) {
      continue;
    }
    return false;
  }
  return true;
}

// Parse exported identifiers from a `module Foo (a, B (..), type (+)) where` header.
function parseModuleExports(headerText) {
  const m = headerText.match(/\bmodule\s+[A-Za-z0-9_.]+\s*\(([\s\S]*?)\)\s*where\b/);
  if (!m) return null;
  const inner = m[1].replace(/--[^\n]*/g, "");
  const exports = [];
  let depth = 0;
  let cur = "";
  for (const ch of inner) {
    if (ch === "(") depth++;
    else if (ch === ")") depth--;
    if (ch === "," && depth === 0) {
      exports.push(cur);
      cur = "";
    } else {
      cur += ch;
    }
  }
  if (cur.trim()) exports.push(cur);

  const names = [];
  for (const raw of exports) {
    const t = raw.trim().replace(/^type\s+/, "");
    const id = t.match(/^([A-Za-z_][A-Za-z0-9_']*|\([^)]+\))/);
    if (id) names.push(id[1]);
  }
  return names;
}

// Scrape LANGUAGE pragmas, grouped import statements, and exported names from
// the chapter's module header, plus assemble the full chapter module source.
function scrapeChapterContext(blocks) {
  const chapterPragmas = [];
  const chapterImports = [];
  let chapterExports = null;
  const fullChunks = [];

  blocks.forEach((pre) => {
    const cls = pre.classList;
    if (
      cls.contains("ignore") ||
      cls.contains("spec") ||
      cls.contains("fail") ||
      cls.contains("exercise") ||
      cls.contains("wip")
    ) {
      return;
    }
    const text = pre.textContent;
    fullChunks.push(text);

    if (isModuleHeaderOnly(text)) {
      chapterExports = parseModuleExports(text);
      let currentImport = null;
      const flushImport = () => {
        if (currentImport) {
          chapterImports.push(currentImport);
          currentImport = null;
        }
      };
      for (const line of text.split("\n")) {
        if (/^\s*\{-#\s*LANGUAGE\b/.test(line)) {
          flushImport();
          chapterPragmas.push(line.trim());
        } else if (/^\s*import\s+/.test(line)) {
          flushImport();
          currentImport = line;
        } else if (currentImport && /^\s+/.test(line) && line.trim().length > 0) {
          currentImport += "\n" + line;
        } else {
          flushImport();
        }
      }
      flushImport();
    }
  });

  return {
    chapterPragmas,
    chapterImports,
    chapterExports,
    fullChapterSource: fullChunks.join("\n\n"),
  };
}

function wireEditorKeys(editor, onRun) {
  editor.addEventListener("keydown", (ev) => {
    if (ev.key === "Tab") {
      ev.preventDefault();
      const start = editor.selectionStart;
      const end = editor.selectionEnd;
      editor.value =
        editor.value.slice(0, start) + "  " + editor.value.slice(end);
      editor.selectionStart = editor.selectionEnd = start + 2;
    } else if ((ev.ctrlKey || ev.metaKey) && ev.key === "Enter") {
      ev.preventDefault();
      onRun();
    }
  });
}

function mountChapterBar(mountEl, client, chapterModule, ctx) {
  mountEl.innerHTML = "";
  mountEl.classList.add("plfh-chapter-bar--ready");

  const header = document.createElement("div");
  header.className = "plfh-chapter-bar-row";

  const label = document.createElement("span");
  label.className = "plfh-chapter-bar-title";
  label.innerHTML = `<strong>Interactive GHCi (Wasm):</strong> <code>${chapterModule}</code>`;

  const actions = document.createElement("div");
  actions.className = "plfh-chapter-bar-actions";

  const openBtn = document.createElement("button");
  openBtn.type = "button";
  openBtn.className = "plfh-wasm-btn plfh-wasm-check";
  openBtn.textContent = "Open Chapter GHCi";

  const checkAllBtn = document.createElement("button");
  checkAllBtn.type = "button";
  checkAllBtn.className = "plfh-wasm-btn plfh-wasm-edit";
  checkAllBtn.textContent = "Check Whole Chapter";

  const statusSpan = document.createElement("span");
  statusSpan.className = "plfh-wasm-status";
  statusSpan.textContent = "Loads on demand";

  actions.append(openBtn, checkAllBtn);
  header.append(label, actions, statusSpan);

  const drawer = document.createElement("div");
  drawer.className = "plfh-chapter-drawer";
  drawer.hidden = true;

  const replRow = document.createElement("form");
  replRow.className = "plfh-wasm-repl";

  const promptLabel = document.createElement("span");
  promptLabel.className = "plfh-wasm-prompt";
  promptLabel.textContent = "ghci>";

  const replInput = document.createElement("input");
  replInput.type = "text";
  replInput.className = "plfh-wasm-repl-input";
  replInput.placeholder = `Try :browse ${chapterModule}, :t ..., :k! ..., or any expression`;
  replInput.setAttribute("aria-label", `Chapter GHCi prompt for ${chapterModule}`);

  const replBtn = document.createElement("button");
  replBtn.type = "submit";
  replBtn.className = "plfh-wasm-btn plfh-wasm-eval";
  replBtn.textContent = "Eval";

  replRow.append(promptLabel, replInput, replBtn);

  const scratchWrap = document.createElement("details");
  scratchWrap.className = "plfh-chapter-scratch";
  const scratchSummary = document.createElement("summary");
  scratchSummary.textContent = "Scratchpad (write & check exercises in this chapter)";
  const scratchEditor = document.createElement("textarea");
  scratchEditor.className = "plfh-wasm-editor";
  scratchEditor.spellcheck = false;
  scratchEditor.rows = 6;
  scratchEditor.placeholder = `-- Declarations here automatically import ${chapterModule}\n-- Press Ctrl/Cmd+Enter or click Check Scratchpad`;
  const scratchBtn = document.createElement("button");
  scratchBtn.type = "button";
  scratchBtn.className = "plfh-wasm-btn plfh-wasm-check";
  scratchBtn.textContent = "Check Scratchpad";
  scratchWrap.append(scratchSummary, scratchEditor, scratchBtn);

  const output = document.createElement("pre");
  output.className = "plfh-wasm-output";
  output.hidden = true;

  drawer.append(replRow, scratchWrap, output);
  mountEl.append(header, drawer);

  client.onProgress((p) => {
    const msg = formatProgress(p);
    if (msg) statusSpan.textContent = msg;
  });

  openBtn.addEventListener("click", async () => {
    const opening = drawer.hidden;
    drawer.hidden = !opening;
    openBtn.textContent = opening ? "Hide Chapter GHCi" : "Open Chapter GHCi";
    if (!opening) return;
    replInput.focus();
    if (!client.booted) {
      openBtn.disabled = true;
      statusSpan.textContent = "Starting Dependent GHCi Wasm...";
      const res = await client.boot(chapterModule);
      openBtn.disabled = false;
      if (!res.ok) {
        output.hidden = false;
        output.dataset.state = "err";
        output.textContent = res.stderr || res.status;
        statusSpan.textContent = "Bundle unavailable";
      }
    }
  });

  checkAllBtn.addEventListener("click", async () => {
    drawer.hidden = false;
    openBtn.textContent = "Hide Chapter GHCi";
    checkAllBtn.disabled = true;
    statusSpan.textContent = client.booted
      ? `Checking ${chapterModule}...`
      : "Starting Dependent GHCi Wasm...";
    const res = await client.checkBlock({
      code: ctx.fullChapterSource,
      chapterModule,
    });
    checkAllBtn.disabled = false;
    output.hidden = false;
    output.dataset.state = res.ok ? "ok" : "err";
    statusSpan.textContent = res.ok
      ? `${chapterModule} checked (${res.elapsedMs} ms)`
      : `Check failed (${res.elapsedMs} ms)`;
    output.textContent =
      [res.stdout, res.stderr].filter(Boolean).join("\n") ||
      (res.ok
        ? `Ok, ${chapterModule} typechecked and loaded into GHCi (-XDependentTypes).`
        : res.status);
  });

  const runScratch = async () => {
    const code = scratchEditor.value.trim();
    if (!code) return;
    scratchBtn.disabled = true;
    statusSpan.textContent = client.booted ? "Checking scratchpad..." : "Starting GHCi Wasm...";
    const res = await client.checkBlock({
      code,
      chapterModule,
      chapterPragmas: ctx.chapterPragmas,
      chapterImports: ctx.chapterImports,
      chapterExports: ctx.chapterExports,
    });
    scratchBtn.disabled = false;
    output.hidden = false;
    output.dataset.state = res.ok ? "ok" : "err";
    statusSpan.textContent = res.ok
      ? `Scratchpad checked (${res.elapsedMs} ms)`
      : `Type error (${res.elapsedMs} ms)`;
    output.textContent =
      [res.stdout, res.stderr].filter(Boolean).join("\n") ||
      (res.ok
        ? "Ok, scratchpad typechecked and loaded into GHCi (-XDependentTypes)."
        : res.status);
  };

  scratchBtn.addEventListener("click", runScratch);
  wireEditorKeys(scratchEditor, runScratch);

  replRow.addEventListener("submit", async (ev) => {
    ev.preventDefault();
    const line = replInput.value.trim();
    if (!line) return;
    replBtn.disabled = true;
    statusSpan.textContent = "Evaluating...";
    const res = await client.repl(line, chapterModule);
    replBtn.disabled = false;
    output.hidden = false;
    output.dataset.state = res.ok ? "ok" : "err";
    statusSpan.textContent = `${res.ok ? "Done" : "Error"} (${res.elapsedMs} ms)`;
    const text = [res.stdout, res.stderr].filter(Boolean).join("\n");
    output.textContent = `ghci> ${line}\n${text}`;
  });
}

export function enhancePlfhPage({
  workerUrl,
  rootfsUrl,
  chapterModule = document.body?.dataset?.plfhModule || null,
  selector = "div.sourceCode pre.sourceCode.haskell, pre.plfh-interactive",
} = {}) {
  const client = new PlfhGhciClient({ workerUrl, rootfsUrl });
  const blocks = [...document.querySelectorAll(selector)];
  const chapterCtx = scrapeChapterContext(blocks);

  const chapterMount = document.getElementById("plfh-chapter-playground");
  if (chapterMount && chapterModule) {
    mountChapterBar(chapterMount, client, chapterModule, chapterCtx);
  }

  blocks.forEach((pre, idx) => {
    const cls = pre.classList;
    if (cls.contains("ignore") || cls.contains("spec") || cls.contains("wip")) {
      return;
    }

    const container = pre.closest("div.sourceCode") || pre;
    if (container.dataset.plfhEnhanced) return;

    const initialCode = pre.textContent;
    if (isModuleHeaderOnly(initialCode)) {
      return;
    }
    container.dataset.plfhEnhanced = "1";

    const isFail = cls.contains("fail");
    const isExercise = cls.contains("exercise");
    const expectedCode = container.dataset.expect || pre.dataset.expect || null;
    const blockMod =
      pre.dataset.plfhModule || container.dataset.plfhModule || chapterModule;

    const wrapper = document.createElement("div");
    wrapper.className = "plfh-wasm-widget";

    const bar = document.createElement("div");
    bar.className = "plfh-wasm-toolbar";

    const checkBtn = document.createElement("button");
    checkBtn.type = "button";
    checkBtn.className = "plfh-wasm-btn plfh-wasm-check";
    checkBtn.textContent = isFail
      ? "Verify Failure (Wasm)"
      : isExercise
        ? "Check Solution (Wasm)"
        : "Check in GHCi (Wasm)";

    const editBtn = document.createElement("button");
    editBtn.type = "button";
    editBtn.className = "plfh-wasm-btn plfh-wasm-edit";
    editBtn.textContent = isExercise ? "Solve / Edit" : "Edit";

    const resetBtn = document.createElement("button");
    resetBtn.type = "button";
    resetBtn.className = "plfh-wasm-btn plfh-wasm-reset";
    resetBtn.textContent = "Reset";
    resetBtn.hidden = true;

    const statusSpan = document.createElement("span");
    statusSpan.className = "plfh-wasm-status";
    if (isFail && expectedCode) {
      statusSpan.textContent = `Expected: ${expectedCode}`;
    }

    bar.append(checkBtn, editBtn, resetBtn, statusSpan);

    const editor = document.createElement("textarea");
    editor.className = "plfh-wasm-editor";
    editor.spellcheck = false;
    editor.value = initialCode;
    editor.rows = Math.max(4, Math.min(24, initialCode.split("\n").length + 1));
    editor.hidden = true;

    const replRow = document.createElement("form");
    replRow.className = "plfh-wasm-repl";
    replRow.hidden = true;

    const promptLabel = document.createElement("span");
    promptLabel.className = "plfh-wasm-prompt";
    promptLabel.textContent = "ghci>";

    const replInput = document.createElement("input");
    replInput.type = "text";
    replInput.className = "plfh-wasm-repl-input";
    replInput.placeholder = ":t ..., :k! ..., or any Haskell expression";
    replInput.setAttribute("aria-label", `GHCi prompt for block ${idx + 1}`);

    const replBtn = document.createElement("button");
    replBtn.type = "submit";
    replBtn.className = "plfh-wasm-btn plfh-wasm-eval";
    replBtn.textContent = "Eval";

    replRow.append(promptLabel, replInput, replBtn);

    const output = document.createElement("pre");
    output.className = "plfh-wasm-output";
    output.hidden = true;

    wrapper.append(bar, editor, replRow, output);
    container.insertAdjacentElement("afterend", wrapper);

    client.onProgress((p) => {
      if (statusSpan.dataset.active !== "1") return;
      const msg = formatProgress(p);
      if (msg) statusSpan.textContent = msg;
    });

    editBtn.addEventListener("click", () => {
      const editing = editor.hidden;
      editor.hidden = !editing;
      container.hidden = editing;
      resetBtn.hidden = !editing;
      editBtn.textContent = editing
        ? "View Highlighted"
        : isExercise
          ? "Solve / Edit"
          : "Edit";
      if (editing) editor.focus();
    });

    resetBtn.addEventListener("click", () => {
      editor.value = initialCode;
    });

    const runCheck = async () => {
      checkBtn.disabled = true;
      statusSpan.dataset.active = "1";
      statusSpan.textContent = client.booted
        ? "Checking..."
        : "Starting GHCi Wasm...";
      const code = editor.hidden ? initialCode : editor.value;
      const res = await client.checkBlock({
        code,
        chapterModule: blockMod,
        chapterPragmas: chapterCtx.chapterPragmas,
        chapterImports: chapterCtx.chapterImports,
        chapterExports: chapterCtx.chapterExports,
      });
      statusSpan.dataset.active = "0";
      checkBtn.disabled = false;
      output.hidden = false;

      const combined = [res.stderr, res.stdout].filter(Boolean).join("\n");
      if (isFail && expectedCode) {
        if (!res.ok && combined.includes(expectedCode)) {
          statusSpan.textContent = `Rejected as expected (${expectedCode}, ${res.elapsedMs} ms)`;
          output.dataset.state = "ok";
          output.textContent = combined;
        } else if (res.ok) {
          statusSpan.textContent = `Unexpectedly passed (${res.elapsedMs} ms)`;
          output.dataset.state = "warn";
          output.textContent =
            combined || "Module typechecked (was expected to fail with " + expectedCode + ").";
        } else {
          statusSpan.textContent = `Failed (${res.elapsedMs} ms)`;
          output.dataset.state = "err";
          output.textContent = combined || res.status;
        }
        return;
      }

      if (res.ok) {
        replRow.hidden = false;
        statusSpan.textContent = `Checked (${res.elapsedMs} ms)`;
        output.dataset.state = "ok";
        output.textContent =
          [res.stdout, res.stderr].filter(Boolean).join("\n") ||
          "Ok, module typechecked and loaded into GHCi (-XDependentTypes).";
      } else {
        statusSpan.textContent = `Type error (${res.elapsedMs} ms)`;
        output.dataset.state = "err";
        output.textContent = combined || res.status;
      }
    };

    checkBtn.addEventListener("click", runCheck);
    wireEditorKeys(editor, runCheck);

    replRow.addEventListener("submit", async (ev) => {
      ev.preventDefault();
      const line = replInput.value.trim();
      if (!line) return;
      replBtn.disabled = true;
      statusSpan.dataset.active = "1";
      statusSpan.textContent = "Evaluating...";
      const res = await client.repl(line, blockMod);
      statusSpan.dataset.active = "0";
      replBtn.disabled = false;
      output.hidden = false;
      output.dataset.state = res.ok ? "ok" : "err";
      statusSpan.textContent = `${res.ok ? "Done" : "Error"} (${res.elapsedMs} ms)`;
      const text = [res.stdout, res.stderr].filter(Boolean).join("\n");
      output.textContent = `ghci> ${line}\n${text}`;
    });
  });

  return client;
}
