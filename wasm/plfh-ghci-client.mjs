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

// Parse GHC typed-hole diagnostics ([GHC-88464]) into structured goals and valid fits
// so the browser UI can render Agda-mode clickable refinement chips.
function parseTypedHoles(diagText) {
  if (!diagText || !diagText.includes("Found hole:")) return [];
  const holes = [];
  const sections = diagText.split(/(?=^[^\n]*error:\s*\[GHC-88464\])/m);
  const skipFits = new Set(["undefined", "error", "errorWithoutStackTrace"]);

  for (const sec of sections) {
    if (!sec.includes("Found hole:")) continue;
    const goalMatch = sec.match(
      /Found hole:\s+(_[A-Za-z0-9_']*)\s+::\s+([\s\S]*?)(?=\n\s*(?:Or perhaps|Where:|•|\|)|$)/
    );
    if (!goalMatch) continue;
    const name = goalMatch[1];
    const goalType = goalMatch[2].replace(/\s+/g, " ").trim();
    const fits = [];
    const seen = new Set();

    const extractFitsBlock = (headerRe, isRefinement) => {
      const m = sec.match(headerRe);
      if (!m) return;
      const lines = m[1].split("\n");
      for (const line of lines) {
        // GHC indents fit entries with 8 spaces: "        Refl :: forall ..."
        const fm = line.match(/^\s{6,10}([^\s(][^:]*?)\s+::\s+(.*)$/);
        if (!fm) continue;
        const expr = fm[1].trim();
        const typeSig = fm[2].trim();
        if (!expr || skipFits.has(expr) || seen.has(expr)) continue;
        seen.add(expr);
        fits.push({ expr, typeSig, refinement: isRefinement });
      }
    };

    extractFitsBlock(
      /Valid hole fits include\n([\s\S]*?)(?=\n\s*(?:Valid refinement hole fits include|\(Some hole fits suppressed|\|)|$)/,
      false
    );
    extractFitsBlock(
      /Valid refinement hole fits include\n([\s\S]*?)(?=\n\s*(?:\(Some refinement hole fits suppressed|\|)|$)/,
      true
    );

    holes.push({ name, goalType, fits });
  }
  return holes;
}

// Replace the first standalone occurrence of `holeName` (`_`, `_qed`, ...) in `code`.
function applyHoleFit(code, holeName, fitExpr) {
  const escaped = holeName.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const re = new RegExp(`(^|[^A-Za-z0-9_'])(${escaped})(?![A-Za-z0-9_'])`);
  return code.replace(re, (match, prefix, _tok, offset) => {
    const needsParens = /\s/.test(fitExpr) && !/^\(.*\)$/.test(fitExpr);
    const before = code.slice(0, offset + prefix.length);
    const insideApp = /[A-Za-z0-9_')\]]\s+$/.test(before);
    const replacement = needsParens && insideApp ? `(${fitExpr})` : fitExpr;
    return `${prefix}${replacement}`;
  });
}

// Inject refinement-level hole-fit flags when the opt-in toggle is active and a hole exists.
function maybeWithRefinementPragmas(code, refinementEnabled) {
  if (!refinementEnabled) return code;
  if (!/(^|[^A-Za-z0-9_'])_[A-Za-z0-9_']*/.test(code)) return code;
  if (/-frefinement-level-hole-fits/.test(code)) return code;
  return (
    "{-# OPTIONS_GHC -frefinement-level-hole-fits=1 -fmax-refinement-hole-fits=6 -funclutter-valid-hole-fits #-}\n" +
    code
  );
}

// Render interactive Agda-mode hole goal & clickable fit buttons above the raw diagnostic log.
function renderHolePanel(panelEl, diagText, onFill) {
  const holes = parseTypedHoles(diagText);
  panelEl.innerHTML = "";
  if (holes.length === 0) {
    panelEl.hidden = true;
    return;
  }
  panelEl.hidden = false;

  const heading = document.createElement("div");
  heading.className = "plfh-hole-heading";
  heading.textContent = "Typed Holes (Agda-mode — click a fit to refine & re-check):";
  panelEl.append(heading);

  for (const hole of holes) {
    const card = document.createElement("div");
    card.className = "plfh-hole-card";

    const goal = document.createElement("div");
    goal.className = "plfh-hole-goal";
    goal.innerHTML = `<code>${escapeHtml(hole.name)} :: ${escapeHtml(hole.goalType)}</code>`;
    card.append(goal);

    if (hole.fits.length > 0) {
      const fitsRow = document.createElement("div");
      fitsRow.className = "plfh-hole-fits";
      for (const fit of hole.fits.slice(0, 10)) {
        const btn = document.createElement("button");
        btn.type = "button";
        btn.className = fit.refinement
          ? "plfh-hole-fit-btn plfh-hole-fit-btn--refine"
          : "plfh-hole-fit-btn";
        btn.textContent = fit.expr;
        btn.title = `${fit.expr} :: ${fit.typeSig}`;
        btn.addEventListener("click", () => onFill(hole.name, fit.expr));
        fitsRow.append(btn);
      }
      card.append(fitsRow);
    }
    panelEl.append(card);
  }
}

function escapeHtml(str) {
  return str
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;");
}

function mountChapterBar(mountEl, client, chapterModule, ctx, uiState) {
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

  const refineLabel = document.createElement("label");
  refineLabel.className = "plfh-refinement-toggle";
  refineLabel.title =
    "Enable -frefinement-level-hole-fits=1 when checking snippets with typed holes (_) — experimental while GHC valid hole fits are being refined";
  const refineCheckbox = document.createElement("input");
  refineCheckbox.type = "checkbox";
  refineCheckbox.checked = uiState.refinementFits;
  refineCheckbox.addEventListener("change", () => {
    uiState.refinementFits = refineCheckbox.checked;
  });
  refineLabel.append(refineCheckbox, document.createTextNode(" Refinement fits"));

  const statusSpan = document.createElement("span");
  statusSpan.className = "plfh-wasm-status";
  statusSpan.textContent = "Loads on demand";

  actions.append(openBtn, checkAllBtn, refineLabel);
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
  scratchEditor.placeholder = `-- Declarations here automatically import ${chapterModule}\n-- Tip: write a typed hole like _qed to inspect goals & valid hole fits (Ctrl/Cmd+Enter)`;
  const scratchBtn = document.createElement("button");
  scratchBtn.type = "button";
  scratchBtn.className = "plfh-wasm-btn plfh-wasm-check";
  scratchBtn.textContent = "Check Scratchpad";
  scratchWrap.append(scratchSummary, scratchEditor, scratchBtn);

  const holePanel = document.createElement("div");
  holePanel.className = "plfh-hole-panel";
  holePanel.hidden = true;

  const output = document.createElement("pre");
  output.className = "plfh-wasm-output";
  output.hidden = true;

  drawer.append(replRow, scratchWrap, holePanel, output);
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
    const rawCode = scratchEditor.value.trim();
    if (!rawCode) return;
    scratchBtn.disabled = true;
    holePanel.hidden = true;
    statusSpan.textContent = client.booted ? "Checking scratchpad..." : "Starting GHCi Wasm...";
    const res = await client.checkBlock({
      code: maybeWithRefinementPragmas(rawCode, uiState.refinementFits),
      chapterModule,
      chapterPragmas: ctx.chapterPragmas,
      chapterImports: ctx.chapterImports,
      chapterExports: ctx.chapterExports,
    });
    scratchBtn.disabled = false;
    output.hidden = false;
    const combined = [res.stdout, res.stderr].filter(Boolean).join("\n");
    const hasHoles = !res.ok && combined.includes("Found hole:");
    output.dataset.state = res.ok ? "ok" : hasHoles ? "warn" : "err";
    statusSpan.textContent = res.ok
      ? `Scratchpad checked (${res.elapsedMs} ms)`
      : hasHoles
        ? `Typed hole(s) found (${res.elapsedMs} ms)`
        : `Type error (${res.elapsedMs} ms)`;
    output.textContent =
      combined ||
      (res.ok
        ? "Ok, scratchpad typechecked and loaded into GHCi (-XDependentTypes)."
        : res.status);
    if (hasHoles) {
      renderHolePanel(holePanel, combined, (holeName, fitExpr) => {
        scratchWrap.open = true;
        scratchEditor.value = applyHoleFit(scratchEditor.value, holeName, fitExpr);
        scratchEditor.focus();
        runScratch();
      });
    }
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

const PLAYGROUND_PRESETS = [
  {
    id: "induction",
    label: "Peano Induction",
    replHint: "natToInt (plus 2 3)",
    code: `{-# LANGUAGE DependentTypes #-}
module Playground where

import Data.Type.Equality ((:~:) (Refl), trans)
import HaskLib.Nat (Nat (..), congSucc, plus, type (+))

twoPlusThree :: (2 + 3 :: Nat) :~: 5
twoPlusThree = Refl

plusIdentityR :: foreach (m :: Nat) -> plus m Zero :~: m
plusIdentityR Zero     = Refl
plusIdentityR (Succ m) = congSucc (plusIdentityR m)

plusSuc :: foreach (m n :: Nat) -> plus m (Succ n) :~: Succ (plus m n)
plusSuc Zero     _ = Refl
plusSuc (Succ m) n = congSucc (plusSuc m n)

plusComm :: foreach (m n :: Nat) -> plus m n :~: plus n m
plusComm m Zero     = plusIdentityR m
plusComm m (Succ k) = plusSuc m k \`trans\` congSucc (plusComm m k)

natToInt :: Nat -> Int
natToInt Zero     = 0
natToInt (Succ n) = 1 + natToInt n
`,
  },
  {
    id: "holes",
    label: "Agda-mode Typed Hole",
    replHint: ":t twoPlusThree",
    code: `{-# LANGUAGE DependentTypes #-}
module Playground where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..), plus)

-- Click "Check & Load in GHCi", then click the \`Refl\` chip below!
twoPlusThree :: plus 2 3 :~: 5
twoPlusThree = _qed
`,
  },
  {
    id: "lists",
    label: "Prelude List Laws",
    replHint: ":t lengthMap",
    code: `{-# LANGUAGE DependentTypes, NoListTuplePuns #-}
{-# OPTIONS_GHC -fno-enable-rewrite-rules #-}
module Playground where

import Data.Type.Equality ((:~:) (Refl))
import GHC.Types (List)
import HaskLib (congSucc, size)
import HaskLib.Nat (Nat (..), plus)

lengthAppend :: forall a. foreach (xs ys :: List a)
             -> size (xs ++ ys) :~: plus (size xs) (size ys)
lengthAppend []       _  = Refl
lengthAppend (_ : xs) ys = congSucc (lengthAppend xs ys)

lengthMap :: forall a b. foreach (f :: a -> b) -> foreach (xs :: List a)
          -> size (map f xs) :~: size xs
lengthMap _ []       = Refl
lengthMap f (_ : xs) = congSucc (lengthMap f xs)
`,
  },
  {
    id: "sigma",
    label: "Dependent Pair (Sigma)",
    replHint: "extractHalf",
    code: `{-# LANGUAGE DependentTypes, UndecidableInstances #-}
module Playground where

import Data.Type.Equality ((:~:) (Refl))
import GHC.Sigma (Sigma (Pair))
import HaskLib.Nat (Nat (..), plus)

type EvenSigma (n :: Nat) = some (k :: Nat) | plus k k :~: n

halfOfFour :: EvenSigma 4
halfOfFour = Pair 2 Refl

natToInt :: Nat -> Int
natToInt Zero     = 0
natToInt (Succ n) = 1 + natToInt n

extractHalf :: Int
extractHalf = case halfOfFour of
  Pair k Refl -> natToInt k
`,
  },
  {
    id: "debruijn",
    label: "Intrinsically-Typed STLC",
    replHint: "isTwoValue",
    code: `{-# LANGUAGE DependentTypes #-}
module Playground where

import Data.Type.Equality ((:~:) (Refl))
import qualified PLFH.Part2.DeBruijn as DB

-- Capture-avoiding substitution under a binder shifts free variables automatically!
shiftUnderLam
  :: DB.substSingle @(DB.CExt DB.CEmpty DB.TNat)
                    @(DB.TArr DB.TNat DB.TNat)
                    @(DB.TArr DB.TNat (DB.TArr DB.TNat DB.TNat))
       (DB.Lam (DB.Var (DB.S DB.Z)))
       (DB.Lam (DB.Var (DB.S DB.Z)))
     :~: DB.Lam (DB.Lam (DB.Var (DB.S (DB.S DB.Z))))
shiftUnderLam = Refl

isTwoValue :: Bool
isTwoValue =
  let t :: DB.Term DB.CEmpty DB.TNat
      t = DB.termTwo
  in case DB.checkValue t of
       DB.YesVal _ -> True
       DB.NotVal   -> False
`,
  },
  {
    id: "neg",
    label: "Type Error (2 + 2 = 5)",
    replHint: ":k! plus 2 2",
    code: `{-# LANGUAGE DependentTypes #-}
module Playground where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..), plus)

-- GHC rejects this false proof with [GHC-83865] (4 /= 5):
bogus :: plus 2 2 :~: 5
bogus = Refl
`,
  },
];

function mountStandalonePlayground(mountEl, client, uiState) {
  mountEl.innerHTML = "";
  let activePreset = PLAYGROUND_PRESETS[0];

  const presetBar = document.createElement("div");
  presetBar.className = "plfh-preset-bar";
  const presetBtns = new Map();

  const editor = document.createElement("textarea");
  editor.className = "plfh-wasm-editor plfh-playground-editor";
  editor.spellcheck = false;
  editor.rows = 16;
  editor.value = activePreset.code;

  const replInput = document.createElement("input");
  replInput.type = "text";
  replInput.className = "plfh-wasm-repl-input";
  replInput.placeholder = `Try ${activePreset.replHint}, :browse HaskLib.Nat, :t ..., or :k! plus 2 3`;
  replInput.setAttribute("aria-label", "Playground GHCi prompt");

  const selectPreset = (preset) => {
    activePreset = preset;
    editor.value = preset.code;
    replInput.placeholder = `Try ${preset.replHint}, :browse HaskLib.Nat, :t ..., or :k! plus 2 3`;
    for (const [id, btn] of presetBtns.entries()) {
      btn.classList.toggle("plfh-preset-btn--active", id === preset.id);
    }
  };

  for (const preset of PLAYGROUND_PRESETS) {
    const btn = document.createElement("button");
    btn.type = "button";
    btn.className = "plfh-preset-btn";
    btn.textContent = preset.label;
    btn.addEventListener("click", () => selectPreset(preset));
    presetBtns.set(preset.id, btn);
    presetBar.append(btn);
  }
  selectPreset(activePreset);

  const toolbar = document.createElement("div");
  toolbar.className = "plfh-wasm-toolbar";

  const checkBtn = document.createElement("button");
  checkBtn.type = "button";
  checkBtn.className = "plfh-wasm-btn plfh-wasm-check";
  checkBtn.textContent = "Check & Load in GHCi";

  const resetBtn = document.createElement("button");
  resetBtn.type = "button";
  resetBtn.className = "plfh-wasm-btn plfh-wasm-reset";
  resetBtn.textContent = "Reset Example";
  resetBtn.addEventListener("click", () => {
    editor.value = activePreset.code;
  });

  const refineLabel = document.createElement("label");
  refineLabel.className = "plfh-refinement-toggle";
  refineLabel.title =
    "Enable -frefinement-level-hole-fits=1 when checking snippets with typed holes (_) — experimental while GHC valid hole fits are being refined";
  const refineCheckbox = document.createElement("input");
  refineCheckbox.type = "checkbox";
  refineCheckbox.checked = uiState.refinementFits;
  refineCheckbox.addEventListener("change", () => {
    uiState.refinementFits = refineCheckbox.checked;
  });
  refineLabel.append(refineCheckbox, document.createTextNode(" Refinement fits"));

  const statusSpan = document.createElement("span");
  statusSpan.className = "plfh-wasm-status";
  statusSpan.textContent = "Loads Dependent GHCi (Wasm) on first run";

  toolbar.append(checkBtn, resetBtn, refineLabel, statusSpan);

  const holePanel = document.createElement("div");
  holePanel.className = "plfh-hole-panel";
  holePanel.hidden = true;

  const output = document.createElement("pre");
  output.className = "plfh-wasm-output";
  output.hidden = true;

  const replRow = document.createElement("form");
  replRow.className = "plfh-wasm-repl";

  const promptLabel = document.createElement("span");
  promptLabel.className = "plfh-wasm-prompt";
  promptLabel.textContent = "ghci>";

  const replBtn = document.createElement("button");
  replBtn.type = "submit";
  replBtn.className = "plfh-wasm-btn plfh-wasm-eval";
  replBtn.textContent = "Eval";

  replRow.append(promptLabel, replInput, replBtn);

  mountEl.append(presetBar, toolbar, editor, holePanel, output, replRow);

  client.onProgress((p) => {
    const msg = formatProgress(p);
    if (msg) statusSpan.textContent = msg;
  });

  const runCheck = async () => {
    const rawCode = editor.value.trim();
    if (!rawCode) return;
    checkBtn.disabled = true;
    holePanel.hidden = true;
    statusSpan.textContent = client.booted
      ? "Checking..."
      : "Starting Dependent GHCi Wasm...";
    const res = await client.checkBlock({
      code: maybeWithRefinementPragmas(rawCode, uiState.refinementFits),
      chapterModule: null,
    });
    checkBtn.disabled = false;
    output.hidden = false;
    const combined = [res.stderr, res.stdout].filter(Boolean).join("\n");
    const hasHoles = !res.ok && combined.includes("Found hole:");
    output.dataset.state = res.ok ? "ok" : hasHoles ? "warn" : "err";
    statusSpan.textContent = res.ok
      ? `Checked & loaded (${res.elapsedMs} ms)`
      : hasHoles
        ? `Typed hole(s) found (${res.elapsedMs} ms)`
        : `Type error (${res.elapsedMs} ms)`;
    output.textContent =
      combined ||
      (res.ok
        ? "Ok, module typechecked and loaded into GHCi (-XDependentTypes)."
        : res.status);
    if (hasHoles) {
      renderHolePanel(holePanel, combined, (holeName, fitExpr) => {
        editor.value = applyHoleFit(editor.value, holeName, fitExpr);
        editor.focus();
        runCheck();
      });
    }
  };

  checkBtn.addEventListener("click", runCheck);
  wireEditorKeys(editor, runCheck);

  replRow.addEventListener("submit", async (ev) => {
    ev.preventDefault();
    const line = replInput.value.trim();
    if (!line) return;
    replBtn.disabled = true;
    statusSpan.textContent = client.booted
      ? "Evaluating..."
      : "Starting Dependent GHCi Wasm...";
    const res = await client.repl(line, null);
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

  const uiState = { refinementFits: false };
  const standaloneMount = document.getElementById("plfh-standalone-playground");
  if (standaloneMount) {
    mountStandalonePlayground(standaloneMount, client, uiState);
  }
  const chapterMount = document.getElementById("plfh-chapter-playground");
  if (chapterMount && chapterModule) {
    mountChapterBar(chapterMount, client, chapterModule, chapterCtx, uiState);
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

    const holePanel = document.createElement("div");
    holePanel.className = "plfh-hole-panel";
    holePanel.hidden = true;

    const output = document.createElement("pre");
    output.className = "plfh-wasm-output";
    output.hidden = true;

    wrapper.append(bar, editor, replRow, holePanel, output);
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
      holePanel.hidden = true;
      statusSpan.dataset.active = "1";
      statusSpan.textContent = client.booted
        ? "Checking..."
        : "Starting GHCi Wasm...";
      const rawCode = editor.hidden ? initialCode : editor.value;
      const res = await client.checkBlock({
        code: maybeWithRefinementPragmas(rawCode, uiState.refinementFits),
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
        const hasHoles = combined.includes("Found hole:");
        statusSpan.textContent = hasHoles
          ? `Typed hole(s) found (${res.elapsedMs} ms)`
          : `Type error (${res.elapsedMs} ms)`;
        output.dataset.state = hasHoles ? "warn" : "err";
        output.textContent = combined || res.status;
        if (hasHoles) {
          renderHolePanel(holePanel, combined, (holeName, fitExpr) => {
            if (editor.hidden) {
              editor.hidden = false;
              container.hidden = true;
              resetBtn.hidden = false;
              editBtn.textContent = "View Highlighted";
            }
            editor.value = applyHoleFit(editor.value, holeName, fitExpr);
            editor.focus();
            runCheck();
          });
        }
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
