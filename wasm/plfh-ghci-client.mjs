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
      cls.contains("exercise")
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
      editor.dispatchEvent(new Event("input", { bubbles: true }));
    } else if ((ev.ctrlKey || ev.metaKey) && ev.key === "Enter") {
      ev.preventDefault();
      onRun();
    }
  });
}

function escapeRegex(str) {
  return str.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

function splitTopLevelTypeSig(text) {
  let depth = 0;
  for (let i = 0; i < text.length - 3; i++) {
    const ch = text[i];
    if (ch === "(" || ch === "[" || ch === "{") depth++;
    else if (ch === ")" || ch === "]" || ch === "}") depth = Math.max(0, depth - 1);
    else if (depth === 0 && text.slice(i, i + 4) === " :: ") {
      return {
        expr: text.slice(0, i).trim(),
        typeSig: text.slice(i + 4).trim(),
      };
    }
  }
  return { expr: text.trim(), typeSig: "" };
}

function sanitizeRefinementFit(expr) {
  let out = "";
  const subgoals = [];
  let i = 0;
  while (i < expr.length) {
    const sub = expr.slice(i);
    const m = sub.match(/^\(\s*(_[A-Za-z0-9_']*)\s*::\s*/);
    if (m) {
      let depth = 1;
      let j = i + m[0].length;
      while (j < expr.length && depth > 0) {
        if (expr[j] === "(") depth++;
        else if (expr[j] === ")") depth--;
        j++;
      }
      const innerType = expr
        .slice(i + m[0].length, j - 1)
        .replace(/\s+/g, " ")
        .trim();
      subgoals.push(innerType);
      out += m[1];
      i = j;
    } else {
      out += expr[i];
      i++;
    }
  }
  return { cleanExpr: out.replace(/\s+/g, " ").trim(), subgoals };
}

// Parse GHC typed-hole diagnostics ([GHC-88464]) into structured goals, direct fits,
// subgoal-splitting refinement fits, and pattern-match case-split suggestions.
function parseTypedHoles(diagText) {
  if (!diagText || !diagText.includes("Found hole:")) return [];
  const holes = [];
  const sections = diagText.split(/(?=^[^\n]*error:\s*\[GHC-88464\])/m);
  const skipFits = new Set([
    "undefined",
    "error",
    "errorWithoutStackTrace",
    "errorCallWithCallStackException",
  ]);

  for (const sec of sections) {
    if (!sec.includes("Found hole:")) continue;
    const locMatch = sec.match(/^[^\n]*?:(\d+):(\d+):\s*error:\s*\[GHC-88464\]/m);
    const line = locMatch ? Number(locMatch[1]) : null;
    const col = locMatch ? Number(locMatch[2]) : null;

    const goalMatch = sec.match(
      /Found hole:\s+(_[A-Za-z0-9_']*)\s+::\s+([\s\S]*?)(?=\n\s*(?:Or perhaps|Where:|•|\|)|$)/
    );
    if (!goalMatch) continue;
    const name = goalMatch[1];
    const goalType = goalMatch[2].replace(/\s+/g, " ").trim();

    const eqMatch = sec.match(/In an equation for [‘']([^’']+)[’']:\s*([^\n]+)/);
    const fnName = eqMatch ? eqMatch[1].trim() : null;
    const equationText = eqMatch ? eqMatch[2].trim() : null;

    const fits = [];
    const seen = new Set();

    const parseFitEntries = (rawInline, rawBlock, isRefinement) => {
      const rawItems = [];
      if (rawInline && rawInline.trim()) {
        rawItems.push(rawInline.trim());
      }
      if (rawBlock) {
        const blockLines = rawBlock.split("\n").filter((l) => l.trim().length > 0);
        let baseIndent = null;
        let current = null;
        for (const l of blockLines) {
          const indent = l.match(/^(\s*)/)[1].length;
          const trimmed = l.trim();
          if (baseIndent === null) {
            baseIndent = indent;
            current = [trimmed];
          } else if (
            indent <= baseIndent &&
            !trimmed.startsWith("::") &&
            !trimmed.startsWith("with ") &&
            !trimmed.startsWith("where ")
          ) {
            if (current) rawItems.push(current.join("\n"));
            current = [trimmed];
          } else {
            if (current) current.push(trimmed);
          }
        }
        if (current) rawItems.push(current.join("\n"));
      }

      for (const item of rawItems) {
        const lines = item.split("\n");
        const headLines = [];
        const metaLines = [];
        let inMeta = false;
        for (const l of lines) {
          if (/^(?:where|with)\s+/.test(l)) inMeta = true;
          if (inMeta) metaLines.push(l);
          else headLines.push(l);
        }
        const headJoined = headLines.join(" ").replace(/\s+/g, " ").trim();
        const metaJoined = metaLines.join(" ").replace(/\s+/g, " ").trim();
        if (!headJoined) continue;

        if (isRefinement) {
          const { cleanExpr, subgoals } = sanitizeRefinementFit(headJoined);
          if (!cleanExpr || skipFits.has(cleanExpr) || seen.has(`ref:${cleanExpr}`)) {
            continue;
          }
          seen.add(`ref:${cleanExpr}`);
          fits.push({
            expr: cleanExpr,
            typeSig: subgoals.length > 0 ? `Subgoal: ${subgoals.join(", ")}` : metaJoined,
            fullTooltip: [headJoined, metaJoined].filter(Boolean).join("\n"),
            refinement: true,
          });
        } else {
          const { expr, typeSig } = splitTopLevelTypeSig(headJoined);
          if (!expr || skipFits.has(expr) || seen.has(`fit:${expr}`)) continue;
          seen.add(`fit:${expr}`);
          fits.push({
            expr,
            typeSig: typeSig || metaJoined,
            fullTooltip: [headJoined, metaJoined].filter(Boolean).join("\n"),
            refinement: false,
          });
        }
      }
    };

    const directM = sec.match(
      /Valid hole fits include(?:[ \t]+([^\n]+)|\n([\s\S]*?))(?=\n\s*(?:Valid refinement hole fits include|Suggested fixes:|\(Some hole fits suppressed|\|)|$)/
    );
    if (directM) parseFitEntries(directM[1], directM[2], false);

    const refM = sec.match(
      /Valid refinement hole fits include(?:[ \t]+([^\n]+)|\n([\s\S]*?))(?=\n\s*(?:Suggested fixes:|\(Some refinement hole fits suppressed|\|)|$)/
    );
    if (refM) parseFitEntries(refM[1], refM[2], true);

    const splits = [];
    const fixM = sec.match(/Suggested fixes:\n([\s\S]*?)(?=\n\s*\||$)/);
    if (fixM) {
      const items = fixM[1].split(/^\s*•\s+/m).filter((s) => s.trim().length > 0);
      for (const rawItem of items) {
        const flat = rawItem.replace(/\s+/g, " ").trim();
        const pm = flat.match(
          /Pattern-match on [‘']([^’']+)[’']\s*\(constructors:\s*([^)]+)\)\s*to reduce [‘']([^’']+)[’']/
        );
        if (!pm) continue;
        const varName = pm[1].trim();
        const constructors = [...pm[2].matchAll(/[‘']([^’']+)[’']/g)].map((cm) =>
          cm[1].trim()
        );
        const stuckFn = pm[3].trim();
        if (varName && constructors.length > 0) {
          splits.push({ varName, constructors, stuckFn });
        }
      }
    }

    holes.push({ line, col, name, goalType, fnName, equationText, fits, splits });
  }
  return holes;
}

function findTopLevelEquals(line) {
  let depth = 0;
  for (let i = 0; i < line.length; i++) {
    const ch = line[i];
    if (ch === "(" || ch === "[" || ch === "{") depth++;
    else if (ch === ")" || ch === "]" || ch === "}") depth = Math.max(0, depth - 1);
    else if (
      depth === 0 &&
      ch === "=" &&
      line[i - 1] !== "=" &&
      line[i - 1] !== "/" &&
      line[i - 1] !== "<" &&
      line[i - 1] !== ">" &&
      line[i + 1] !== "=" &&
      line[i + 1] !== ">"
    ) {
      return i;
    }
  }
  return -1;
}

function extractLhsBinders(line, fnName) {
  const vars = new Set();
  if (!line) return vars;
  const eqPos = findTopLevelEquals(line);
  const lhs = eqPos === -1 ? line : line.slice(0, eqPos);
  const tokens = lhs.match(/\b[a-z][A-Za-z0-9_']*\b/g) || [];
  let skippedFn = false;
  for (const tok of tokens) {
    if (!skippedFn && fnName && tok === fnName) {
      skippedFn = true;
      continue;
    }
    vars.add(tok);
  }
  return vars;
}

// Map renamed GHC skolem suffixes (e.g. `n1` -> `n`) back to the source LHS binder
// when the base binder is in scope on the equation LHS and the suffixed token is not.
function normalizeSkolemVars(expr, lhsVars, code) {
  if (!lhsVars || lhsVars.size === 0) return expr;
  return expr.replace(/\b([a-z][A-Za-z0-9_']*?)(\d+)\b/g, (full, base) => {
    if (lhsVars.has(full) || !lhsVars.has(base)) return full;
    if (code && new RegExp(`\\b${escapeRegex(full)}\\b`).test(code)) return full;
    return base;
  });
}

function findHoleLineIndex(lines, hole, lineOffset) {
  const holeRe = new RegExp(
    `(^|[^A-Za-z0-9_'])${escapeRegex(hole.name)}(?![A-Za-z0-9_'])`
  );
  if (hole.line != null && lineOffset != null) {
    const idx = hole.line - 1 - lineOffset;
    if (idx >= 0 && idx < lines.length && holeRe.test(lines[idx])) {
      return idx;
    }
  }
  if (hole.equationText) {
    const normEq = hole.equationText.replace(/\s+/g, " ").trim();
    const exactIdx = lines.findIndex(
      (l) => l.replace(/\s+/g, " ").trim() === normEq
    );
    if (exactIdx !== -1) return exactIdx;

    const eqPos = findTopLevelEquals(normEq);
    if (eqPos !== -1) {
      const lhsPrefix = normEq.slice(0, eqPos).trim();
      const lhsIdx = lines.findIndex((l) => {
        const nl = l.replace(/\s+/g, " ").trim();
        return nl.startsWith(lhsPrefix) && holeRe.test(l);
      });
      if (lhsIdx !== -1) return lhsIdx;
    }
  }
  return lines.findIndex((l) => holeRe.test(l));
}

// Replace the hole occurrence on the diagnostic's target line in `code`.
function applyHoleFit(code, hole, rawFitExpr, lineOffset = null) {
  const lines = code.split("\n");
  const idx = findHoleLineIndex(lines, hole, lineOffset);
  if (idx === -1) return code;

  const targetLine = lines[idx];
  const lhsVars = extractLhsBinders(targetLine, hole.fnName);
  const fitExpr = normalizeSkolemVars(rawFitExpr, lhsVars, code);
  const eqPos = findTopLevelEquals(targetLine);
  const searchStart = eqPos !== -1 ? eqPos : 0;

  const re = new RegExp(
    `(^|[^A-Za-z0-9_'])(${escapeRegex(hole.name)})(?![A-Za-z0-9_'])`,
    "g"
  );
  re.lastIndex = searchStart;
  let chosen = null;
  let m;
  while ((m = re.exec(targetLine)) !== null) {
    const tokCol = m.index + m[1].length + 1; // 1-based column
    if (!chosen || (hole.col != null && Math.abs(tokCol - hole.col) < Math.abs(chosen.tokCol - hole.col))) {
      chosen = { index: m.index, prefix: m[1], tok: m[2], tokCol };
    }
  }
  if (!chosen && searchStart > 0) {
    re.lastIndex = 0;
    while ((m = re.exec(targetLine)) !== null) {
      const tokCol = m.index + m[1].length + 1;
      if (!chosen || (hole.col != null && Math.abs(tokCol - hole.col) < Math.abs(chosen.tokCol - hole.col))) {
        chosen = { index: m.index, prefix: m[1], tok: m[2], tokCol };
      }
    }
  }
  if (!chosen) return code;

  const tokStart = chosen.index + chosen.prefix.length;
  const tokEnd = tokStart + chosen.tok.length;
  const before = targetLine.slice(0, tokStart);
  const needsParens = /\s/.test(fitExpr) && !/^\(.*\)$/.test(fitExpr);
  const insideApp = /[A-Za-z0-9_')\]]\s+$/.test(before);
  const replacement = needsParens && insideApp ? `(${fitExpr})` : fitExpr;
  lines[idx] = before + replacement + targetLine.slice(tokEnd);
  return lines.join("\n");
}

function inferLocalCtorArities(code) {
  const arities = new Map();
  for (const rawLine of code.split("\n")) {
    const line = rawLine.replace(/--.*$/, "").trim();
    if (!line) continue;
    // GADT constructor: `C :: a -> b -> T ...`
    const gadtM = line.match(/^([A-Z][A-Za-z0-9_']*)\s*::\s*(.*)$/);
    if (gadtM) {
      const ctor = gadtM[1];
      let sig = gadtM[2].replace(/^forall\b[^.]*\.\s*/, "");
      // Count top-level `->` arrows outside parens.
      let depth = 0;
      let arrows = 0;
      for (let i = 0; i < sig.length - 1; i++) {
        const ch = sig[i];
        if (ch === "(" || ch === "[" || ch === "{") depth++;
        else if (ch === ")" || ch === "]" || ch === "}") depth = Math.max(0, depth - 1);
        else if (depth === 0 && sig[i] === "-" && sig[i + 1] === ">") {
          arrows++;
          i++;
        }
      }
      arities.set(ctor, arrows);
      continue;
    }
    // H98 ADT line: `data Foo a = Bar | Baz a (Foo a)` or `| Baz a (Foo a)`
    const adtM = line.match(/^(?:data|newtype)\s+[^=]+=\s*(.*)$/) || line.match(/^\|\s*(.*)$/);
    if (adtM) {
      for (const alt of adtM[1].split("|")) {
        const cleaned = alt.replace(/\bderiving\b.*$/, "").trim();
        const cm = cleaned.match(/^([A-Z][A-Za-z0-9_']*)(?:\s+(.*))?$/);
        if (!cm) continue;
        const ctor = cm[1];
        const rest = (cm[2] || "").trim();
        if (!rest) {
          arities.set(ctor, 0);
        } else {
          // Count top-level whitespace-separated type arguments.
          let depth = 0;
          let args = 0;
          let inTok = false;
          for (const ch of rest) {
            if (ch === "(" || ch === "[" || ch === "{") {
              if (depth === 0 && !inTok) {
                args++;
                inTok = true;
              }
              depth++;
            } else if (ch === ")" || ch === "]" || ch === "}") {
              depth = Math.max(0, depth - 1);
            } else if (/\s/.test(ch) && depth === 0) {
              inTok = false;
            } else if (depth === 0 && !inTok) {
              args++;
              inTok = true;
            }
          }
          arities.set(ctor, args);
        }
      }
    }
  }
  return arities;
}

function pickFreshVar(base, used) {
  if (!used.has(base)) {
    used.add(base);
    return base;
  }
  for (let i = 1; i < 20; i++) {
    const cand = `${base}${i}`;
    if (!used.has(cand)) {
      used.add(cand);
      return cand;
    }
  }
  return `${base}_`;
}

function buildCtorPattern(ctor, varName, otherVars, localArities) {
  const used = new Set(otherVars);
  used.delete(varName);
  const recursiveArg = varName;

  if (ctor === "[]") return "[]";
  if (ctor === ":" || ctor === "(:)") {
    const headBase = varName.endsWith("s") && varName.length > 1 ? varName.slice(0, -1) : "x";
    const head = pickFreshVar(headBase, new Set([...used, recursiveArg]));
    return `(${head} : ${recursiveArg})`;
  }
  if (ctor === "()") return "()";

  const nullary = new Set([
    "Zero", "True", "False", "Nothing", "Refl", "ReflP", "Nil", "One",
    "FZ", "Z", "LZ", "LTZ", "EQ", "LT", "GT", "CEmpty", "TNat",
  ]);
  if (nullary.has(ctor)) return ctor;

  const unaryRecursive = new Set(["Succ", "Suc", "X0", "X1", "Inc", "FS", "S", "LS", "LTS"]);
  if (unaryRecursive.has(ctor)) return `(${ctor} ${recursiveArg})`;

  if (ctor === "Just") return `(Just ${pickFreshVar("x", used)})`;
  if (ctor === "Left") return `(Left ${pickFreshVar("x", used)})`;
  if (ctor === "Right") return `(Right ${pickFreshVar("y", used)})`;
  if (ctor === "Yes") return `(Yes ${pickFreshVar("p", used)})`;
  if (ctor === "No") return `(No ${pickFreshVar("np", used)})`;
  if (ctor === "Pair") {
    const a = pickFreshVar("x", used);
    const b = pickFreshVar("y", used);
    return `(Pair ${a} ${b})`;
  }

  const arity = localArities.get(ctor) ?? 0;
  if (arity <= 0) return ctor;
  const args = [];
  for (let i = 0; i < arity; i++) {
    args.push(pickFreshVar(i === 0 ? "x" : `x${i + 1}`, used));
  }
  return `(${ctor} ${args.join(" ")})`;
}

// Agda-mode case split: split the hole's equation line across constructors of `split.varName`.
function applyCaseSplit(code, hole, split, lineOffset = null) {
  const lines = code.split("\n");
  const idx = findHoleLineIndex(lines, hole, lineOffset);
  if (idx === -1) return code;

  const line = lines[idx];
  const eqPos = findTopLevelEquals(line);
  if (eqPos === -1) return code;

  const lhs = line.slice(0, eqPos);
  const rhs = line.slice(eqPos + 1);
  const localArities = inferLocalCtorArities(code);
  const otherVars = extractLhsBinders(line, hole.fnName);

  // Locate `split.varName` in LHS after the function name.
  const fnPrefixLen = hole.fnName ? Math.max(0, lhs.indexOf(hole.fnName) + hole.fnName.length) : 0;
  const lhsHead = lhs.slice(0, fnPrefixLen);
  const lhsArgs = lhs.slice(fnPrefixLen);
  const varRe = new RegExp(`(^|[^A-Za-z0-9_'])(${escapeRegex(split.varName)})(?![A-Za-z0-9_'])`);
  const vm = lhsArgs.match(varRe);
  if (!vm) return code;

  const varStart = vm.index + vm[1].length;
  const varEnd = varStart + vm[2].length;
  const beforeVar = lhsHead + lhsArgs.slice(0, varStart);
  const afterVar = lhsArgs.slice(varEnd);

  const pats = split.constructors.map((ctor) =>
    buildCtorPattern(ctor, split.varName, otherVars, localArities)
  );
  const maxPatLen = Math.max(...pats.map((p) => p.length));

  const newLines = split.constructors.map((ctor, i) => {
    const pat = pats[i];
    const pad = " ".repeat(Math.max(0, maxPatLen - pat.length));
    let branchRhs = rhs;
    if (hole.name !== "_") {
      const safeSuffix = ctor.replace(/[^A-Za-z0-9_]/g, "") || String(i + 1);
      const holeRe = new RegExp(
        `(^|[^A-Za-z0-9_'])${escapeRegex(hole.name)}(?![A-Za-z0-9_'])`
      );
      branchRhs = rhs.replace(holeRe, `$1${hole.name}_${safeSuffix}`);
    }
    return `${beforeVar}${pat}${pad}${afterVar}=${branchRhs}`;
  });

  lines.splice(idx, 1, ...newLines);
  return lines.join("\n");
}

// Enable general refinement hole fits (-frefinement-level-hole-fits=2 and
// -fabstract-refinement-hole-fits) and the standalone Dependent.Plugin.ProofSearch
// HoleFitPlugin for congruence/transitivity subgoal refinements & bounded synthesis.
function refinementExtraGhcArgs(uiState) {
  const parts = [];
  if (uiState.refinementFits) {
    parts.push("-frefinement-level-hole-fits=2", "-fabstract-refinement-hole-fits");
  } else {
    parts.push("-fmax-refinement-hole-fits=0");
  }
  if (uiState.proofSearch) {
    parts.push("-fplugin=Dependent.Plugin.ProofSearch");
  }
  return parts.join(" ");
}

// Render interactive Agda-mode hole goals, case-split buttons, and clickable fit chips.
function renderHolePanel(panelEl, diagText, { code = "", lineOffset = null, onFill, onSplit }) {
  const holes = parseTypedHoles(diagText);
  panelEl.innerHTML = "";
  if (holes.length === 0) {
    panelEl.hidden = true;
    return;
  }
  panelEl.hidden = false;

  const heading = document.createElement("div");
  heading.className = "plfh-hole-heading";
  heading.textContent =
    "Typed Holes (Agda-mode — click a case split or fit to refine & re-check):";
  panelEl.append(heading);

  const codeLines = code ? code.split("\n") : [];

  for (const hole of holes) {
    const card = document.createElement("div");
    card.className = "plfh-hole-card";

    const lineIdx = codeLines.length > 0 ? findHoleLineIndex(codeLines, hole, lineOffset) : -1;
    const lhsVars = extractLhsBinders(
      lineIdx !== -1 ? codeLines[lineIdx] : hole.equationText,
      hole.fnName
    );

    if (hole.equationText) {
      const eqBadge = document.createElement("div");
      eqBadge.className = "plfh-hole-eq";
      eqBadge.innerHTML = `<code>${escapeHtml(hole.equationText)}</code>`;
      card.append(eqBadge);
    }

    const goal = document.createElement("div");
    goal.className = "plfh-hole-goal";
    goal.innerHTML = `<code>${escapeHtml(hole.name)} :: ${escapeHtml(hole.goalType)}</code>`;
    card.append(goal);

    if (hole.splits.length > 0 && onSplit) {
      const splitRow = document.createElement("div");
      splitRow.className = "plfh-hole-fits";
      const lbl = document.createElement("span");
      lbl.className = "plfh-hole-row-label";
      lbl.textContent = "Case split:";
      splitRow.append(lbl);
      for (const sp of hole.splits) {
        const btn = document.createElement("button");
        btn.type = "button";
        btn.className = "plfh-hole-fit-btn plfh-hole-fit-btn--split";
        btn.textContent = `Split on ${sp.varName} (${sp.constructors.join(" | ")})`;
        btn.title = `Pattern-match on '${sp.varName}' to reduce '${sp.stuckFn}'`;
        btn.addEventListener("click", () => onSplit(hole, sp));
        splitRow.append(btn);
      }
      card.append(splitRow);
    }

    const directFits = hole.fits.filter((f) => !f.refinement);
    const refFits = hole.fits.filter((f) => f.refinement);

    if (directFits.length > 0) {
      const fitsRow = document.createElement("div");
      fitsRow.className = "plfh-hole-fits";
      const lbl = document.createElement("span");
      lbl.className = "plfh-hole-row-label";
      lbl.textContent = "Fill:";
      fitsRow.append(lbl);
      for (const fit of directFits.slice(0, 8)) {
        const displayExpr = normalizeSkolemVars(fit.expr, lhsVars, code);
        const btn = document.createElement("button");
        btn.type = "button";
        btn.className = "plfh-hole-fit-btn";
        btn.textContent = displayExpr;
        btn.title = fit.fullTooltip || `${displayExpr} :: ${fit.typeSig}`;
        btn.addEventListener("click", () => onFill(hole, fit.expr));
        fitsRow.append(btn);
      }
      card.append(fitsRow);
    }

    if (refFits.length > 0) {
      const refRow = document.createElement("div");
      refRow.className = "plfh-hole-fits";
      const lbl = document.createElement("span");
      lbl.className = "plfh-hole-row-label";
      lbl.textContent = "Refine subgoal:";
      refRow.append(lbl);
      for (const fit of refFits.slice(0, 8)) {
        const displayExpr = normalizeSkolemVars(fit.expr, lhsVars, code);
        const btn = document.createElement("button");
        btn.type = "button";
        btn.className = "plfh-hole-fit-btn plfh-hole-fit-btn--refine";
        btn.textContent = displayExpr;
        btn.title = fit.fullTooltip || `${displayExpr} (${fit.typeSig})`;
        btn.addEventListener("click", () => onFill(hole, fit.expr));
        refRow.append(btn);
      }
      card.append(refRow);
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

// Parse GHC diagnostic locations (`path:line:col:`, `path:line:col-end:`, or
// `path:(l1,c1)-(l2,c2):`) into 0-based line indices & 0-based half-open column spans.
function parseErrorSpans(diagText, lineOffset = null) {
  if (!diagText) return [];
  const off = lineOffset ?? 0;
  const spans = [];
  const seen = new Set();

  const rangeRe = /^[^\n]*?:(\d+):(\d+)(?:-(\d+))?:\s*(error|warning):/gm;
  let m;
  while ((m = rangeRe.exec(diagText)) !== null) {
    if (m[4] !== "error") continue;
    const lineIdx = Number(m[1]) - 1 - off;
    const startCol = Math.max(0, Number(m[2]) - 1);
    const endCol = m[3] ? Math.max(startCol + 1, Number(m[3])) : null;
    if (lineIdx < 0) continue;
    const key = `${lineIdx}:${startCol}:${endCol ?? ""}`;
    if (!seen.has(key)) {
      seen.add(key);
      spans.push({ lineIdx, startCol, endCol });
    }
  }

  const multiRe = /^[^\n]*?:\((\d+),(\d+)\)-\((\d+),(\d+)\):\s*error:/gm;
  while ((m = multiRe.exec(diagText)) !== null) {
    const l1 = Number(m[1]) - 1 - off;
    const c1 = Math.max(0, Number(m[2]) - 1);
    const l2 = Number(m[3]) - 1 - off;
    const c2 = Math.max(1, Number(m[4]));
    if (l1 < 0) continue;
    for (let li = l1; li <= Math.min(l2, l1 + 6); li++) {
      const sc = li === l1 ? c1 : 0;
      const ec = li === l2 ? c2 : null;
      const key = `${li}:${sc}:${ec ?? ""}`;
      if (!seen.has(key)) {
        seen.add(key);
        spans.push({ lineIdx: li, startCol: sc, endCol: ec });
      }
    }
  }
  return spans;
}

const AGDA_KEYWORDS = new Set([
  "foreach",
  "forall",
  "some",
  "exists",
  "module",
  "where",
  "import",
  "qualified",
  "as",
  "hiding",
  "data",
  "newtype",
  "type",
  "class",
  "instance",
  "let",
  "in",
  "case",
  "of",
  "if",
  "then",
  "else",
  "do",
  "deriving",
  "infix",
  "infixl",
  "infixr",
  "pattern",
  "family",
]);

const AGDA_KNOWN_DATACONS = new Set([
  "Refl",
  "HRefl",
  "Zero",
  "Succ",
  "VNil",
  "VCons",
  "FZ",
  "FS",
  "Pair",
  "Pack",
  "Just",
  "Nothing",
  "Left",
  "Right",
  "True",
  "False",
  "MkIso",
  "MkEmbed",
  "Iff",
  "MkCPair",
  "Witness",
  "ZleN",
  "SleS",
  "EvenZ",
  "EvenS",
  "OddS",
  "Yes",
  "No",
  "Here",
  "There",
  "Nil",
  "Cons",
  "Lam",
  "App",
  "Var",
  "Suc",
  "Done",
  "OutOfGas",
  "MkGas",
  "CEmpty",
  "CExt",
  "TNat",
  "TArr",
  "Z",
  "S",
]);

const AGDA_KNOWN_TYCONS = new Set([
  "Type",
  "Constraint",
  "Matchability",
  "Nat",
  "Vec",
  "Fin",
  "List",
  "Maybe",
  "Either",
  "Bool",
  "Int",
  "Integer",
  "Char",
  "String",
  "Double",
  "Float",
  "IO",
  "Void",
  "Proxy",
  "Sigma",
  "SomeVec",
  "Exists",
  "Iso",
  "Embed",
  "Dec",
  "Not",
  "Even",
  "Odd",
  "All",
  "Any",
  "In",
  "Term",
  "Context",
  "EvenSigma",
  "SizedRow",
  "SizedVec",
]);

const VALID_SEMANTIC_KINDS = new Set([
  "datacon",
  "tycon",
  "tyvar",
  "fn",
  "local",
]);

function normalizeGhcLineTokens(line, rawTokens) {
  if (!rawTokens || rawTokens.length === 0) return [];
  const n = line.length;
  const out = [];
  for (const raw of rawTokens) {
    let s = Math.max(0, Math.min(raw.startCol, n));
    let e = Math.max(s, Math.min(raw.endCol, n));
    if (e <= s || !VALID_SEMANTIC_KINDS.has(raw.kind)) continue;
    // Strip surrounding parens/backticks when GHC spans `(op)` or `` `fn` ``.
    if (
      e - s >= 3 &&
      ((line[s] === "(" && line[e - 1] === ")") ||
        (line[s] === "`" && line[e - 1] === "`"))
    ) {
      s += 1;
      e -= 1;
    }
    if (e > s) {
      out.push({ startCol: s, endCol: e, kind: raw.kind });
    }
  }
  out.sort((a, b) => a.startCol - b.startCol || b.endCol - a.endCol);
  // Deduplicate overlapping starts, keeping the most specific span.
  const dedup = [];
  let lastEnd = -1;
  for (const tok of out) {
    if (tok.startCol >= lastEnd) {
      dedup.push(tok);
      lastEnd = tok.endCol;
    }
  }
  return dedup;
}

function highlightHaskellLine(
  line,
  lineIdx,
  { inBlockComment, isTypeLine, holeSpans, ghcLineTokens }
) {
  // Hole spans on this line take precedence for Agda-green goal boxes.
  const holesHere = (holeSpans || []).filter((h) => h.lineIdx === lineIdx);
  const findHoleAt = (col) =>
    holesHere.find((h) => col >= h.startCol && col < h.endCol);
  const ghcToks = normalizeGhcLineTokens(line, ghcLineTokens);
  const ghcTokByStart = new Map(ghcToks.map((t) => [t.startCol, t]));

  let out = "";
  let i = 0;
  let blockDepth = inBlockComment;
  let inTypeCtx = isTypeLine;
  const n = line.length;

  while (i < n) {
    const hole = findHoleAt(i);
    if (hole && i === hole.startCol) {
      out += `<span class="plfh-agda-hole">${escapeHtml(line.slice(hole.startCol, hole.endCol))}</span>`;
      i = hole.endCol;
      continue;
    }

    if (blockDepth > 0) {
      const openIdx = line.indexOf("{-", i);
      const closeIdx = line.indexOf("-}", i);
      if (closeIdx === -1) {
        out += `<span class="plfh-tok-comment">${escapeHtml(line.slice(i))}</span>`;
        return { html: out, inBlockComment: blockDepth };
      }
      if (openIdx !== -1 && openIdx < closeIdx) {
        out += `<span class="plfh-tok-comment">${escapeHtml(line.slice(i, openIdx + 2))}</span>`;
        blockDepth++;
        i = openIdx + 2;
      } else {
        out += `<span class="plfh-tok-comment">${escapeHtml(line.slice(i, closeIdx + 2))}</span>`;
        blockDepth--;
        i = closeIdx + 2;
      }
      continue;
    }

    // Pragmas {-# ... #-}
    if (line.startsWith("{-#", i)) {
      const end = line.indexOf("#-}", i + 3);
      const stop = end === -1 ? n : end + 3;
      out += `<span class="plfh-tok-pragma">${escapeHtml(line.slice(i, stop))}</span>`;
      i = stop;
      continue;
    }

    // Block comments {- ... -}
    if (line.startsWith("{-", i)) {
      blockDepth = 1;
      out += `<span class="plfh-tok-comment">${escapeHtml("{-")}</span>`;
      i += 2;
      continue;
    }

    // Line comments -- ...
    if (
      line.startsWith("--", i) &&
      (i + 2 === n || !/[!#$%&*+./<=>?@\\^|~:-]/.test(line[i + 2]))
    ) {
      out += `<span class="plfh-tok-comment">${escapeHtml(line.slice(i))}</span>`;
      break;
    }

    // String literals
    if (line[i] === '"') {
      let j = i + 1;
      while (j < n) {
        if (line[j] === "\\") j += 2;
        else if (line[j] === '"') {
          j++;
          break;
        } else j++;
      }
      out += `<span class="plfh-tok-str">${escapeHtml(line.slice(i, j))}</span>`;
      i = j;
      continue;
    }

    // Char literals ('a', '\n')
    if (line[i] === "'" && i + 2 < n) {
      const charM = line.slice(i).match(/^'(?:\\.|[^'\\])'/);
      if (charM) {
        out += `<span class="plfh-tok-str">${escapeHtml(charM[0])}</span>`;
        i += charM[0].length;
        continue;
      }
    }

    // Compiler-exact GHC RenamedSource semantic token span (takes precedence over heuristics).
    const ghcTok = ghcTokByStart.get(i);
    if (ghcTok && ghcTok.endCol <= n) {
      const text = line.slice(i, ghcTok.endCol);
      if (!AGDA_KEYWORDS.has(text)) {
        out += `<span class="plfh-tok-${ghcTok.kind}">${escapeHtml(text)}</span>`;
        i = ghcTok.endCol;
        continue;
      }
    }

    // Numbers
    if (/\d/.test(line[i]) && (i === 0 || !/[A-Za-z0-9_']/.test(line[i - 1]))) {
      const numM = line.slice(i).match(/^\d+(?:\.\d+)?/);
      if (numM) {
        out += `<span class="plfh-tok-lit">${escapeHtml(numM[0])}</span>`;
        i += numM[0].length;
        continue;
      }
    }

    // Identifiers / keywords / constructors
    if (/[A-Za-z_]/.test(line[i])) {
      let j = i + 1;
      while (j < n && /[A-Za-z0-9_']/.test(line[j])) j++;
      const word = line.slice(i, j);
      if (AGDA_KEYWORDS.has(word)) {
        out += `<span class="plfh-tok-kw">${escapeHtml(word)}</span>`;
        if (word === "type" || word === "data" || word === "newtype" || word === "class" || word === "instance") {
          inTypeCtx = true;
        }
      } else if (/^[A-Z]/.test(word)) {
        const isCon =
          AGDA_KNOWN_TYCONS.has(word)
            ? "plfh-tok-tycon"
            : AGDA_KNOWN_DATACONS.has(word)
              ? "plfh-tok-datacon"
              : inTypeCtx
                ? "plfh-tok-tycon"
                : "plfh-tok-datacon";
        out += `<span class="${isCon}">${escapeHtml(word)}</span>`;
      } else if (i === 0) {
        out += `<span class="plfh-tok-fn">${escapeHtml(word)}</span>`;
      } else {
        out += escapeHtml(word);
      }
      i = j;
      continue;
    }

    // Multi-char operators / symbols
    const opM = line.slice(i).match(/^(?::~~:|:~:|::|->|=>|<-|\+\+|==|\/=|<=|>=|&&|\|\||[:!#$%&*+./<=>?@\\^|~-]+)/);
    if (opM) {
      const op = opM[0];
      if (op === "::") inTypeCtx = true;
      else if (op === "=" && !line.slice(0, i).includes("type ")) inTypeCtx = false;
      out += `<span class="plfh-tok-op">${escapeHtml(op)}</span>`;
      i += op.length;
      continue;
    }

    out += escapeHtml(line[i]);
    i++;
  }

  return { html: out, inBlockComment: blockDepth };
}

function renderErrorLine(line, spansHere) {
  if (!spansHere || spansHere.length === 0) {
    return escapeHtml(line);
  }
  const sorted = [...spansHere].sort((a, b) => a.startCol - b.startCol);
  let out = "";
  let pos = 0;
  for (const sp of sorted) {
    const start = Math.max(pos, Math.min(sp.startCol, line.length));
    let end = sp.endCol !== null ? Math.min(sp.endCol, line.length) : start;
    if (end <= start) {
      const tok = line.slice(start).match(/^[A-Za-z0-9_']+|^\S+/);
      end = tok ? start + tok[0].length : Math.min(line.length, start + 1);
    }
    if (start > pos) out += escapeHtml(line.slice(pos, start));
    if (end > start) {
      out += `<span class="plfh-agda-err">${escapeHtml(line.slice(start, end))}</span>`;
    }
    pos = Math.max(pos, end);
  }
  if (pos < line.length) out += escapeHtml(line.slice(pos));
  return `<span class="plfh-agda-err-line">${out}</span>`;
}

// Render Agda-mode code backdrop: monochrome when unverified, full semantic colors
// when compiled by GHC, green goal boxes on typed holes, and red spans on errors.
function highlightDependentHaskell(
  code,
  {
    state = "unverified",
    holes = [],
    errors = [],
    lineOffset = null,
    semanticTokens = null,
  } = {}
) {
  if (state === "unverified" || state === "checking") {
    return escapeHtml(code) + "\n";
  }

  const lines = code.split("\n");
  if (state === "err") {
    const byLine = new Map();
    for (const sp of errors || []) {
      if (!byLine.has(sp.lineIdx)) byLine.set(sp.lineIdx, []);
      byLine.get(sp.lineIdx).push(sp);
    }
    return (
      lines
        .map((line, idx) => renderErrorLine(line, byLine.get(idx)))
        .join("\n") + "\n"
    );
  }

  // Group GHC RenamedSource semantic tokens by 0-based line index when available.
  const ghcByLine = new Map();
  if (Array.isArray(semanticTokens)) {
    for (const [li, sc, ec, kind] of semanticTokens) {
      if (!ghcByLine.has(li)) ghcByLine.set(li, []);
      ghcByLine.get(li).push({ startCol: sc, endCol: ec, kind });
    }
  }

  // Verified ("ok") or verified-with-holes ("holes"): compute exact hole spans.
  const holeSpans = [];
  for (const h of holes || []) {
    const lineIdx = findHoleLineIndex(lines, h, lineOffset);
    if (lineIdx === -1) continue;
    const lineText = lines[lineIdx];
    const targetCol = h.col ? Math.max(0, h.col - 1) : 0;
    const re = new RegExp(`(?<![A-Za-z0-9_'])${escapeRegex(h.name)}(?![A-Za-z0-9_'])`, "g");
    let best = null;
    let bestDist = Infinity;
    let mm;
    while ((mm = re.exec(lineText)) !== null) {
      const dist = Math.abs(mm.index - targetCol);
      if (dist < bestDist) {
        bestDist = dist;
        best = mm.index;
      }
    }
    if (best !== null) {
      holeSpans.push({
        lineIdx,
        startCol: best,
        endCol: best + h.name.length,
      });
    }
  }

  let inBlockComment = 0;
  let prevWasSigCont = false;
  const rendered = lines.map((line, idx) => {
    const trimmed = line.trim();
    const startsSig =
      /^[a-z_][A-Za-z0-9_']*\s*::/.test(line) ||
      /^\s*(?:type|data|newtype|class|instance)\b/.test(line) ||
      (prevWasSigCont && /^\s*(?:->|=>|::|\|)/.test(line));
    const res = highlightHaskellLine(line, idx, {
      inBlockComment,
      isTypeLine: startsSig,
      holeSpans,
      ghcLineTokens: ghcByLine.get(idx) || null,
    });
    inBlockComment = res.inBlockComment;
    prevWasSigCont =
      startsSig && trimmed.length > 0 && !trimmed.includes(" = ");
    return res.html;
  });

  return rendered.join("\n") + "\n";
}

const AGDA_BADGE_LABELS = {
  unverified: "Unverified · Ctrl+Enter",
  checking: "Checking…",
  ok: "Verified ✓",
  holes: "Holes (Agda-mode)",
  err: "Type Error",
};

function createAgdaEditor({
  initialValue = "",
  rows = 8,
  placeholder = "",
  extraClass = "",
} = {}) {
  const root = document.createElement("div");
  root.className = "plfh-agda-editor";
  root.dataset.state = "unverified";

  const badge = document.createElement("span");
  badge.className = "plfh-agda-badge";
  badge.textContent = AGDA_BADGE_LABELS.unverified;

  const backdrop = document.createElement("pre");
  backdrop.className = "plfh-agda-backdrop";
  backdrop.setAttribute("aria-hidden", "true");
  const codeEl = document.createElement("code");
  backdrop.append(codeEl);

  const textarea = document.createElement("textarea");
  textarea.className = `plfh-wasm-editor plfh-agda-input${extraClass ? " " + extraClass : ""}`;
  textarea.spellcheck = false;
  textarea.rows = rows;
  if (placeholder) textarea.placeholder = placeholder;
  textarea.value = initialValue;

  root.append(backdrop, textarea, badge);

  let state = "unverified";
  let lastMeta = {};

  const render = () => {
    root.dataset.state = state;
    const hasGhcTokens =
      Array.isArray(lastMeta.semanticTokens) && lastMeta.semanticTokens.length > 0;
    root.dataset.semanticSource =
      state === "ok" || state === "holes"
        ? hasGhcTokens
          ? "ghc"
          : "lexer"
        : "";
    badge.textContent = AGDA_BADGE_LABELS[state] || "";
    badge.title = hasGhcTokens
      ? "Semantic highlighting from GHC RenamedSource"
      : "";
    codeEl.innerHTML = highlightDependentHaskell(textarea.value, {
      state,
      ...lastMeta,
    });
    backdrop.scrollTop = textarea.scrollTop;
    backdrop.scrollLeft = textarea.scrollLeft;
  };

  textarea.addEventListener("input", () => {
    state = "unverified";
    lastMeta = {};
    render();
  });

  textarea.addEventListener("scroll", () => {
    backdrop.scrollTop = textarea.scrollTop;
    backdrop.scrollLeft = textarea.scrollLeft;
  });

  render();

  return {
    root,
    textarea,
    get value() {
      return textarea.value;
    },
    set value(v) {
      textarea.value = v;
      state = "unverified";
      lastMeta = {};
      render();
    },
    setUnverified() {
      state = "unverified";
      lastMeta = {};
      render();
    },
    setChecking() {
      state = "checking";
      lastMeta = {};
      render();
    },
    setVerified({ holes = [], lineOffset = null, semanticTokens = null } = {}) {
      state = holes && holes.length > 0 ? "holes" : "ok";
      lastMeta = { holes, lineOffset, semanticTokens };
      render();
    },
    setErrors({ errors = [], lineOffset = null } = {}) {
      state = "err";
      lastMeta = { errors, lineOffset };
      render();
    },
    focus() {
      textarea.focus();
    },
  };
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
    "Enable Dependent Haskell refinement hole fits & subgoal splitting (on by default under -XDependentTypes)";
  const refineCheckbox = document.createElement("input");
  refineCheckbox.type = "checkbox";
  refineCheckbox.checked = uiState.refinementFits;
  refineCheckbox.addEventListener("change", () => {
    uiState.refinementFits = refineCheckbox.checked;
  });
  refineLabel.append(refineCheckbox, document.createTextNode(" Refinement fits"));

  const proofLabel = document.createElement("label");
  proofLabel.className = "plfh-refinement-toggle";
  proofLabel.title =
    "Enable Dependent.Plugin.ProofSearch (-fplugin=Dependent.Plugin.ProofSearch) for congruence/transitivity refinements & bounded proof search";
  const proofCheckbox = document.createElement("input");
  proofCheckbox.type = "checkbox";
  proofCheckbox.checked = uiState.proofSearch;
  proofCheckbox.addEventListener("change", () => {
    uiState.proofSearch = proofCheckbox.checked;
  });
  proofLabel.append(proofCheckbox, document.createTextNode(" ProofSearch plugin"));

  const statusSpan = document.createElement("span");
  statusSpan.className = "plfh-wasm-status";
  statusSpan.textContent = "Loads on demand";

  actions.append(openBtn, checkAllBtn, refineLabel, proofLabel);
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
  const scratchEditor = createAgdaEditor({
    rows: 6,
    placeholder: `-- Declarations here automatically import ${chapterModule}\n-- Tip: write a typed hole like _qed to inspect goals & valid hole fits (Ctrl/Cmd+Enter)`,
  });
  const scratchBtn = document.createElement("button");
  scratchBtn.type = "button";
  scratchBtn.className = "plfh-wasm-btn plfh-wasm-check";
  scratchBtn.textContent = "Check Scratchpad";
  scratchWrap.append(scratchSummary, scratchEditor.root, scratchBtn);

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
    scratchEditor.setChecking();
    statusSpan.textContent = client.booted ? "Checking scratchpad..." : "Starting GHCi Wasm...";
    const res = await client.checkBlock({
      code: scratchEditor.value,
      chapterModule,
      chapterPragmas: ctx.chapterPragmas,
      chapterImports: ctx.chapterImports,
      chapterExports: ctx.chapterExports,
      extraGhcArgs: refinementExtraGhcArgs(uiState),
    });
    scratchBtn.disabled = false;
    output.hidden = false;
    const combined = [res.stdout, res.stderr].filter(Boolean).join("\n");
    const hasHoles = !res.ok && combined.includes("Found hole:");
    const lineOffset = res.lineOffset ?? null;
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
    if (res.ok) {
      scratchEditor.setVerified({
        holes: [],
        lineOffset,
        semanticTokens: res.semanticTokens ?? null,
      });
    } else if (hasHoles) {
      const parsedHoles = parseTypedHoles(combined);
      scratchEditor.setVerified({ holes: parsedHoles, lineOffset });
      renderHolePanel(holePanel, combined, {
        code: scratchEditor.value,
        lineOffset,
        onFill: (hole, fitExpr) => {
          scratchWrap.open = true;
          scratchEditor.value = applyHoleFit(scratchEditor.value, hole, fitExpr, lineOffset);
          scratchEditor.focus();
          runScratch();
        },
        onSplit: (hole, split) => {
          scratchWrap.open = true;
          scratchEditor.value = applyCaseSplit(scratchEditor.value, hole, split, lineOffset);
          scratchEditor.focus();
          runScratch();
        },
      });
    } else {
      scratchEditor.setErrors({
        errors: parseErrorSpans(combined, lineOffset),
        lineOffset,
      });
    }
  };

  scratchBtn.addEventListener("click", runScratch);
  wireEditorKeys(scratchEditor.textarea, runScratch);

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

import Data.Nat.Dependent (Nat (..), natToInt, plus, type (+))
import Data.Type.Equality.Dependent ((:~:) (Refl), cong, trans)

twoPlusThree :: (2 + 3 :: Nat) :~: 5
twoPlusThree = Refl

plusIdentityR :: foreach (m :: Nat) -> plus m Zero :~: m
plusIdentityR Zero     = Refl
plusIdentityR (Succ m) = cong Succ (plusIdentityR m)

plusSuc :: foreach (m n :: Nat) -> plus m (Succ n) :~: Succ (plus m n)
plusSuc Zero     _ = Refl
plusSuc (Succ m) n = cong Succ (plusSuc m n)

plusComm :: foreach (m n :: Nat) -> plus m n :~: plus n m
plusComm m Zero     = plusIdentityR m
plusComm m (Succ k) = plusSuc m k \`trans\` cong Succ (plusComm m k)
`,
  },
  {
    id: "routes",
    label: "Routes & Monad Stack",
    replHint: "demo",
    code: `{-# LANGUAGE DependentTypes, ListTuplePuns, TypeFamilies, UndecidableInstances #-}
module Playground where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, modify', runStateT)
import Control.Monad.Trans.Writer.Strict (WriterT, runWriterT, tell)
import Data.Functor.Identity (Identity (runIdentity))
import Data.Kind (Type)
import GHC.Matchability (U)
import Text.Read (readMaybe)

data RunMode = PureMode | LoggedMode | MeteredMode

-- Select the monad transformer stack and unwrapped result type with type-level case:
type StackM (m :: RunMode) = case m of
  PureMode    -> Identity
  LoggedMode  -> WriterT [String] Identity
  MeteredMode -> StateT Int (WriterT [String] Identity)

type StackOut (m :: RunMode) a = case m of
  PureMode    -> a
  LoggedMode  -> (a, [String])
  MeteredMode -> ((a, Int), [String])

withStackMonad :: foreach (m :: RunMode) -> (Monad (StackM m) => a) -> a
withStackMonad PureMode    k = k
withStackMonad LoggedMode  k = k
withStackMonad MeteredMode k = k

runMode :: foreach (m :: RunMode) -> StackM m a -> StackOut m a
runMode PureMode    act = runIdentity act
runMode LoggedMode  act = runIdentity (runWriterT act)
runMode MeteredMode act = runIdentity (runWriterT (runStateT act 0))

recordHit :: foreach (m :: RunMode) -> String -> StackM m ()
recordHit PureMode    _   = pure ()
recordHit LoggedMode  msg = tell [msg]
recordHit MeteredMode msg = modify' (+ 1) >> lift (tell [msg])

data WireTy = TInt | TString | TBool

interp :: WireTy -> Type
interp TInt    = type Int
interp TString = type String
interp TBool   = type Bool

data Seg  = Users | Posts | Health
data Part = Lit Seg | Cap WireTy

infixr 5 :>
data Route = Part :> Route | Get WireTy

data Endpoint = UserPost | HealthCheck

apiRoute :: Endpoint -> Route
apiRoute UserPost    = Lit Users :> Cap TInt :> Lit Posts :> Cap TString :> Get TBool
apiRoute HealthCheck = Lit Health :> Get TString

type family RouteType (ret :: WireTy %U -> Type) (r :: Route) :: Type where
  RouteType ret (Lit _  :> rest) = RouteType ret rest
  RouteType ret (Cap ty :> rest) = interp ty -> RouteType ret rest
  RouteType ret (Get res)        = ret res

type HandlerRet (m :: RunMode) = \\res -> StackM m (Either String (interp res))
type LinkRet                   = \\res -> String

type HandlerType m r = RouteType (HandlerRet m) r
type LinkType      r = RouteType LinkRet r

segPath :: Seg -> String
segPath Users  = "users"
segPath Posts  = "posts"
segPath Health = "health"

wireName :: WireTy -> String
wireName TInt    = "Int"
wireName TString = "String"
wireName TBool   = "Bool"

parseWire :: foreach (t :: WireTy) -> String -> Either String (interp t)
parseWire TInt    raw = maybe (Left ("400: bad Int " ++ raw)) Right (readMaybe raw)
parseWire TString raw = Right raw
parseWire TBool   raw = maybe (Left ("400: bad Bool " ++ raw)) Right (readMaybe raw)

renderWire :: foreach (t :: WireTy) -> interp t -> String
renderWire TInt    n = show n
renderWire TString s = s
renderWire TBool   b = show b

describeRoute :: Route -> String
describeRoute (Lit s  :> rest) = "/" ++ segPath s ++ describeRoute rest
describeRoute (Cap ty :> rest) = "/<" ++ wireName ty ++ ">" ++ describeRoute rest
describeRoute (Get res)        = " -> " ++ wireName res

buildLink :: foreach (r :: Route) -> LinkType r
buildLink r = go r ""
  where
    go :: foreach (r' :: Route) -> String -> LinkType r'
    go (Lit s  :> rest) acc = go rest (acc ++ "/" ++ segPath s)
    go (Cap ty :> rest) acc = \\val -> go rest (acc ++ "/" ++ renderWire ty val)
    go (Get _)          acc = acc

dispatch :: foreach (m :: RunMode) -> foreach (r :: Route)
         -> HandlerType m r -> [String] -> StackOut m (Either String String)
dispatch m r handler path = withStackMonad m (runMode m (go r handler path))
  where
    go :: Monad (StackM m)
       => foreach (r' :: Route) -> HandlerType m r' -> [String] -> StackM m (Either String String)
    go (Lit s :> rest) h ps = case ps of
      (p : ps') | p == segPath s -> go rest h ps'
                | otherwise      -> pure (Left ("404: expected /" ++ segPath s))
      []                         -> pure (Left ("404: missing /" ++ segPath s))
    go (Cap ty :> rest) h ps = case ps of
      (p : ps') -> case parseWire ty p of
                     Left err  -> pure (Left err)
                     Right val -> go rest (h val) ps'
      []        -> pure (Left "404: missing segment")
    go (Get res) h ps = case ps of
      [] -> do
        out <- h
        pure (case out of { Left err -> Left err; Right val -> Right (renderWire res val) })
      _  -> pure (Left "404: trailing path")

handleUserPost :: foreach (m :: RunMode) -> Int -> String -> StackM m (Either String Bool)
handleUserPost m uid slug = withStackMonad m (do
  recordHit m ("GET /users/" ++ show uid ++ "/posts/" ++ slug)
  pure (Right (uid > 0 && not (null slug))))

demo :: (String, String, ((Either String String, Int), [String]))
demo =
  ( describeRoute (apiRoute UserPost)
  , buildLink (apiRoute UserPost) 42 "dependent-haskell"
  , dispatch MeteredMode (apiRoute UserPost) (handleUserPost MeteredMode) ["users", "42", "posts", "dependent-haskell"]
  )
`,
  },
  {
    id: "holes",
    label: "Agda-mode & ProofSearch",
    replHint: ":t plusAssoc",
    code: `{-# LANGUAGE DependentTypes #-}
module Playground where

import Data.Nat.Dependent (Nat (..), plus)
import Data.Type.Equality.Dependent ((:~:) (Refl), cong)

-- Interactive Agda-mode proof in 3 clicks (powered by Dependent.Plugin.ProofSearch):
-- 1. Click "Check & Load in GHCi" -> GHC suggests splitting on \`m\`.
-- 2. Click "Split on m (Zero | Succ)" -> GHC generates both cases.
-- 3. Click \`Refl\`, then \`cong Succ (plusAssoc m n p)\` (or refine via \`cong Succ _\`)!
plusAssoc :: foreach (m n p :: Nat)
          -> plus (plus m n) p :~: plus m (plus n p)
plusAssoc m n p = _
`,
  },
  {
    id: "dep-compose",
    label: "Dependent (.) & dependent-base",
    replHint: "composeDemo",
    code: `{-# LANGUAGE DependentTypes, ListTuplePuns #-}
{-# OPTIONS_GHC -fno-enable-rewrite-rules #-}
module Playground where

import Prelude hiding ((.))
import Data.Function.Dependent ((.))
import Data.Nat.Dependent (Nat (..), natToInt, plus)
import Data.Nat.Dependent.Properties (plusZero)
import Data.Type.Equality.Dependent ((:~:) (Refl), cong)
import Data.Vec.Dependent (Vec (..), toListVec)

zeros :: foreach (n :: Nat) -> Vec Nat n
zeros Zero     = VNil
zeros (Succ n) = VCons Zero (zeros n)

-- First-class dependent composition (.):
zerosPlus1 :: foreach (n :: Nat) -> Vec Nat (plus 1 n)
zerosPlus1 = (.) zeros (plus 1)

plusIdSucc :: foreach (n :: Nat) -> plus (Succ n) Zero :~: Succ n
plusIdSucc = plusZero . Succ

congSuccPlus :: foreach (m :: Nat)
             -> forall (x y :: Nat). x :~: y -> Succ (plus m x) :~: Succ (plus m y)
congSuccPlus m eq = cong (Succ . plus m) eq

composeDemo :: [Int]
composeDemo = map natToInt (toListVec (zerosPlus1 2))
`,
  },
  {
    id: "lists",
    label: "Prelude List Laws",
    replHint: ":t lengthMap",
    code: `{-# LANGUAGE DependentTypes, NoListTuplePuns #-}
{-# OPTIONS_GHC -fno-enable-rewrite-rules #-}
module Playground where

import Data.List.Dependent (size)
import Data.Nat.Dependent (Nat (..), plus)
import Data.Type.Equality.Dependent ((:~:) (Refl), cong)
import GHC.Types (List)

lengthAppend :: forall a. foreach (xs ys :: List a)
             -> size (xs ++ ys) :~: plus (size xs) (size ys)
lengthAppend []       _  = Refl
lengthAppend (_ : xs) ys = cong Succ (lengthAppend xs ys)

lengthMap :: forall a b. foreach (f :: a -> b) -> foreach (xs :: List a)
          -> size (map f xs) :~: size xs
lengthMap _ []       = Refl
lengthMap f (_ : xs) = cong Succ (lengthMap f xs)
`,
  },
  {
    id: "sigma",
    label: "Dependent Pair (Sigma)",
    replHint: "extractHalf",
    code: `{-# LANGUAGE DependentTypes, UndecidableInstances #-}
module Playground where

import Data.Nat.Dependent (Nat (..), natToInt, plus)
import Data.Sigma.Dependent (Sigma (Pair))
import Data.Type.Equality ((:~:) (Refl))

type EvenSigma (n :: Nat) = some (k :: Nat) | plus k k :~: n

halfOfFour :: EvenSigma 4
halfOfFour = Pair 2 Refl

extractHalf :: Int
extractHalf = case halfOfFour of
  Pair k Refl -> natToInt k
`,
  },
  {
    id: "vec",
    label: "Length-Indexed Vectors",
    replHint: "lookupVec (FS FZ) combined",
    code: `{-# LANGUAGE DependentTypes #-}
module Playground where

import Data.Fin.Dependent (Fin (..))
import Data.Nat.Dependent (Nat (..))
import Data.Vec.Dependent (Vec (..), appendVec, headVec, lookupVec, mapVec)

xs :: Vec String 2
xs = VCons "dependent" (VCons "haskell" VNil)

ys :: Vec String 1
ys = VCons "works" VNil

combined :: Vec String 3
combined = appendVec xs ys

lengths :: Vec Int 3
lengths = mapVec length combined

firstWord :: String
firstWord = headVec combined
`,
  },
  {
    id: "linear-protocol",
    label: "Linear Session Protocol",
    replHint: "runSession",
    code: `{-# LANGUAGE DependentTypes, LinearTypes, ListTuplePuns #-}
module Playground where

import Data.Type.Equality ((:~:) (Refl))

data Ur a where
  Ur :: a -> Ur a

data ProtoState = StInit | StAuthed | StDone
data Agency     = ClientTurn | Closed

agency :: ProtoState -> Agency
agency StInit   = ClientTurn
agency StAuthed = ClientTurn
agency StDone   = Closed

type Payload (st :: ProtoState) = case st of
  StInit   -> String
  StAuthed -> Int
  StDone   -> ()

data Msg (from :: ProtoState) (to :: ProtoState) where
  MLogin  :: Payload StInit   -> Msg StInit   StAuthed
  MQuery  :: Payload StAuthed -> Msg StAuthed StAuthed
  MLogout ::                     Msg StAuthed StDone

data Chan (st :: ProtoState) = MkChan (Ur [String])

-- Linear retained transition: consumes the old channel once and requires ClientTurn.
send :: foreach (from %1 :: ProtoState)
     -> (agency from :~: ClientTurn)
     -> Msg from to -> Chan from %1 -> Chan to
send StInit   Refl (MLogin tok) (MkChan (Ur log0)) = MkChan (Ur (("AUTH "  ++ tok)      : log0))
send StAuthed Refl (MQuery qid) (MkChan (Ur log0)) = MkChan (Ur (("QUERY " ++ show qid) : log0))
send StAuthed Refl MLogout      (MkChan (Ur log0)) = MkChan (Ur ("BYE"                  : log0))

closeChan :: Chan StDone %1 -> [String]
closeChan (MkChan (Ur log0)) = reverse log0

runSession :: [String]
runSession =
  let c0 = MkChan (Ur []) :: Chan StInit
      c1 = send StInit   Refl (MLogin "tok-42") c0
      c2 = send StAuthed Refl (MQuery 7)        c1
      c3 = send StAuthed Refl MLogout           c2
  in closeChan c3
`,
  },
  {
    id: "typed-sql",
    label: "Typed SQL Schema",
    replHint: "sqlDemo",
    code: `{-# LANGUAGE DependentTypes, UndecidableInstances #-}
{-# OPTIONS_GHC -fno-enable-rewrite-rules #-}
module Playground where

import Data.Kind (Type)
import GHC.Tuple (Tuple2)
import GHC.Types (List)

data ColId = CId | CName | CActive
data SqlTy = SInt | SText | SBool
data Col   = MkCol ColId SqlTy

sqlVal :: SqlTy -> Type
sqlVal SInt  = type Int
sqlVal SText = type String
sqlVal SBool = type Bool

data Row (s :: List Col) where
  RNil  :: Row []
  RCons :: sqlVal t -> Row rest -> Row (MkCol c t : rest)

data InSchema (col :: Col) (s :: List Col) where
  Here  :: InSchema col (col : rest)
  There :: InSchema col rest -> InSchema col (other : rest)

data Table where
  MkTable :: foreach (s :: List Col) -> List (Row s) -> Table

colName :: ColId -> String
colName CId     = "id"
colName CName   = "name"
colName CActive = "active"

sqlTypeName :: SqlTy -> String
sqlTypeName SInt  = "INT"
sqlTypeName SText = "TEXT"
sqlTypeName SBool = "BOOL"

createTableDDL :: String -> List Col -> String
createTableDDL tbl cols = "CREATE TABLE " ++ tbl ++ " (" ++ go cols ++ ");"
  where
    go []                 = ""
    go [MkCol c t]        = colName c ++ " " ++ sqlTypeName t
    go (MkCol c t : rest) = colName c ++ " " ++ sqlTypeName t ++ ", " ++ go rest

getCol :: InSchema (MkCol c t) s -> Row s -> sqlVal t
getCol Here      (RCons v _)    = v
getCol (There p) (RCons _ rest) = getCol p rest

-- INNER JOIN combines schemas directly with Prelude (++):
joinRow :: Row s1 -> Row s2 -> Row (s1 ++ s2)
joinRow RNil         r2 = r2
joinRow (RCons v r1) r2 = RCons v (joinRow r1 r2)

type UserSchema = [MkCol CId SInt, MkCol CName SText, MkCol CActive SBool]

userRows :: List (Row UserSchema)
userRows =
  [ RCons 1 (RCons "Ada"   (RCons True  RNil))
  , RCons 2 (RCons "Grace" (RCons True  RNil))
  ]

usersTable :: Table
usersTable = MkTable [MkCol CId SInt, MkCol CName SText, MkCol CActive SBool] userRows

tableDDL :: String -> Table -> String
tableDDL name (MkTable s _) = createTableDDL name s

sqlDemo :: Tuple2 String (List String)
sqlDemo =
  ( tableDDL "users" usersTable
  , map (getCol (There Here)) userRows
  )
`,
  },
  {
    id: "effect-stack",
    label: "Composable Effect Stack",
    replHint: "effDemo",
    code: `{-# LANGUAGE DependentTypes, TypeFamilies, UndecidableInstances #-}
module Playground where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader (ReaderT, ask, runReaderT)
import Control.Monad.Trans.State.Strict (StateT, modify', runStateT)
import Control.Monad.Trans.Writer.Strict (WriterT, runWriterT, tell)
import Data.Functor.Identity (Identity (runIdentity))
import Data.Kind (Type)
import GHC.Tuple (Tuple2, Unit)
import GHC.Types (List)

data Eff = EEnv | ECount | ELog

type family StackM (es :: List Eff) :: Type -> Type where
  StackM []            = Identity
  StackM (EEnv   : es) = ReaderT String (StackM es)
  StackM (ECount : es) = StateT  Int    (StackM es)
  StackM (ELog   : es) = WriterT (List String) (StackM es)

type family StackOut (es :: List Eff) (a :: Type) :: Type where
  StackOut []            a = a
  StackOut (EEnv   : es) a = StackOut es a
  StackOut (ECount : es) a = StackOut es (Tuple2 a Int)
  StackOut (ELog   : es) a = StackOut es (Tuple2 a (List String))

withMonad :: foreach (es :: List Eff) -> (Monad (StackM es) => r) -> r
withMonad []            k = k
withMonad (EEnv   : es) k = withMonad es k
withMonad (ECount : es) k = withMonad es k
withMonad (ELog   : es) k = withMonad es k

runStack :: foreach (es :: List Eff) -> String -> StackM es a -> StackOut es a
runStack []            _   m = runIdentity m
runStack (EEnv   : es) env m = runStack es env (runReaderT m env)
runStack (ECount : es) env m = runStack es env (runStateT  m 0)
runStack (ELog   : es) env m = runStack es env (runWriterT m)

data Has (e :: Eff) (es :: List Eff) where
  Here  :: Has e (e : es)
  There :: Has e es -> Has e (x : es)

liftStep :: foreach (x :: Eff) (es :: List Eff)
         -> (Monad (StackM es) => StackM es a -> StackM (x : es) a)
liftStep EEnv   _ m = lift m
liftStep ECount _ m = lift m
liftStep ELog   _ m = lift m

askEff :: foreach (es :: List Eff) -> Has EEnv es -> StackM es String
askEff []       h = case h of {}
askEff (x : es) h = case x of
  EEnv   -> case h of { Here -> withMonad es ask; There p -> withMonad es (liftStep EEnv es (askEff es p)) }
  ECount -> case h of { There p -> withMonad es (liftStep ECount es (askEff es p)) }
  ELog   -> case h of { There p -> withMonad es (liftStep ELog es (askEff es p)) }

tickEff :: foreach (es :: List Eff) -> Has ECount es -> StackM es Unit
tickEff []       h = case h of {}
tickEff (x : es) h = case x of
  EEnv   -> case h of { There p -> withMonad es (liftStep EEnv es (tickEff es p)) }
  ECount -> case h of { Here -> withMonad es (modify' (+ 1)); There p -> withMonad es (liftStep ECount es (tickEff es p)) }
  ELog   -> case h of { There p -> withMonad es (liftStep ELog es (tickEff es p)) }

tellEff :: foreach (es :: List Eff) -> Has ELog es -> String -> StackM es Unit
tellEff []       h _   = case h of {}
tellEff (x : es) h msg = case x of
  EEnv   -> case h of { There p -> withMonad es (liftStep EEnv es (tellEff es p msg)) }
  ECount -> case h of { There p -> withMonad es (liftStep ECount es (tellEff es p msg)) }
  ELog   -> case h of { Here -> withMonad es (tell [msg]); There p -> withMonad es (liftStep ELog es (tellEff es p msg)) }

worker :: foreach (es :: List Eff)
       -> Has EEnv es -> Has ECount es -> Has ELog es
       -> StackM es String
worker es hEnv hCount hLog = withMonad es (do
  env <- askEff es hEnv
  tellEff es hLog ("boot:" ++ env)
  tickEff es hCount
  tickEff es hCount
  tellEff es hLog "done"
  pure ("ok@" ++ env))

effDemo :: Tuple2 (Tuple2 String Int) (List String)
effDemo = runStack [EEnv, ECount, ELog] "prod"
  (worker [EEnv, ECount, ELog] Here (There Here) (There (There Here)))
`,
  },
  {
    id: "typed-net",
    label: "Shape-Checked Neural Net",
    replHint: "netDemo",
    code: `{-# LANGUAGE DependentTypes, ListTuplePuns #-}
module Playground where

import Data.Nat.Dependent (Nat (..), mul)
import Data.Nat.Dependent.Properties (mulComm)
import Data.Type.Equality.Dependent (rewrite)
import Data.Vec.Dependent (Vec (..), appendVec, foldrVec, mapVec, toListVec, zipWithVec)

type Matrix r c = Vec (Vec Double c) r

dot :: Vec Double n -> Vec Double n -> Double
dot xs ys = foldrVec (+) 0 (zipWithVec (*) xs ys)

matVec :: Matrix out inp -> Vec Double inp -> Vec Double out
matVec weights x = mapVec (\`dot\` x) weights

data Net (inp :: Nat) (out :: Nat) where
  NId    :: Net n n
  NDense :: Matrix h i -> Net h o -> Net i o

forward :: Net i o -> Vec Double i -> Vec Double o
forward NId          x = x
forward (NDense w n) x = forward n (mapVec (max 0) (matVec w x))

flatten :: foreach (r c :: Nat) -> Matrix r c -> Vec Double (mul r c)
flatten Zero     _ VNil           = VNil
flatten (Succ r) c (VCons row rs) = appendVec row (flatten r c rs)

-- Constructive reshape via dependent-base's proved mulComm (no ghc-typelits plugin):
reshapeTranspose :: foreach (r c :: Nat) -> Vec Double (mul r c) -> Vec Double (mul c r)
reshapeTranspose r c v = rewrite (mulComm r c) v

layer1 :: Matrix 2 3
layer1 =
  VCons (VCons 1.0 (VCons 2.0 (VCons (-1.0) VNil)))
 (VCons (VCons 0.5 (VCons (-1.0) (VCons 2.0 VNil))) VNil)

layer2 :: Matrix 1 2
layer2 = VCons (VCons 2.0 (VCons 3.0 VNil)) VNil

sampleNet :: Net 3 1
sampleNet = NDense layer1 (NDense layer2 NId)

netDemo :: ([Double], [Double])
netDemo =
  ( toListVec (forward sampleNet (VCons 1.0 (VCons 1.0 (VCons 1.0 VNil))))
  , toListVec (reshapeTranspose 2 3 (flatten 2 3 layer1))
  )
`,
  },
  {
    id: "checked-codec",
    label: "Checked Wire Codec",
    replHint: "codecDemo",
    code: `{-# LANGUAGE DependentTypes, ListTuplePuns #-}
module Playground where

import Data.Kind (Type)
import Data.Type.Equality.Dependent ((:~:) (Refl), cong, rewrite)

data Schema = SEnd | SInt String Schema | SBool String Schema

payload :: Schema -> Type
payload SEnd        = type ()
payload (SInt  _ r) = type (Int,  payload r)
payload (SBool _ r) = type (Bool, payload r)

docSchema :: Schema -> String
docSchema SEnd        = "{}"
docSchema (SInt  f r) = f ++ ":int, "  ++ docSchema r
docSchema (SBool f r) = f ++ ":bool, " ++ docSchema r

data Tok = TokInt Int | TokBool Bool deriving (Eq, Show)

encode :: foreach (s :: Schema) -> payload s -> [Tok]
encode SEnd        ()      = []
encode (SInt  _ r) (n, xs) = TokInt  n : encode r xs
encode (SBool _ r) (b, xs) = TokBool b : encode r xs

decode :: foreach (s :: Schema) -> [Tok] -> Either String (payload s)
decode SEnd        []               = Right ()
decode SEnd        _                = Left "trailing tokens"
decode (SInt  _ r) (TokInt  n : ts) = fmap (\\xs -> (n, xs)) (decode r ts)
decode (SBool _ r) (TokBool b : ts) = fmap (\\xs -> (b, xs)) (decode r ts)
decode (SInt  f _) _                = Left ("expected int for "  ++ f)
decode (SBool f _) _                = Left ("expected bool for " ++ f)

appendSchema :: Schema -> Schema -> Schema
appendSchema SEnd        s2 = s2
appendSchema (SInt  f r) s2 = SInt  f (appendSchema r s2)
appendSchema (SBool f r) s2 = SBool f (appendSchema r s2)

appendSchemaAssoc :: foreach (a b c :: Schema)
                  -> appendSchema (appendSchema a b) c :~: appendSchema a (appendSchema b c)
appendSchemaAssoc SEnd        _ _ = Refl
appendSchemaAssoc (SInt  f r) b c = cong (SInt  f) (appendSchemaAssoc r b c)
appendSchemaAssoc (SBool f r) b c = cong (SBool f) (appendSchemaAssoc r b c)

newtype Packet (s :: Schema) = MkPacket { unPacket :: [Tok] } deriving Show

reassocPacket :: foreach (a b c :: Schema)
              -> Packet (appendSchema (appendSchema a b) c)
              -> Packet (appendSchema a (appendSchema b c))
reassocPacket a b c p = rewrite (appendSchemaAssoc a b c) p

codecDemo :: (String, [Tok], Either String (Int, (Bool, (Int, ()))))
codecDemo =
  let wire = encode (SInt "id" (SBool "active" (SInt "score" SEnd))) (7, (True, (99, ())))
      pkt  = reassocPacket (SInt "id" SEnd) (SBool "active" SEnd) (SInt "score" SEnd) (MkPacket wire)
  in ( docSchema (SInt "id" (SBool "active" (SInt "score" SEnd)))
     , unPacket pkt
     , decode (SInt "id" (SBool "active" (SInt "score" SEnd))) (unPacket pkt)
     )
`,
  },
  {
    id: "units-of-measure",
    label: "Units of Measure",
    replHint: "physicsDemo",
    code: `{-# LANGUAGE DependentTypes, ListTuplePuns #-}
module Playground where

import Data.Nat.Dependent (Nat (..), minus, plus)
import Data.Nat.Dependent.Properties (minusDiag, plusComm)
import Data.Type.Equality.Dependent (rewrite)

newtype Qty (mp :: Nat) (mn :: Nat) (sp :: Nat) (sn :: Nat) = Qty { unQty :: Double }
  deriving Show

type Scalar = Qty 0 0 0 0
type Meter  = Qty 1 0 0 0
type Sec    = Qty 0 0 1 0
type Speed  = Qty 1 0 0 1

(+!) :: Qty mp mn sp sn -> Qty mp mn sp sn -> Qty mp mn sp sn
Qty x +! Qty y = Qty (x + y)

(*!) :: Qty mp1 mn1 sp1 sn1 -> Qty mp2 mn2 sp2 sn2
     -> Qty (plus mp1 mp2) (plus mn1 mn2) (plus sp1 sp2) (plus sn1 sn2)
Qty x *! Qty y = Qty (x * y)

(/!) :: Qty mp1 mn1 sp1 sn1 -> Qty mp2 mn2 sp2 sn2
     -> Qty (plus mp1 mn2) (plus mn1 mp2) (plus sp1 sn2) (plus sn1 sp2)
Qty x /! Qty y = Qty (x / y)

normalize :: Qty mp mn sp sn -> Qty (minus mp mn) (minus mn mp) (minus sp sn) (minus sn sp)
normalize (Qty x) = Qty x

commUnit :: foreach (mp1 mn1 sp1 sn1 mp2 mn2 sp2 sn2 :: Nat)
         -> Qty (plus mp1 mp2) (plus mn1 mn2) (plus sp1 sp2) (plus sn1 sn2)
         -> Qty (plus mp2 mp1) (plus mn2 mn1) (plus sp2 sp1) (plus sn2 sn1)
commUnit mp1 mn1 sp1 sn1 mp2 mn2 sp2 sn2 q =
  rewrite (plusComm mp1 mp2) (rewrite (plusComm mn1 mn2)
    (rewrite (plusComm sp1 sp2) (rewrite (plusComm sn1 sn2) q)))

cancelSelf :: foreach (mp mn sp sn :: Nat)
           -> Qty (plus mp mn) (plus mn mp) (plus sp sn) (plus sn sp)
           -> Scalar
cancelSelf mp mn sp sn q =
  rewrite (plusComm mn mp)
    (rewrite (plusComm sn sp)
      (rewrite (minusDiag (plus mp mn))
        (rewrite (minusDiag (plus sp sn)) (normalize q))))

physicsDemo :: (Double, Double)
physicsDemo =
  let dist  = Qty 100.0 :: Meter
      time  = Qty 10.0  :: Sec
      speed = normalize (dist /! time) :: Speed
      ratio = cancelSelf 1 0 0 0 (dist /! dist)
  in (unQty speed, unQty ratio)
`,
  },
  {
    id: "block-chunking",
    label: "Block Chunking (ObsEq)",
    replHint: "chunkDemo",
    code: `{-# LANGUAGE DependentTypes, ListTuplePuns #-}
{-# OPTIONS_GHC -fplugin=Dependent.Plugin.ObsEq -fplugin-opt=Dependent.Plugin.ObsEq:tests=30 #-}
module Playground where

import Data.Nat.Dependent (Nat (..), minus, mul, plus)
import Data.Type.Equality ((:~:), gcastWith, sym)
import Data.Vec.Dependent (Vec (..), appendVec, toListVec)
import Dependent.ObsEq (ObsConfig, defaultObsConfig, obsEqWith, withMaxSize, withPartialPct)

totalCfg :: ObsConfig
totalCfg = withMaxSize 8 (withPartialPct 0 defaultObsConfig)

ltNat :: Nat -> Nat -> Bool
ltNat _        Zero     = False
ltNat Zero     (Succ _) = True
ltNat (Succ m) (Succ n) = ltNat m n

-- Try changing \`ltNat n d\` to \`not (ltNat d n)\` (off-by-one bug) and re-check:
divNat :: Nat -> Nat -> Nat
divNat n d
  | ltNat n d = Zero
  | otherwise = Succ (divNat (minus n d) d)

modNat :: Nat -> Nat -> Nat
modNat n d
  | ltNat n d = n
  | otherwise = modNat (minus n d) d

concatBlocks :: forall a (k d :: Nat). Vec (Vec a d) k -> Vec a (mul k d)
concatBlocks VNil         = VNil
concatBlocks (VCons b bs) = appendVec b (concatBlocks bs)

divModLaw :: foreach (n d' :: Nat)
          -> plus (mul (divNat n (Succ d')) (Succ d')) (modNat n (Succ d')) :~: n
divModLaw n d' = obsEqWith totalCfg

reassemble :: forall a. foreach (n d' :: Nat)
           -> Vec (Vec a (Succ d')) (divNat n (Succ d'))
           -> Vec a (modNat n (Succ d'))
           -> Vec a n
reassemble n d' blocks remChunk =
  gcastWith (divModLaw n d') (appendVec (concatBlocks blocks) remChunk)

chunkDemo :: [Int]
chunkDemo =
  let b1, b2 :: Vec Int 3
      b1   = VCons 1 (VCons 2 (VCons 3 VNil))
      b2   = VCons 4 (VCons 5 (VCons 6 VNil))
      tl :: Vec Int 2
      tl   = VCons 7 (VCons 8 VNil)
      blks = gcastWith (sym (obsEqWith totalCfg :: divNat 8 3 :~: 2)) (VCons b1 (VCons b2 VNil))
      remV = gcastWith (sym (obsEqWith totalCfg :: modNat 8 3 :~: 2)) tl
  in toListVec (reassemble 8 2 blks remV)
`,
  },
  {
    id: "goldbach",
    label: "Goldbach (1742 · ObsEq)",
    replHint: "goldbachDemo",
    code: `{-# LANGUAGE DependentTypes, ListTuplePuns #-}
{-# OPTIONS_GHC -fplugin=Dependent.Plugin.ObsEq -fplugin-opt=Dependent.Plugin.ObsEq:tests=40 #-}
module Playground where

import Data.Type.Equality ((:~:))
import Dependent.ObsEq (Gen, chooseInt, obsEqGen)

isPrime :: Int -> Bool
isPrime n = n >= 2 && go 2
  where
    go d
      | d * d > n      = True
      | n \`mod\` d == 0 = False
      | otherwise      = go (d + 1)

goldbach :: Int -> (Int, Int)
goldbach n = go 2
  where
    go p
      | p > n                        = (0, 0)
      | isPrime p && isPrime (n - p) = (p, n - p)
      | otherwise                    = go (p + 1)

validGoldbach :: Int -> Bool
validGoldbach n
  | n < 4     = True
  | otherwise = let (p, q) = goldbach n in isPrime p && isPrime q && p + q == n

-- Try changing \`(* 2) <$> chooseInt (2, 100)\` to \`chooseInt (4, 100)\` to allow odd inputs:
genEvenGe4 :: Gen Int
genEvenGe4 = (* 2) <$> chooseInt (2, 100)

data GoldbachCert (n :: Int) where
  MkGoldbach :: (Int, Int) -> (validGoldbach n :~: True) -> GoldbachCert n

certifyGoldbach :: foreach (n :: Int) -> GoldbachCert n
certifyGoldbach n = MkGoldbach (goldbach n) (obsEqGen genEvenGe4)

runGoldbach :: Int -> (Int, Int)
runGoldbach n = case certifyGoldbach n of MkGoldbach pq _ -> pq

goldbachDemo :: [(Int, (Int, Int))]
goldbachDemo = [(n, runGoldbach n) | n <- [4, 28, 100]]
`,
  },
  {
    id: "four-squares",
    label: "Four Squares (1770 · ObsEq)",
    replHint: "lagrangeDemo",
    code: `{-# LANGUAGE DependentTypes, ListTuplePuns #-}
{-# OPTIONS_GHC -fplugin=Dependent.Plugin.ObsEq -fplugin-opt=Dependent.Plugin.ObsEq:tests=50 #-}
module Playground where

import Data.Type.Equality ((:~:))
import Dependent.ObsEq (ObsConfig, defaultObsConfig, obsEqWith, withMaxSize, withPartialPct)

totalCfg :: ObsConfig
totalCfg = withMaxSize 30 (withPartialPct 0 defaultObsConfig)

isqrt :: Int -> Int
isqrt n = go 0
  where
    go k | (k + 1) * (k + 1) > n = k
         | otherwise             = go (k + 1)

-- Change \`d <- [0 .. isqrt r3]\` to \`d <- [0]\` (3 squares) to see GHC shrink to n = 7:
fourSquares :: Int -> (Int, Int, Int, Int)
fourSquares n = case
  [ (a, b, c, d)
  | a <- [0 .. isqrt n]
  , let r1 = n - a * a
  , b <- [0 .. isqrt r1]
  , let r2 = r1 - b * b
  , c <- [0 .. isqrt r2]
  , let r3 = r2 - c * c
  , d <- [0 .. isqrt r3]
  , d * d == r3
  ] of
    (sol : _) -> sol
    []        -> (0, 0, 0, 0)

sumSq4 :: Int -> Int
sumSq4 n
  | n < 0     = n
  | otherwise = case fourSquares n of (a, b, c, d) -> a * a + b * b + c * c + d * d

data FourSqCert (n :: Int) where
  MkFourSq :: (Int, Int, Int, Int) -> (sumSq4 n :~: n) -> FourSqCert n

lagrange :: foreach (n :: Int) -> FourSqCert n
lagrange n = MkFourSq (fourSquares n) (obsEqWith totalCfg)

runLagrange :: Int -> (Int, Int, Int, Int)
runLagrange n = case lagrange n of MkFourSq q _ -> q

lagrangeDemo :: [(Int, (Int, Int, Int, Int))]
lagrangeDemo = [(n, runLagrange n) | n <- [7, 15, 23, 42]]
`,
  },
  {
    id: "nqueens",
    label: "N-Queens (NP · ObsEq)",
    replHint: "queensDemo",
    code: `{-# LANGUAGE DependentTypes, ListTuplePuns #-}
{-# OPTIONS_GHC -fplugin=Dependent.Plugin.ObsEq -fplugin-opt=Dependent.Plugin.ObsEq:tests=30 #-}
module Playground where

import Data.Type.Equality ((:~:))
import Dependent.ObsEq (ObsConfig, defaultObsConfig, obsEqWith, withMaxSize, withPartialPct)

boardCfg :: ObsConfig
boardCfg = withMaxSize 8 (withPartialPct 0 defaultObsConfig)

safePlace :: Int -> [Int] -> Bool
safePlace q placed = and [q /= r && abs (q - r) /= d | (d, r) <- zip [1..] placed]

solveQueens :: Int -> [Int]
solveQueens n = case go n of
  (board : _) -> board
  []          -> []
  where
    go 0 = [[]]
    go k = [q : qs | qs <- go (k - 1), q <- [1 .. n], safePlace q qs]

validBoard :: Int -> [Int] -> Bool
validBoard n qs =
  length qs == n && all (\\q -> q >= 1 && q <= n) qs && check qs
  where
    check []       = True
    check (q : rs) = safePlace q rs && check rs

-- Try changing \`n < 4\` to \`n < 2\` to see GHC shrink to n = 2:
queensValid :: Int -> Bool
queensValid n
  | n < 4     = True
  | otherwise = validBoard n (solveQueens n)

data QueensCert (n :: Int) where
  MkQueens :: [Int] -> (queensValid n :~: True) -> QueensCert n

certifyQueens :: foreach (n :: Int) -> QueensCert n
certifyQueens n = MkQueens (solveQueens n) (obsEqWith boardCfg)

runQueens :: Int -> [Int]
runQueens n = case certifyQueens n of MkQueens board _ -> board

queensDemo :: [(Int, [Int])]
queensDemo = [(n, runQueens n) | n <- [4, 5, 6, 8]]
`,
  },
  {
    id: "typecase-records",
    label: "Type Case, Record Dot & Sections",
    replHint: "(defaultVal String, sampleItems, pairChars)",
    code: `{-# LANGUAGE DependentTypes, ListTuplePuns, OverloadedRecordDot #-}
module Playground where

import Data.Kind (Type)
import Data.Nat.Dependent (Nat (..), natToInt)
import Data.Sigma.Dependent (Sigma (Pair), first)
import Data.Type.Equality.Dependent ((:~:) (Refl), cong)
import Data.Vec.Dependent (SomeVec, Vec (..), toListVec)
import GHC.Sigma.Projection (second)

-- 1. Runtime Type pattern matching (Proposal #378 section 4.9):
defaultVal :: foreach (a :: Type) -> Maybe a
defaultVal a = case a of
  Int    -> Just 0
  Bool   -> Just True
  [Char] -> Just "dependent haskell"
  _      -> Nothing

-- 2. Dependent OverloadedRecordDot on dependent records and Sigma:
data SizedVec a = SizedVec
  { vecLen   :: Nat
  , vecItems :: Vec a vecLen
  }

sampleVec :: SizedVec String
sampleVec = SizedVec 2 (VCons "dependent" (VCons "base" VNil))

sampleLen :: Int
sampleLen = natToInt sampleVec.vecLen

sampleItems :: [String]
sampleItems = toListVec sampleVec.vecItems

pairVec :: SomeVec Char
pairVec = Pair 2 (VCons 'o' (VCons 'k' VNil))

readSecond :: forall a. foreach (p :: SomeVec a) -> Vec a (first p)
readSecond p = p.second

pairChars :: String
pairChars = toListVec (readSecond pairVec)

-- 3. Operator sections directly inside cong:
congConsL :: forall a (x :: a) (ys1 ys2 :: [a]).
             ys1 :~: ys2 -> (x : ys1) :~: (x : ys2)
congConsL eq = cong (x :) eq

congConsR :: forall a (x1 x2 :: a) (ys :: [a]).
             x1 :~: x2 -> (x1 : ys) :~: (x2 : ys)
congConsR eq = cong (: ys) eq
`,
  },
  {
    id: "debruijn",
    label: "Intrinsically-Typed STLC",
    replHint: "evalTwoPlusTwo",
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

termToInt :: DB.Term DB.CEmpty DB.TNat -> Int
termToInt DB.Zero    = 0
termToInt (DB.Suc n) = 1 + termToInt n
termToInt _          = -1

-- Run PLFH's intrinsically-typed STLC evaluator on \`2 + 2\` with 40 steps of gas:
evalTwoPlusTwo :: Int
evalTwoPlusTwo =
  let prog :: DB.Term DB.CEmpty DB.TNat
      prog = DB.App (DB.App DB.plusTerm DB.termTwo) DB.termTwo
  in case DB.eval (DB.MkGas 40) prog of
       DB.Done v _ _   -> termToInt v
       DB.OutOfGas _ _ -> -1
`,
  },
  {
    id: "obseq",
    label: "Observational Equality (ObsEq)",
    replHint: "sampleAccVec",
    code: `{-# LANGUAGE DependentTypes, ListTuplePuns #-}
{-# OPTIONS_GHC -fplugin=Dependent.Plugin.ObsEq -fplugin-opt=Dependent.Plugin.ObsEq:tests=30 #-}
module Playground where

import Data.Nat.Dependent (Nat (..), plus)
import Data.Type.Equality ((:~:) (Refl), gcastWith)
import Data.Vec.Dependent (Vec (..), toListVec)
import Dependent.ObsEq
  ( Gen
  , ObsConfig
  , chooseInt
  , defaultObsConfig
  , obsEq
  , obsEqGen
  , obsEqWith
  , withMaxSize
  , withObsEqWith
  , withPartialPct
  , withTests
  )

-- Non-structural unfold addition (lazy-equivalent to plus on partial inputs):
unfoldPlus :: Nat -> Nat -> Nat
unfoldPlus m n = step (Just m) n
  where
    step Nothing acc         = acc
    step (Just Zero) acc     = step Nothing acc
    step (Just (Succ k)) acc = Succ (step (Just k) acc)

-- Non-structural tail-recursive accumulator addition.
-- Try changing \`go Zero acc = acc\` to \`go Zero acc = Succ acc\` to see a shrunk counterexample!
accPlus :: Nat -> Nat -> Nat
accPlus m n = go m n
  where
    go Zero acc     = acc
    go (Succ k) acc = go k (Succ acc)

twiceHalfEven :: Int -> Int
twiceHalfEven n
  | even n    = (n \`quot\` 2) * 2
  | otherwise = error "twiceHalfEven: odd input"

genEvenInt :: Gen Int
genEvenInt = (* 2) <$> chooseInt (-50, 50)

totalCfg :: ObsConfig
totalCfg = withMaxSize 12 (withPartialPct 0 (withTests 30 defaultObsConfig))

unfoldPlusCorrect :: foreach (m n :: Nat) -> unfoldPlus m n :~: plus m n
unfoldPlusCorrect m n = obsEq

accPlusCorrect :: foreach (m n :: Nat) -> accPlus m n :~: plus m n
accPlusCorrect m n = obsEqWith totalCfg

evenRoundtrip :: foreach (n :: Int) -> twiceHalfEven n :~: n
evenRoundtrip n = obsEqGen genEvenInt

-- Transport a Vec across an observational witness:
-- gcastWith transports via (:~:); withObsEqWith brings (a ~ b) into scope directly under totalCfg.
toAccVec :: foreach (m n :: Nat) -> Vec Int (plus m n) -> Vec Int (accPlus m n)
toAccVec m n v = gcastWith (obsEqWith totalCfg :: plus m n :~: accPlus m n) v

fromAccVec :: foreach (m n :: Nat) -> Vec Int (accPlus m n) -> Vec Int (plus m n)
fromAccVec m n v = withObsEqWith totalCfg @(accPlus m n) @(plus m n) @(Vec Int (plus m n)) v

sampleAccVec :: [Int]
sampleAccVec = toListVec (fromAccVec 2 1 (toAccVec 2 1 (VCons 10 (VCons 20 (VCons 30 VNil)))))
`,
  },
  {
    id: "neg",
    label: "Type Error (2 + 2 = 5)",
    replHint: ":k! plus 2 2",
    code: `{-# LANGUAGE DependentTypes #-}
module Playground where

import Data.Nat.Dependent (Nat (..), plus)
import Data.Type.Equality ((:~:) (Refl))

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

  const editor = createAgdaEditor({
    initialValue: activePreset.code,
    rows: 16,
    extraClass: "plfh-playground-editor",
  });

  const replInput = document.createElement("input");
  replInput.type = "text";
  replInput.className = "plfh-wasm-repl-input";
  replInput.placeholder = `Try ${activePreset.replHint}, :browse Prelude.Dependent, :t ..., or :k! plus 2 3`;
  replInput.setAttribute("aria-label", "Playground GHCi prompt");

  const selectPreset = (preset) => {
    activePreset = preset;
    editor.value = preset.code;
    replInput.placeholder = `Try ${preset.replHint}, :browse Prelude.Dependent, :t ..., or :k! plus 2 3`;
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
    "Enable Dependent Haskell refinement hole fits & subgoal splitting (on by default under -XDependentTypes)";
  const refineCheckbox = document.createElement("input");
  refineCheckbox.type = "checkbox";
  refineCheckbox.checked = uiState.refinementFits;
  refineCheckbox.addEventListener("change", () => {
    uiState.refinementFits = refineCheckbox.checked;
  });
  refineLabel.append(refineCheckbox, document.createTextNode(" Refinement fits"));

  const proofLabel = document.createElement("label");
  proofLabel.className = "plfh-refinement-toggle";
  proofLabel.title =
    "Enable Dependent.Plugin.ProofSearch (-fplugin=Dependent.Plugin.ProofSearch) for congruence/transitivity subgoal refinements & bounded proof search";
  const proofCheckbox = document.createElement("input");
  proofCheckbox.type = "checkbox";
  proofCheckbox.checked = uiState.proofSearch;
  proofCheckbox.addEventListener("change", () => {
    uiState.proofSearch = proofCheckbox.checked;
  });
  proofLabel.append(proofCheckbox, document.createTextNode(" ProofSearch plugin"));

  const statusSpan = document.createElement("span");
  statusSpan.className = "plfh-wasm-status";
  statusSpan.textContent = "Loads Dependent GHCi (Wasm) on first run";

  toolbar.append(checkBtn, resetBtn, refineLabel, proofLabel, statusSpan);

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

  mountEl.append(presetBar, toolbar, editor.root, holePanel, output, replRow);

  client.onProgress((p) => {
    const msg = formatProgress(p);
    if (msg) statusSpan.textContent = msg;
  });

  const runCheck = async () => {
    const rawCode = editor.value.trim();
    if (!rawCode) return;
    checkBtn.disabled = true;
    holePanel.hidden = true;
    editor.setChecking();
    statusSpan.textContent = client.booted
      ? "Checking..."
      : "Starting Dependent GHCi Wasm...";
    const res = await client.checkBlock({
      code: editor.value,
      chapterModule: null,
      extraGhcArgs: refinementExtraGhcArgs(uiState),
    });
    checkBtn.disabled = false;
    output.hidden = false;
    const combined = [res.stderr, res.stdout].filter(Boolean).join("\n");
    const hasHoles = !res.ok && combined.includes("Found hole:");
    const lineOffset = res.lineOffset ?? null;
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
    if (res.ok) {
      editor.setVerified({
        holes: [],
        lineOffset,
        semanticTokens: res.semanticTokens ?? null,
      });
    } else if (hasHoles) {
      const parsedHoles = parseTypedHoles(combined);
      editor.setVerified({ holes: parsedHoles, lineOffset });
      renderHolePanel(holePanel, combined, {
        code: editor.value,
        lineOffset,
        onFill: (hole, fitExpr) => {
          editor.value = applyHoleFit(editor.value, hole, fitExpr, lineOffset);
          editor.focus();
          runCheck();
        },
        onSplit: (hole, split) => {
          editor.value = applyCaseSplit(editor.value, hole, split, lineOffset);
          editor.focus();
          runCheck();
        },
      });
    } else {
      editor.setErrors({
        errors: parseErrorSpans(combined, lineOffset),
        lineOffset,
      });
    }
  };

  checkBtn.addEventListener("click", runCheck);
  wireEditorKeys(editor.textarea, runCheck);

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

function mountShowcaseBar(mountEl, client, uiState, cardEntries) {
  mountEl.innerHTML = "";
  mountEl.classList.add("plfh-chapter-bar--ready");

  const acts = [...document.querySelectorAll(".plfh-showcase-act")];
  const completeEntries = cardEntries.filter((e) => !e.isHole);
  const holeEntries = cardEntries.filter((e) => e.isHole);

  const header = document.createElement("div");
  header.className = "plfh-chapter-bar-row";

  const label = document.createElement("span");
  label.className = "plfh-chapter-bar-title";
  const holeSuffix =
    holeEntries.length > 0
      ? ` + ${holeEntries.length} Agda-mode hole${holeEntries.length === 1 ? "" : "s"}`
      : "";
  label.innerHTML = `<strong>Live Walkthrough (Wasm):</strong> ${completeEntries.length} runnable modules${holeSuffix}`;

  const actions = document.createElement("div");
  actions.className = "plfh-chapter-bar-actions";

  const checkAllBtn = document.createElement("button");
  checkAllBtn.type = "button";
  checkAllBtn.className = "plfh-wasm-btn plfh-wasm-check";
  checkAllBtn.textContent = `Check All ${completeEntries.length} Modules`;

  const refineLabel = document.createElement("label");
  refineLabel.className = "plfh-refinement-toggle";
  refineLabel.title =
    "Enable general refinement hole fits (-frefinement-level-hole-fits=2 -fabstract-refinement-hole-fits)";
  const refineCheckbox = document.createElement("input");
  refineCheckbox.type = "checkbox";
  refineCheckbox.checked = uiState.refinementFits;
  refineCheckbox.addEventListener("change", () => {
    uiState.refinementFits = refineCheckbox.checked;
  });
  refineLabel.append(refineCheckbox, document.createTextNode(" Refinement fits"));

  const proofLabel = document.createElement("label");
  proofLabel.className = "plfh-refinement-toggle";
  proofLabel.title =
    "Enable Dependent.Plugin.ProofSearch (-fplugin=Dependent.Plugin.ProofSearch)";
  const proofCheckbox = document.createElement("input");
  proofCheckbox.type = "checkbox";
  proofCheckbox.checked = uiState.proofSearch;
  proofCheckbox.addEventListener("change", () => {
    uiState.proofSearch = proofCheckbox.checked;
  });
  proofLabel.append(proofCheckbox, document.createTextNode(" ProofSearch plugin"));

  const statusSpan = document.createElement("span");
  statusSpan.className = "plfh-wasm-status";
  statusSpan.textContent = "Loads Dependent GHCi (Wasm) on demand";

  actions.append(checkAllBtn, refineLabel, proofLabel);
  header.append(label, actions, statusSpan);
  mountEl.append(header);

  const actCheckBtns = [];
  const actJumpBtns = new Map();
  const actCountSpans = new Map();

  const updateActProgress = () => {
    for (const actEl of acts) {
      const actId = actEl.id;
      const entries = completeEntries.filter((e) => e.actId === actId);
      const badge = actCountSpans.get(actId);
      if (!badge) continue;
      if (entries.length === 0) {
        badge.textContent = "hole";
        continue;
      }
      const passed = entries.filter((e) => e.passed).length;
      badge.textContent = passed === entries.length ? `✓ ${passed}/${entries.length}` : `${passed}/${entries.length}`;
      badge.classList.toggle("plfh-act-count--done", passed === entries.length);
    }
  };

  for (const entry of cardEntries) {
    entry.onPassChange = updateActProgress;
  }

  client.onProgress((p) => {
    if (statusSpan.dataset.active !== "1") return;
    const msg = formatProgress(p);
    if (msg) statusSpan.textContent = msg;
  });

  const setBatchDisabled = (disabled) => {
    checkAllBtn.disabled = disabled;
    for (const b of actCheckBtns) b.disabled = disabled;
  };

  const runBatch = async (entries, desc) => {
    if (entries.length === 0) return;
    setBatchDisabled(true);
    statusSpan.dataset.active = "1";
    const t0 = performance.now();
    let passed = 0;
    let failed = 0;
    for (let i = 0; i < entries.length; i++) {
      statusSpan.textContent = client.booted
        ? `Checking ${desc} (${i + 1}/${entries.length})...`
        : "Starting Dependent GHCi Wasm...";
      const ok = await entries[i].run();
      if (ok) passed++;
      else failed++;
    }
    const elapsedMs = Math.round(performance.now() - t0);
    statusSpan.dataset.active = "0";
    setBatchDisabled(false);
    updateActProgress();
    statusSpan.textContent =
      failed === 0
        ? `All ${passed}/${entries.length} modules verified ✓ (${elapsedMs} ms)`
        : `${passed}/${entries.length} verified, ${failed} failed (${elapsedMs} ms)`;
  };

  if (acts.length > 0) {
    const jumpBar = document.createElement("nav");
    jumpBar.className = "plfh-act-jump-bar";
    jumpBar.setAttribute("aria-label", "Walkthrough sections");

    for (const actEl of acts) {
      const actId = actEl.id;
      const num = actEl.dataset.actNum || "";
      const title = actEl.dataset.actTitle || actId;
      const entries = completeEntries.filter((e) => e.actId === actId);

      const jumpBtn = document.createElement("button");
      jumpBtn.type = "button";
      jumpBtn.className = "plfh-act-jump-btn";
      jumpBtn.dataset.actTarget = actId;

      const numSpan = document.createElement("span");
      numSpan.className = "plfh-act-num";
      numSpan.textContent = `Part ${num}`;

      const titleSpan = document.createElement("span");
      titleSpan.className = "plfh-act-name";
      titleSpan.textContent = title;

      const countSpan = document.createElement("span");
      countSpan.className = "plfh-act-count";
      countSpan.textContent = entries.length > 0 ? `0/${entries.length}` : "hole";

      jumpBtn.append(numSpan, titleSpan, countSpan);
      jumpBtn.addEventListener("click", () => {
        actEl.scrollIntoView({ behavior: "smooth", block: "start" });
      });

      actJumpBtns.set(actId, jumpBtn);
      actCountSpans.set(actId, countSpan);
      jumpBar.append(jumpBtn);

      // Inject per-section Check button right below the section heading when it has complete modules.
      const heading = actEl.querySelector("h2, h3");
      if (heading && entries.length > 0) {
        const actBar = document.createElement("div");
        actBar.className = "plfh-act-inline-bar";
        const actBtn = document.createElement("button");
        actBtn.type = "button";
        actBtn.className = "plfh-wasm-btn plfh-wasm-edit";
        actBtn.textContent = `Check Part ${num} (${entries.length} module${entries.length === 1 ? "" : "s"})`;
        actBtn.addEventListener("click", () => runBatch(entries, `Part ${num}`));
        actCheckBtns.push(actBtn);
        actBar.append(actBtn);
        heading.insertAdjacentElement("afterend", actBar);
      }
    }

    mountEl.append(jumpBar);
    updateActProgress();

    // Highlight active section in the sticky bar as the reader scrolls.
    if (typeof IntersectionObserver !== "undefined") {
      const observer = new IntersectionObserver(
        (obsEntries) => {
          for (const oe of obsEntries) {
            if (oe.isIntersecting) {
              const id = oe.target.id;
              for (const [k, b] of actJumpBtns.entries()) {
                b.classList.toggle("plfh-act-jump-btn--active", k === id);
              }
            }
          }
        },
        { rootMargin: "-20% 0px -65% 0px", threshold: 0.01 }
      );
      for (const actEl of acts) observer.observe(actEl);
    }
  }

  checkAllBtn.addEventListener("click", () => {
    runBatch(completeEntries, "all modules");
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

  const uiState = { refinementFits: true, proofSearch: true };
  const standaloneMount = document.getElementById("plfh-standalone-playground");
  if (standaloneMount) {
    mountStandalonePlayground(standaloneMount, client, uiState);
  }
  const chapterMount = document.getElementById("plfh-chapter-playground");
  if (chapterMount && chapterModule) {
    mountChapterBar(chapterMount, client, chapterModule, chapterCtx, uiState);
  }

  const showcaseCardRunners = [];

  blocks.forEach((pre, idx) => {
    const cls = pre.classList;
    if (cls.contains("ignore") || cls.contains("spec")) {
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
    const isShowcaseHole =
      pre.dataset.showcaseHole === "1" || container.dataset.showcaseHole === "1";
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

    const editor = createAgdaEditor({
      initialValue: initialCode,
      rows: Math.max(4, Math.min(24, initialCode.split("\n").length + 1)),
    });
    editor.root.hidden = true;

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

    wrapper.append(bar, editor.root, replRow, holePanel, output);
    container.insertAdjacentElement("afterend", wrapper);

    const setContainerState = (st) => {
      container.classList.remove("plfh-block--ok", "plfh-block--holes", "plfh-block--err");
      if (st) container.classList.add(`plfh-block--${st}`);
    };

    client.onProgress((p) => {
      if (statusSpan.dataset.active !== "1") return;
      const msg = formatProgress(p);
      if (msg) statusSpan.textContent = msg;
    });

    editBtn.addEventListener("click", () => {
      const editing = editor.root.hidden;
      editor.root.hidden = !editing;
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
      setContainerState(null);
    });

    const runCheck = async () => {
      checkBtn.disabled = true;
      holePanel.hidden = true;
      editor.setChecking();
      statusSpan.dataset.active = "1";
      statusSpan.textContent = client.booted
        ? "Checking..."
        : "Starting GHCi Wasm...";
      const rawCode = editor.root.hidden ? initialCode : editor.value;
      const res = await client.checkBlock({
        code: rawCode,
        chapterModule: blockMod,
        chapterPragmas: chapterCtx.chapterPragmas,
        chapterImports: chapterCtx.chapterImports,
        chapterExports: chapterCtx.chapterExports,
        extraGhcArgs: refinementExtraGhcArgs(uiState),
      });
      statusSpan.dataset.active = "0";
      checkBtn.disabled = false;
      output.hidden = false;

      const combined = [res.stderr, res.stdout].filter(Boolean).join("\n");
      const lineOffset = res.lineOffset ?? null;
      if (isFail && expectedCode) {
        if (!res.ok && combined.includes(expectedCode)) {
          statusSpan.textContent = `Rejected as expected (${expectedCode}, ${res.elapsedMs} ms)`;
          output.dataset.state = "ok";
          output.textContent = combined;
          setContainerState("ok");
          editor.setErrors({ errors: parseErrorSpans(combined, lineOffset), lineOffset });
          return true;
        } else if (res.ok) {
          statusSpan.textContent = `Unexpectedly passed (${res.elapsedMs} ms)`;
          output.dataset.state = "warn";
          output.textContent =
            combined || "Module typechecked (was expected to fail with " + expectedCode + ").";
          setContainerState("holes");
          editor.setVerified({ holes: [], lineOffset });
          return false;
        } else {
          statusSpan.textContent = `Failed (${res.elapsedMs} ms)`;
          output.dataset.state = "err";
          output.textContent = combined || res.status;
          setContainerState("err");
          editor.setErrors({ errors: parseErrorSpans(combined, lineOffset), lineOffset });
          return false;
        }
      }

      if (res.ok) {
        replRow.hidden = false;
        statusSpan.textContent = `Checked (${res.elapsedMs} ms)`;
        output.dataset.state = "ok";
        output.textContent =
          [res.stdout, res.stderr].filter(Boolean).join("\n") ||
          "Ok, module typechecked and loaded into GHCi (-XDependentTypes).";
        setContainerState("ok");
        editor.setVerified({
          holes: [],
          lineOffset,
          semanticTokens: res.semanticTokens ?? null,
        });
        return true;
      } else {
        const hasHoles = combined.includes("Found hole:");
        statusSpan.textContent = hasHoles
          ? `Typed hole(s) found (${res.elapsedMs} ms)`
          : `Type error (${res.elapsedMs} ms)`;
        output.dataset.state = hasHoles ? "warn" : "err";
        output.textContent = combined || res.status;
        if (hasHoles) {
          const parsedHoles = parseTypedHoles(combined);
          setContainerState("holes");
          editor.setVerified({ holes: parsedHoles, lineOffset });
          const revealEditor = () => {
            if (editor.root.hidden) {
              editor.root.hidden = false;
              container.hidden = true;
              resetBtn.hidden = false;
              editBtn.textContent = "View Highlighted";
            }
          };
          renderHolePanel(holePanel, combined, {
            code: editor.value,
            lineOffset,
            onFill: (hole, fitExpr) => {
              revealEditor();
              editor.value = applyHoleFit(editor.value, hole, fitExpr, lineOffset);
              editor.focus();
              runCheck();
            },
            onSplit: (hole, split) => {
              revealEditor();
              editor.value = applyCaseSplit(editor.value, hole, split, lineOffset);
              editor.focus();
              runCheck();
            },
          });
        } else {
          setContainerState("err");
          editor.setErrors({
            errors: parseErrorSpans(combined, lineOffset),
            lineOffset,
          });
        }
        return false;
      }
    };

    checkBtn.addEventListener("click", runCheck);
    wireEditorKeys(editor.textarea, runCheck);

    if (!isFail && !isExercise) {
      const actEl = container.closest(".plfh-showcase-act");
      const tabEl = container.closest(".plfh-domain-tab");
      const entry = {
        actId: actEl?.id || "all",
        tabId: tabEl?.id || null,
        isHole: isShowcaseHole,
        passed: false,
        onPassChange: null,
        run: async () => {
          const ok = await runCheck();
          entry.passed = Boolean(ok);
          entry.onPassChange?.();
          return ok;
        },
      };
      // Also update sticky Act progress counter when the user clicks an individual card's Check button.
      checkBtn.removeEventListener("click", runCheck);
      checkBtn.addEventListener("click", () => {
        entry.run();
      });
      showcaseCardRunners.push(entry);
    }

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

function mountDomainTabs(cardEntries) {
  const groups = [...document.querySelectorAll(".plfh-domain-tabs")];
  for (const group of groups) {
    const panels = [...group.querySelectorAll(":scope > .plfh-domain-tab")];
    if (panels.length === 0) continue;

    const tabBar = document.createElement("div");
    tabBar.className = "plfh-tab-bar";
    tabBar.setAttribute("role", "tablist");
    tabBar.setAttribute("aria-label", "Real-world Dependent Haskell examples");

    const buttons = [];
    const btnByPanelId = new Map();

    const activate = (idx, updateHash = false) => {
      const clamped = Math.max(0, Math.min(idx, panels.length - 1));
      panels.forEach((panel, i) => {
        const active = i === clamped;
        panel.hidden = !active;
        buttons[i].setAttribute("aria-selected", active ? "true" : "false");
        buttons[i].tabIndex = active ? 0 : -1;
      });
      if (updateHash && panels[clamped].id) {
        try {
          history.replaceState(null, "", `#${panels[clamped].id}`);
        } catch {}
      }
    };

    panels.forEach((panel, idx) => {
      if (!panel.id) panel.id = `domain-tab-${idx + 1}`;
      panel.setAttribute("role", "tabpanel");
      const label = panel.dataset.tabLabel || panel.querySelector("h3")?.textContent?.trim() || `Example ${idx + 1}`;
      const sub = panel.dataset.tabAudience || "";

      const btn = document.createElement("button");
      btn.type = "button";
      btn.className = "plfh-tab-btn";
      btn.id = `${panel.id}-btn`;
      btn.setAttribute("role", "tab");
      btn.setAttribute("aria-controls", panel.id);
      btn.setAttribute("aria-selected", "false");
      panel.setAttribute("aria-labelledby", btn.id);

      const head = document.createElement("span");
      head.className = "plfh-tab-btn-head";
      const titleSpan = document.createElement("span");
      titleSpan.textContent = label;
      const checkSpan = document.createElement("span");
      checkSpan.className = "plfh-tab-check";
      checkSpan.setAttribute("aria-hidden", "true");
      checkSpan.textContent = "✓";
      head.append(titleSpan, checkSpan);
      btn.append(head);

      if (sub) {
        const subSpan = document.createElement("span");
        subSpan.className = "plfh-tab-sub";
        subSpan.textContent = sub;
        btn.append(subSpan);
      }

      btn.addEventListener("click", () => activate(idx, true));
      btn.addEventListener("keydown", (ev) => {
        if (ev.key === "ArrowRight") {
          ev.preventDefault();
          const next = (idx + 1) % panels.length;
          activate(next, true);
          buttons[next].focus();
        } else if (ev.key === "ArrowLeft") {
          ev.preventDefault();
          const prev = (idx - 1 + panels.length) % panels.length;
          activate(prev, true);
          buttons[prev].focus();
        }
      });

      buttons.push(btn);
      btnByPanelId.set(panel.id, btn);
      tabBar.append(btn);
    });

    group.prepend(tabBar);

    const syncTabChecks = () => {
      for (const panel of panels) {
        const btn = btnByPanelId.get(panel.id);
        if (!btn) continue;
        const panelEntries = cardEntries.filter((e) => e.tabId === panel.id);
        const allPassed = panelEntries.length > 0 && panelEntries.every((e) => e.passed);
        btn.dataset.passed = allPassed ? "1" : "0";
      }
    };

    for (const entry of cardEntries) {
      if (entry.tabId && btnByPanelId.has(entry.tabId)) {
        const prevCb = entry.onPassChange;
        entry.onPassChange = () => {
          prevCb?.();
          syncTabChecks();
        };
      }
    }

    const hashId = window.location.hash ? window.location.hash.slice(1) : "";
    let initialIdx = 0;
    if (hashId) {
      const targetEl = document.getElementById(hashId);
      const targetPanel = targetEl?.closest(".plfh-domain-tab");
      const found = targetPanel ? panels.indexOf(targetPanel) : -1;
      if (found >= 0) initialIdx = found;
    }
    activate(initialIdx, false);
    window.addEventListener("hashchange", () => {
      const h = window.location.hash ? window.location.hash.slice(1) : "";
      if (!h) return;
      const el = document.getElementById(h);
      const p = el?.closest(".plfh-domain-tab");
      const found = p ? panels.indexOf(p) : -1;
      if (found >= 0) activate(found, false);
    });
  }
}

  const showcaseMount = document.getElementById("plfh-showcase-bar");
  if (showcaseMount && showcaseCardRunners.length > 0) {
    mountShowcaseBar(showcaseMount, client, uiState, showcaseCardRunners);
  }
  mountDomainTabs(showcaseCardRunners);

  return client;
}
