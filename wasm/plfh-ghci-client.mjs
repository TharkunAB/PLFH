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

// Wave 6B enables fast pruned refinement hole fits by default under -XDependentTypes.
// Only pass an override flag when the user explicitly unchecks refinement fits.
function refinementExtraGhcArgs(refinementEnabled) {
  return refinementEnabled ? "" : "-fmax-refinement-hole-fits=0";
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
      code: scratchEditor.value,
      chapterModule,
      chapterPragmas: ctx.chapterPragmas,
      chapterImports: ctx.chapterImports,
      chapterExports: ctx.chapterExports,
      extraGhcArgs: refinementExtraGhcArgs(uiState.refinementFits),
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
      const lineOffset = res.lineOffset ?? null;
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
    label: "Agda-mode Case Split & Holes",
    replHint: ":t plusAssoc",
    code: `{-# LANGUAGE DependentTypes #-}
module Playground where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..), plus)
import PLFH.Part1.Induction (cong)

-- Interactive Agda-mode proof in 3 clicks:
-- 1. Click "Check & Load in GHCi" -> GHC suggests splitting on \`m\`.
-- 2. Click "Split on m (Zero | Succ)" -> GHC generates both cases.
-- 3. Click \`Refl\`, then \`cong Succ (plusAssoc m n p)\` (or refine via \`cong Succ _\`)!
plusAssoc :: foreach (m n p :: Nat)
          -> plus (plus m n) p :~: plus m (plus n p)
plusAssoc m n p = _
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
    "Enable Dependent Haskell refinement hole fits & subgoal splitting (on by default under -XDependentTypes)";
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
      code: editor.value,
      chapterModule: null,
      extraGhcArgs: refinementExtraGhcArgs(uiState.refinementFits),
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
      const lineOffset = res.lineOffset ?? null;
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

  const uiState = { refinementFits: true };
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
        code: rawCode,
        chapterModule: blockMod,
        chapterPragmas: chapterCtx.chapterPragmas,
        chapterImports: chapterCtx.chapterImports,
        chapterExports: chapterCtx.chapterExports,
        extraGhcArgs: refinementExtraGhcArgs(uiState.refinementFits),
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
          const lineOffset = res.lineOffset ?? null;
          const revealEditor = () => {
            if (editor.hidden) {
              editor.hidden = false;
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
