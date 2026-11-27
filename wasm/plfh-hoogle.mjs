// Lightweight client-side Hoogle search for the PLFH dependent-base Reference page.
// Indexes every exported declaration directly from the rendered Haskell signature
// blocks on /dependent-base/ so the search index can never drift from the docs.

const PROMOTED_RIGID = new Set([
  "plus",
  "mul",
  "minus",
  "minNat",
  "maxNat",
  "minSize",
  "eqNat",
  "eqSize",
  "compareNat",
  "size",
  "lengthNat",
  "append",
  "map",
  "foldr",
  "zip",
  "zipWith",
  "reverse",
  "shunt",
  "reverseShunt",
  "takeSize",
  "appendVec",
  "first",
  "second",
  "fst",
  "snd",
  "swap",
  "not",
  "bool",
  "maybe",
  "fromMaybe",
  "isJust",
  "isNothing",
  "fmapMaybe",
  "maybeToList",
  "listToMaybe",
  "either",
  "isLeft",
  "isRight",
  "mapLeft",
  "mapRight",
  "swapEither",
  "assocEitherTo",
  "assocEitherFrom",
  "id",
  "const",
  "flip",
  "on",
]);

const KEYWORDS = new Set([
  "forall",
  "foreach",
  "some",
  "exists",
  "type",
  "data",
  "class",
  "where",
  "pattern",
  "infix",
  "infixl",
  "infixr",
]);

// Split a string by a top-level delimiter (outside parens/brackets/braces).
function splitTopLevel(str, delim) {
  const parts = [];
  let depth = 0;
  let cur = "";
  for (let i = 0; i < str.length; i++) {
    const ch = str[i];
    if (ch === "(" || ch === "[" || ch === "{") depth++;
    else if (ch === ")" || ch === "]" || ch === "}") depth = Math.max(0, depth - 1);
    if (depth === 0 && str.startsWith(delim, i)) {
      parts.push(cur.trim());
      cur = "";
      i += delim.length - 1;
      continue;
    }
    cur += ch;
  }
  if (cur.trim()) parts.push(cur.trim());
  return parts;
}

// Strip a balanced outer pair of parentheses if they wrap the entire expression.
function stripOuterParens(s) {
  let str = s.trim();
  while (str.startsWith("(") && str.endsWith(")")) {
    let depth = 0;
    let wrapsAll = true;
    for (let i = 0; i < str.length; i++) {
      if (str[i] === "(") depth++;
      else if (str[i] === ")") depth--;
      if (depth === 0 && i < str.length - 1) {
        wrapsAll = false;
        break;
      }
    }
    if (!wrapsAll) break;
    str = str.slice(1, -1).trim();
  }
  return str;
}

// Strip inline Haskell `--` comments while preserving code.
function stripLineComment(line) {
  const idx = line.indexOf("--");
  return idx === -1 ? line : line.slice(0, idx);
}

// Parse all declarations from the /dependent-base/ page DOM.
export function buildIndexFromDom(root = document) {
  const entries = [];
  const headings = [...root.querySelectorAll("h3[id]")];

  for (const h3 of headings) {
    const anchorId = h3.id;
    const moduleName = (h3.querySelector("code")?.textContent || h3.textContent || "").trim();
    if (!moduleName || moduleName === "Prelude.Dependent") continue;

    // Scan siblings until the next h3 or h2 to find source link + Haskell pre block.
    let sourceHref = "";
    let preEl = null;
    let el = h3.nextElementSibling;
    while (el && !/^H[23]$/.test(el.tagName)) {
      if (!sourceHref) {
        const srcLink = el.querySelector('a[href*="/source/"], a[href*="source/"]');
        if (srcLink) sourceHref = srcLink.getAttribute("href") || "";
      }
      if (!preEl) {
        preEl = el.matches("pre.sourceCode.haskell")
          ? el
          : el.querySelector("pre.sourceCode.haskell");
      }
      el = el.nextElementSibling;
    }
    if (!preEl) continue;

    const rawLines = preEl.textContent.split("\n");
    const blocks = [];
    let cur = null;
    for (const rawLine of rawLines) {
      const cleaned = stripLineComment(rawLine).replace(/\s+$/, "");
      if (!cleaned.trim()) {
        if (cur) {
          blocks.push(cur);
          cur = null;
        }
        continue;
      }
      if (/^infix[lr]?\b/.test(cleaned)) {
        if (cur) {
          blocks.push(cur);
          cur = null;
        }
        continue;
      }
      if (/^\s/.test(cleaned) && cur) {
        cur.lines.push(cleaned);
      } else {
        if (cur) blocks.push(cur);
        cur = { lines: [cleaned] };
      }
    }
    if (cur) blocks.push(cur);

    for (const blk of blocks) {
      const first = blk.lines[0].trim();
      const fullText = blk.lines.map((l) => l.trim()).join(" ").replace(/\s+/g, " ");

      // 1. GADT `data ... where` or `class ... where`
      if (/^(data|class)\b/.test(first) && /\bwhere\s*$/.test(first)) {
        const kind = first.startsWith("class") ? "class" : "data";
        const header = first.replace(/\s*where\s*$/, "").trim();
        const name = extractDeclHeadName(header);
        if (name) {
          entries.push(makeEntry(name, kind, header, moduleName, anchorId, sourceHref));
        }
        // Parse indented constructor/method declarations
        const members = joinIndentedDecls(blk.lines.slice(1));
        for (const mem of members) {
          const m = mem.match(/^([A-Za-z_][A-Za-z0-9_']*|\([^)]+\))\s*::\s*(.+)$/);
          if (m) {
            entries.push(
              makeEntry(
                m[1].trim(),
                kind === "class" ? "method" : "ctor",
                `${m[1].trim()} :: ${m[2].trim()}`,
                moduleName,
                anchorId,
                sourceHref
              )
            );
          }
        }
        continue;
      }

      // 2. ADT `data Foo a = Con1 ... | Con2 ...` or empty `data Void`
      if (/^data\s+/.test(first)) {
        const eqIdx = fullText.indexOf("=");
        const lhs = (eqIdx === -1 ? fullText : fullText.slice(0, eqIdx)).trim();
        const typeName = extractDeclHeadName(lhs);
        if (typeName) {
          entries.push(makeEntry(typeName, "data", fullText, moduleName, anchorId, sourceHref));
        }
        if (eqIdx !== -1) {
          const resType = lhs.replace(/^data\s+/, "").trim();
          const rhs = fullText.slice(eqIdx + 1).trim();
          for (const alt of splitTopLevel(rhs, "|")) {
            const toks = splitConArgs(alt);
            if (toks.length > 0) {
              const conName = toks[0];
              const argTypes = toks.slice(1);
              const conSig =
                argTypes.length > 0
                  ? `${conName} :: ${argTypes.join(" -> ")} -> ${resType}`
                  : `${conName} :: ${resType}`;
              entries.push(makeEntry(conName, "ctor", conSig, moduleName, anchorId, sourceHref));
            }
          }
        }
        continue;
      }

      // 3. `type ... = ...` or standalone kind signature `type Foo :: ...`
      if (/^type\s+/.test(first)) {
        const name = extractTypeDeclName(fullText);
        if (name) {
          const existing = entries.find(
            (e) => e.name === name && e.moduleName === moduleName && e.kind === "type"
          );
          if (existing) {
            existing.sig = `${existing.sig}; ${fullText}`;
            existing.parsed = parseTypeSignature(existing.sig);
          } else {
            entries.push(makeEntry(name, "type", fullText, moduleName, anchorId, sourceHref));
          }
        }
        continue;
      }

      // 4. `pattern Pack`
      if (/^pattern\s+/.test(first)) {
        const m = first.match(/^pattern\s+([A-Za-z_][A-Za-z0-9_']*)/);
        if (m) {
          entries.push(makeEntry(m[1], "pattern", fullText, moduleName, anchorId, sourceHref));
        }
        continue;
      }

      // 5. Value/function signature `name :: Type`
      const sigMatch = fullText.match(/^([a-z_][A-Za-z0-9_']*|\([^)]+\))\s*::\s*(.+)$/);
      if (sigMatch) {
        const name = sigMatch[1].trim();
        const sig = `${name} :: ${sigMatch[2].trim()}`;
        entries.push(makeEntry(name, "fn", sig, moduleName, anchorId, sourceHref));
      }
    }
  }

  return entries;
}

function joinIndentedDecls(lines) {
  const out = [];
  let cur = "";
  for (const raw of lines) {
    const t = raw.trim();
    if (!t) continue;
    if (/^([A-Za-z_][A-Za-z0-9_']*|\([^)]+\))\s*::/.test(t)) {
      if (cur) out.push(cur);
      cur = t;
    } else if (cur) {
      cur += " " + t;
    }
  }
  if (cur) out.push(cur);
  return out;
}

function splitConArgs(alt) {
  const res = [];
  let depth = 0;
  let cur = "";
  for (let i = 0; i < alt.length; i++) {
    const ch = alt[i];
    if (ch === "(" || ch === "[" || ch === "{") depth++;
    else if (ch === ")" || ch === "]" || ch === "}") depth = Math.max(0, depth - 1);
    if (depth === 0 && /\s/.test(ch)) {
      if (cur) {
        res.push(cur);
        cur = "";
      }
    } else {
      cur += ch;
    }
  }
  if (cur) res.push(cur);
  return res;
}

function extractDeclHeadName(header) {
  const body = header.replace(/^(data|class)\s+/, "").trim();
  // Infix data declaration like `(a :: k) :~: (b :: k)` or `c /\ a`
  const infixOp = body.match(/^\([^)]+\)\s*([:!#$%&*+./<=>?@\\^|~-]+)\s*\(/);
  if (infixOp) return `(${infixOp[1]})`;
  const infixSimple = body.match(/^[a-z_][A-Za-z0-9_']*\s+([:!#$%&*+./<=>?@\\^|~-]+)\s+[a-z_]/);
  if (infixSimple) return `(${infixSimple[1]})`;
  const m = body.match(/^(\([^)]+\)|[A-Z][A-Za-z0-9_']*)/);
  return m ? m[1] : null;
}

function extractTypeDeclName(fullText) {
  const body = fullText.replace(/^type\s+/, "").trim();
  const infix = body.match(/^\([^)]+\)\s*([:!#$%&*+./<=>?@\\^|~-]+)\s*\(/);
  if (infix) return `(${infix[1]})`;
  const m = body.match(/^(\([^)]+\)|[A-Z][A-Za-z0-9_']*)/);
  return m ? m[1] : null;
}

// Tokenize a Haskell type expression.
function tokenizeType(str) {
  const tokens = [];
  const re =
    /->|=>|:~~:|:~:|\+\+|\/\\|&&|\|\||===|::|'(?=\[|\()|[()[\]{},|]|%[A-Za-z0-9_]+|GHC\.[A-Za-z0-9_.]+|[A-Za-z_][A-Za-z0-9_']*|[!#$%&*+./<=>?@\\^|~:-]+/g;
  let m;
  while ((m = re.exec(str)) !== null) {
    let t = m[0];
    if (t === "'") continue; // ignore promotion tick in '[x] or '(a, b)
    if (t.startsWith("GHC.TypeNats.")) t = t.slice("GHC.TypeNats.".length);
    tokens.push(t);
  }
  return tokens;
}

function isRigidToken(tok) {
  if (/^[A-Z]/.test(tok)) return true;
  if (PROMOTED_RIGID.has(tok)) return true;
  if (
    [":~:", ":~~:", "++", "+", "/\\", "&&", "||", "->", "=>", "|", "[", "]", "(", ")", ","].includes(
      tok
    )
  ) {
    return true;
  }
  return false;
}

// Extract normalized arrow segments from a signature RHS.
function parseTypeSignature(sigOrQuery) {
  let body = sigOrQuery.trim();
  const dcolon = splitTopLevel(body, "::");
  if (dcolon.length >= 2 && !/^(\(|forall|foreach|some|exists|type|data|class)/.test(dcolon[0])) {
    body = dcolon.slice(1).join(" :: ").trim();
  } else if (/^type\s+/.test(body) && body.includes("=")) {
    body = body.slice(body.indexOf("=") + 1).trim();
  }

  // Strip invisible `forall ... .` chunks anywhere at top-level prefixes.
  const args = [];
  const constraints = [];

  function peelSegment(seg) {
    let s = stripOuterParens(seg);
    // Repeatedly strip invisible `forall ... .`
    while (/^forall\b/.test(s)) {
      let depth = 0;
      let dotIdx = -1;
      for (let i = 6; i < s.length; i++) {
        const ch = s[i];
        if (ch === "(" || ch === "{" || ch === "[") depth++;
        else if (ch === ")" || ch === "}" || ch === "]") depth = Math.max(0, depth - 1);
        else if (depth === 0 && ch === ".") {
          dotIdx = i;
          break;
        } else if (depth === 0 && s.startsWith("->", i)) {
          // Visible forall: handled below as an arrow segment!
          return s;
        }
      }
      if (dotIdx !== -1) {
        s = s.slice(dotIdx + 1).trim();
      } else {
        break;
      }
    }
    return s;
  }

  // Split top-level `->` first.
  const arrowParts = splitTopLevel(body, "->");
  const rawSteps = [];
  for (let i = 0; i < arrowParts.length; i++) {
    let seg = peelSegment(arrowParts[i]);
    // Split any top-level `=>` constraints inside this segment.
    const cParts = splitTopLevel(seg, "=>");
    if (cParts.length > 1) {
      for (let c = 0; c < cParts.length - 1; c++) {
        constraints.push(peelSegment(cParts[c]));
      }
      seg = peelSegment(cParts[cParts.length - 1]);
    }
    // Handle `foreach (x y :: T)` or visible `forall (f :: T)` binder groups.
    const quantMatch = seg.match(/^(foreach|forall)\s+(.+)$/);
    if (quantMatch && i < arrowParts.length - 1) {
      const binderGroup = quantMatch[2].trim();
      const groupMatches = [...binderGroup.matchAll(/\(([^()]+?)\s*::\s*([^()]+)\)/g)];
      if (groupMatches.length > 0) {
        for (const gm of groupMatches) {
          const names = gm[1].trim().split(/\s+/).filter(Boolean);
          const ty = gm[2].trim();
          for (let k = 0; k < names.length; k++) {
            rawSteps.push(ty);
          }
        }
      } else {
        // Fallback: extract type after `::`
        const col = splitTopLevel(stripOuterParens(binderGroup), "::");
        if (col.length >= 2) {
          rawSteps.push(col.slice(1).join(" :: ").trim());
        } else {
          rawSteps.push(binderGroup);
        }
      }
    } else if (seg) {
      rawSteps.push(seg);
    }
  }

  // Canonicalize variables across the entire signature (and locally per part) for alpha-equivalence!
  const varMap = new Map();
  const canonicalize = (exprStr) => {
    const toks = tokenizeType(exprStr).filter(
      (t) => !t.startsWith("%") && !KEYWORDS.has(t) && t !== "{" && t !== "}"
    );
    const localVarMap = new Map();
    const normToks = [];
    const localToks = [];
    const rigids = [];
    for (let i = 0; i < toks.length; i++) {
      let t = toks[i];
      if (t === "List") {
        // Normalize `List a` closely with `[a]`
        rigids.push("[]");
        normToks.push("[]");
        localToks.push("[]");
        continue;
      }
      if (t === "[" && toks[i + 1] === "]") {
        rigids.push("[]");
        normToks.push("[]");
        localToks.push("[]");
        i++;
        continue;
      }
      if (t === "[") {
        rigids.push("[]");
        normToks.push("[");
        localToks.push("[");
        continue;
      }
      if (t === "+") {
        rigids.push("plus");
        normToks.push("plus");
        localToks.push("plus");
        continue;
      }
      if (isRigidToken(t)) {
        if (!["(", ")", "[", "]", ",", "|", "->"].includes(t)) {
          rigids.push(t);
        }
        normToks.push(t);
        localToks.push(t);
      } else if (/^[a-z_][A-Za-z0-9_']*$/.test(t)) {
        if (!varMap.has(t)) varMap.set(t, `$${varMap.size}`);
        if (!localVarMap.has(t)) localVarMap.set(t, `$${localVarMap.size}`);
        normToks.push(varMap.get(t));
        localToks.push(localVarMap.get(t));
      } else {
        rigids.push(t);
        normToks.push(t);
        localToks.push(t);
      }
    }
    return {
      raw: exprStr,
      norm: normToks.join(" "),
      localNorm: localToks.join(" "),
      tokCount: localToks.length,
      rigids,
      rigidSet: new Set(rigids),
      isVarOnly: rigids.length === 0,
    };
  };

  const normSteps = rawSteps.map(canonicalize);
  const normConstraints = constraints.map(canonicalize);
  const ret = normSteps.length > 0 ? normSteps[normSteps.length - 1] : canonicalize("");
  const argList = normSteps.length > 1 ? normSteps.slice(0, -1) : [];

  const allRigids = new Set();
  for (const s of [...argList, ret, ...normConstraints]) {
    for (const r of s.rigids) allRigids.add(r);
  }

  return {
    args: argList,
    ret,
    constraints: normConstraints,
    allRigids,
    fullNorm: [...argList.map((a) => a.norm), ret.norm].join(" -> "),
    rawLower: sigOrQuery.toLowerCase(),
  };
}

function makeEntry(name, kind, sig, moduleName, anchorId, sourceHref) {
  return {
    name,
    nameLower: name.toLowerCase(),
    bareName: name.replace(/^\(|\)$/g, "").toLowerCase(),
    kind,
    sig,
    moduleName,
    moduleLower: moduleName.toLowerCase(),
    anchorId,
    sourceHref,
    parsed: parseTypeSignature(sig),
  };
}

function isTypeQuery(q) {
  if (/->|:~:|:~~:|=>|::|\b(foreach|forall|some|exists)\b|\|/.test(q)) return true;
  if (/[[\]()]/.test(q) && q.trim().includes(" ")) return true;
  // Multiple tokens starting with a capitalized type constructor like `Vec a n` or `Maybe a`
  const words = q.trim().split(/\s+/);
  if (words.length >= 2 && /^[A-Z[]/.test(words[0])) return true;
  return false;
}

function multisetOverlap(aArr, bArr) {
  const counts = new Map();
  for (const x of bArr) counts.set(x, (counts.get(x) || 0) + 1);
  let hits = 0;
  for (const x of aArr) {
    const c = counts.get(x) || 0;
    if (c > 0) {
      hits++;
      counts.set(x, c - 1);
    }
  }
  return hits;
}

function scorePartMatch(qPart, ePart) {
  if (qPart.norm === ePart.norm) return 1.0;
  if (qPart.localNorm === ePart.localNorm) return 0.96;
  if (qPart.rigids.length > 0) {
    const hits = multisetOverlap(qPart.rigids, ePart.rigids);
    if (hits === 0) return 0;
    const recall = hits / qPart.rigids.length;
    const precision = hits / Math.max(1, ePart.rigids.length);
    const lenRatio =
      Math.min(qPart.tokCount, ePart.tokCount) / Math.max(1, Math.max(qPart.tokCount, ePart.tokCount));
    return 0.72 * recall * (0.45 + 0.35 * precision + 0.2 * lenRatio);
  }
  // Query part is a bare type variable (`a`, `b`): matches any type, prefers bare var!
  return ePart.isVarOnly ? 0.92 : 0.45;
}

export function searchEntries(entries, rawQuery) {
  const q = rawQuery.trim();
  if (!q) return [];

  // Optional module filter: `+Data.Vec` or `module:Vec`
  let modFilter = "";
  let cleanQ = q;
  const modMatch = q.match(/(?:^|\s)(?:\+|module:)([A-Za-z0-9_.]+)/);
  if (modMatch) {
    modFilter = modMatch[1].toLowerCase();
    cleanQ = q.replace(modMatch[0], " ").trim();
  }

  const pool = modFilter
    ? entries.filter((e) => e.moduleLower.includes(modFilter))
    : entries;

  if (!cleanQ) {
    return pool.map((entry) => ({ entry, score: 100 }));
  }

  const typeMode = isTypeQuery(cleanQ);
  const qLower = cleanQ.toLowerCase();
  const qBare = qLower.replace(/^\(|\)$/g, "");
  const qParsed = typeMode ? parseTypeSignature(cleanQ) : null;
  const qTerms = cleanQ.split(/\s+/).filter(Boolean);

  const scored = [];

  for (const entry of pool) {
    let score = 0;

    if (typeMode && qParsed) {
      const ep = entry.parsed;

      // Exact alpha-equivalent full signature match!
      if (qParsed.fullNorm === ep.fullNorm) {
        score = 1000;
      } else {
        // 1. Return type alignment
        const retScore = scorePartMatch(qParsed.ret, ep.ret);
        let argScoreSum = 0;
        let inOrderHits = 0;
        const used = new Set();
        let lastIdx = -1;

        for (const qa of qParsed.args) {
          let best = 0;
          let bestIdx = -1;
          for (let j = 0; j < ep.args.length; j++) {
            if (used.has(j)) continue;
            const s = scorePartMatch(qa, ep.args[j]);
            const orderBonus = j > lastIdx ? 0.03 : 0;
            if (s + orderBonus > best) {
              best = s + orderBonus;
              bestIdx = j;
            }
          }
          if (bestIdx !== -1 && best > 0.25) {
            used.add(bestIdx);
            if (bestIdx > lastIdx) inOrderHits++;
            lastIdx = bestIdx;
            argScoreSum += Math.min(1, best);
          }
        }

        // Check rigid constructor coverage across the entire signature
        const qAllRigids = [...qParsed.allRigids];
        const eAllRigids = [...ep.allRigids];
        const rigidHits = multisetOverlap(qAllRigids, eAllRigids);
        const rigidCoverage =
          qAllRigids.length > 0 ? rigidHits / qAllRigids.length : 1;

        // Require meaningful match when rigid constructors were requested
        if (qAllRigids.length > 0 && rigidHits === 0) {
          // Also allow exact substring match for keyword queries like `exists` or `some`
          if (ep.rawLower.includes(qLower)) {
            score = 220;
          }
        } else {
          const argRatio =
            qParsed.args.length > 0 ? argScoreSum / qParsed.args.length : 1;
          const arityDiff = Math.abs(ep.args.length - qParsed.args.length);

          if (qParsed.args.length === 0) {
            // Single-type query like `Vec a n` or `exists`
            const directHit =
              retScore > 0.65 ||
              ep.args.some((a) => scorePartMatch(qParsed.ret, a) > 0.65) ||
              ep.rawLower.includes(qLower);
            if (directHit) {
              score = 320 * rigidCoverage + 280 * retScore + (ep.rawLower.includes(qLower) ? 120 : 0);
            }
          } else if (retScore > 0.25 && argRatio > 0.35 && rigidCoverage >= 0.5) {
            score =
              340 * retScore +
              380 * argRatio +
              140 * rigidCoverage +
              (inOrderHits === qParsed.args.length ? 45 : 0) -
              arityDiff * 24;
          }
        }
      }

      // Small tie-breaker favoring functions/constructors over raw type synonyms for arrow queries
      if (score > 0 && qParsed.args.length > 0 && (entry.kind === "fn" || entry.kind === "ctor")) {
        score += 12;
      }
      if (score < 160) continue;
    } else {
      // Name, module, and bare-type search
      if (entry.nameLower === qLower || entry.bareName === qBare) {
        score = 1000;
      } else if (entry.nameLower.startsWith(qLower) || entry.bareName.startsWith(qBare)) {
        score = 820 - Math.min(80, entry.name.length - q.length);
      } else if (entry.nameLower.includes(qLower) || entry.bareName.includes(qBare)) {
        score = 620;
      } else if (entry.moduleLower.includes(qLower)) {
        score = 440;
      } else if (
        qTerms.length > 1 &&
        qTerms.every(
          (t) =>
            entry.nameLower.includes(t.toLowerCase()) ||
            entry.parsed.rawLower.includes(t.toLowerCase()) ||
            entry.moduleLower.includes(t.toLowerCase())
        )
      ) {
        score = 380;
      } else if (entry.parsed.allRigids.has(cleanQ)) {
        score = 340;
      } else if (entry.parsed.rawLower.includes(qLower)) {
        score = 260;
      } else if (isSubsequence(qBare, entry.bareName)) {
        score = 200;
      } else {
        continue;
      }
    }

    scored.push({ entry, score });
  }

  scored.sort((a, b) => b.score - a.score || a.entry.name.length - b.entry.name.length || a.entry.name.localeCompare(b.entry.name));
  return scored;
}

function isSubsequence(needle, haystack) {
  if (needle.length < 2) return false;
  let i = 0;
  for (let j = 0; j < haystack.length && i < needle.length; j++) {
    if (needle[i] === haystack[j]) i++;
  }
  return i === needle.length;
}

const EXAMPLE_QUERIES = [
  "Fin n -> Vec a n -> a",
  "a :~: b -> b :~: a",
  "Vec a n -> [a]",
  "Nat -> Nat -> Nat",
  "Dec p -> Bool",
  "cong",
];

function mountHoogle(mountEl) {
  const entries = buildIndexFromDom(document);
  mountEl.innerHTML = "";
  mountEl.className = "plfh-hoogle";

  const header = document.createElement("div");
  header.className = "plfh-hoogle-header";
  header.innerHTML =
    `<strong>Search <code>dependent-base</code></strong>` +
    `<span class="plfh-hoogle-meta">${entries.length} indexed symbols &middot; search by name or Dependent Haskell type (press <kbd>/</kbd>)</span>`;

  const row = document.createElement("div");
  row.className = "plfh-hoogle-row";

  const input = document.createElement("input");
  input.type = "search";
  input.className = "plfh-hoogle-input";
  input.placeholder = "Try: Fin n -> Vec a n -> a, a :~: b -> b :~: a, lookupVec, +Data.Nat ...";
  input.setAttribute("aria-label", "Search dependent-base by name or type");
  input.autocomplete = "off";
  input.spellcheck = false;

  const clearBtn = document.createElement("button");
  clearBtn.type = "button";
  clearBtn.className = "plfh-hoogle-clear";
  clearBtn.textContent = "Clear";
  clearBtn.hidden = true;

  row.append(input, clearBtn);

  const chips = document.createElement("div");
  chips.className = "plfh-hoogle-chips";
  for (const ex of EXAMPLE_QUERIES) {
    const btn = document.createElement("button");
    btn.type = "button";
    btn.className = "plfh-hoogle-chip";
    btn.textContent = ex;
    btn.addEventListener("click", () => {
      input.value = ex;
      render(ex);
      input.focus();
    });
    chips.append(btn);
  }

  const resultsBox = document.createElement("div");
  resultsBox.className = "plfh-hoogle-results";
  resultsBox.hidden = true;

  mountEl.append(header, row, chips, resultsBox);

  let showLimit = 15;

  function render(query) {
    const q = query.trim();
    clearBtn.hidden = q.length === 0;
    if (!q) {
      resultsBox.hidden = true;
      resultsBox.innerHTML = "";
      return;
    }

    const matches = searchEntries(entries, q);
    resultsBox.hidden = false;
    resultsBox.innerHTML = "";

    const summary = document.createElement("div");
    summary.className = "plfh-hoogle-summary";
    const modeLabel = isTypeQuery(q.replace(/(?:^|\s)(?:\+|module:)[A-Za-z0-9_.]+/, "").trim())
      ? "type search"
      : "name & symbol search";
    summary.textContent =
      matches.length === 0
        ? `No matches for "${q}" (${modeLabel}).`
        : `${matches.length} match${matches.length === 1 ? "" : "es"} (${modeLabel})`;
    resultsBox.append(summary);

    if (matches.length === 0) return;

    const list = document.createElement("ul");
    list.className = "plfh-hoogle-list";

    const visible = matches.slice(0, showLimit);
    for (const { entry } of visible) {
      const li = document.createElement("li");
      li.className = "plfh-hoogle-item";

      const top = document.createElement("div");
      top.className = "plfh-hoogle-item-top";

      const sigCode = document.createElement("code");
      sigCode.className = "plfh-hoogle-sig";
      sigCode.textContent = entry.sig;

      const meta = document.createElement("span");
      meta.className = "plfh-hoogle-item-links";

      const modLink = document.createElement("a");
      modLink.className = "plfh-hoogle-mod";
      modLink.href = `#${entry.anchorId}`;
      modLink.textContent = entry.moduleName;
      modLink.addEventListener("click", () => {
        const targetHeading = document.getElementById(entry.anchorId);
        if (targetHeading) {
          targetHeading.classList.remove("plfh-hoogle-flash");
          void targetHeading.offsetWidth;
          targetHeading.classList.add("plfh-hoogle-flash");
        }
      });
      meta.append(modLink);

      if (entry.sourceHref) {
        const srcLink = document.createElement("a");
        srcLink.className = "plfh-hoogle-src";
        srcLink.href = entry.sourceHref;
        srcLink.textContent = "source";
        meta.append(srcLink);
      }

      top.append(sigCode, meta);
      li.append(top);
      list.append(li);
    }

    resultsBox.append(list);

    if (matches.length > showLimit) {
      const moreBtn = document.createElement("button");
      moreBtn.type = "button";
      moreBtn.className = "plfh-hoogle-more";
      moreBtn.textContent = `Show all ${matches.length} matches`;
      moreBtn.addEventListener("click", () => {
        showLimit = matches.length;
        render(input.value);
      });
      resultsBox.append(moreBtn);
    }
  }

  input.addEventListener("input", () => {
    showLimit = 15;
    render(input.value);
  });

  clearBtn.addEventListener("click", () => {
    input.value = "";
    showLimit = 15;
    render("");
    input.focus();
  });

  input.addEventListener("keydown", (ev) => {
    if (ev.key === "Escape") {
      input.value = "";
      render("");
      input.blur();
    }
  });

  document.addEventListener("keydown", (ev) => {
    if (
      ev.key === "/" &&
      !ev.ctrlKey &&
      !ev.metaKey &&
      !ev.altKey &&
      document.activeElement?.tagName !== "INPUT" &&
      document.activeElement?.tagName !== "TEXTAREA"
    ) {
      ev.preventDefault();
      input.focus();
      input.select();
    }
  });

  // Support deep links like /dependent-base/?q=Fin+n+->+Vec+a+n+->+a
  const initialQ = new URLSearchParams(window.location.search).get("q");
  if (initialQ) {
    input.value = initialQ;
    render(initialQ);
  }
}

if (typeof document !== "undefined") {
  const boot = () => {
    const mount = document.getElementById("plfh-depbase-hoogle");
    if (mount) mountHoogle(mount);
  };
  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", boot);
  } else {
    boot();
  }
}
