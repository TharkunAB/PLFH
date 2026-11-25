// Dedicated Web Worker for client-side Dependent Haskell GHCi in PLFH.
// Runs entirely in the browser with zero server backend (no SharedArrayBuffer required).

import { Directory, File, PreopenDirectory } from "./browser_wasi_shim.mjs";
import { DyLDBrowserHost, main as dyldMain } from "./dyld.mjs";

const CACHE_NAME = "plfh-wasm-rootfs-v1";

let runCmd = null;
let hsSearchDir = null;
let currentChapter = null;
let interactiveMode = false;
const defaultFlags =
  "-package-env - -package plfh-book -fno-ignore-interface-pragmas -i/tmp/work -outputdir /tmp/out";
const replFlags = `-XDependentTypes ${defaultFlags}`;

const stdoutLines = [];
const stderrLines = [];

function drainOutput() {
  const out = stdoutLines.splice(0, stdoutLines.length).join("\n");
  const err = stderrLines.splice(0, stderrLines.length).join("\n");
  return { stdout: out, stderr: err };
}

function decodeCString(bytes) {
  let end = bytes.indexOf(0);
  if (end === -1) end = bytes.length;
  return new TextDecoder("utf-8").decode(bytes.subarray(0, end));
}

function parseOctal(bytes) {
  const s = decodeCString(bytes).trim();
  return s ? Number.parseInt(s, 8) : 0;
}

function insertEntry(rootMap, rawPath, isDir, fileBytes) {
  const parts = rawPath
    .replace(/^\.?\//, "")
    .split("/")
    .filter((p) => p.length > 0 && p !== ".");
  if (parts.length === 0) return;

  let curMap = rootMap;
  const dirCount = isDir ? parts.length : parts.length - 1;
  for (let i = 0; i < dirCount; i++) {
    const seg = parts[i];
    let next = curMap.get(seg);
    if (!next || !(next instanceof Directory)) {
      next = new Directory([]);
      curMap.set(seg, next);
    }
    curMap = next.contents;
  }

  if (!isDir) {
    const leaf = parts[parts.length - 1];
    curMap.set(leaf, new File(fileBytes, { readonly: false }));
    if (
      leaf.startsWith("libHSrts") &&
      leaf.endsWith(".so") &&
      rawPath.includes("hslib/lib/")
    ) {
      hsSearchDir = "/" + parts.slice(0, parts.length - 1).join("/");
    }
  }
}

async function fetchRootfsResponse(rootfsUrl, onProgress) {
  let cache = null;
  try {
    if (typeof caches !== "undefined") {
      cache = await caches.open(CACHE_NAME);
      const cached = await cache.match(rootfsUrl);
      if (cached && cached.ok && cached.body) {
        onProgress?.({ phase: "cache", loadedBytes: 0, totalBytes: 0 });
        return { response: cached, fromCache: true };
      }
    }
  } catch {
    // Cache API unavailable (e.g. opaque origin or restricted browsing mode).
  }

  const resp = await fetch(rootfsUrl);
  if (!resp.ok) {
    if (resp.status === 404) {
      throw new Error(
        `The wasm32-wasi Dependent GHC bundle (${rootfsUrl}) is not yet published (HTTP 404).\n` +
          "The interactive editor works now; once the first wasm32-wasi rootfs.tar.gz artifact is uploaded, " +
          "clicking Check will typecheck and run Dependent Haskell 10.1 directly in your browser.\n" +
          "See Setup for staging a local bundle."
      );
    }
    throw new Error(`Failed to fetch ${rootfsUrl}: HTTP ${resp.status}`);
  }

  if (cache) {
    try {
      // Prune superseded rootfs versions so browser storage stays bounded to one bundle.
      cache
        .keys()
        .then((keys) => {
          for (const req of keys) {
            if (req.url !== rootfsUrl) cache.delete(req).catch(() => {});
          }
        })
        .catch(() => {});
      // Cache asynchronously so streaming decompression starts immediately.
      cache.put(rootfsUrl, resp.clone()).catch(() => {});
    } catch {
      // Ignore quota or clone errors.
    }
  }
  return { response: resp, fromCache: false };
}

async function fetchAndExtractTarGz(rootfsUrl, onProgress) {
  const { response: resp, fromCache } = await fetchRootfsResponse(
    rootfsUrl,
    onProgress
  );
  const totalBytes = Number(resp.headers.get("content-length") || 0);
  let loadedBytes = 0;

  const progressStream = new TransformStream({
    transform(chunk, controller) {
      loadedBytes += chunk.byteLength;
      onProgress?.({
        phase: fromCache ? "cache" : "download",
        loadedBytes,
        totalBytes,
      });
      controller.enqueue(chunk);
    },
  });

  const gunzipStream = resp.body
    .pipeThrough(progressStream)
    .pipeThrough(new DecompressionStream("gzip"));
  const reader = gunzipStream.getReader();

  // O(N) chunk-queue reader: avoids O(N^2) reallocation on large .so members.
  const chunks = [];
  let headIdx = 0;
  let headOff = 0;
  let buffered = 0;

  async function readExact(n) {
    while (buffered < n) {
      const { done, value } = await reader.read();
      if (done) break;
      if (value && value.byteLength > 0) {
        chunks.push(value);
        buffered += value.byteLength;
      }
    }
    if (buffered === 0) return null;
    const take = Math.min(n, buffered);
    const out = new Uint8Array(take);
    let written = 0;
    while (written < take) {
      const cur = chunks[headIdx];
      const avail = cur.byteLength - headOff;
      const step = Math.min(avail, take - written);
      out.set(cur.subarray(headOff, headOff + step), written);
      written += step;
      headOff += step;
      if (headOff === cur.byteLength) {
        chunks[headIdx] = null;
        headIdx += 1;
        headOff = 0;
      }
    }
    buffered -= take;
    if (headIdx > 64) {
      chunks.splice(0, headIdx);
      headIdx = 0;
    }
    return out;
  }

  async function skipExact(n) {
    if (n <= 0) return;
    await readExact(n);
  }

  const rootDir = new Directory([]);
  let pendingLongName = null;
  let pendingPaxPath = null;

  while (true) {
    const hdr = await readExact(512);
    if (!hdr || hdr.length < 512) break;

    let allZero = true;
    for (let i = 0; i < 512; i++) {
      if (hdr[i] !== 0) {
        allZero = false;
        break;
      }
    }
    if (allZero) continue;

    const name = decodeCString(hdr.subarray(0, 100));
    const size = parseOctal(hdr.subarray(124, 136));
    const typeFlag = hdr[156] === 0 ? "0" : String.fromCharCode(hdr[156]);
    const prefix = decodeCString(hdr.subarray(345, 500));
    const paddedSize = Math.ceil(size / 512) * 512;
    const payload = size > 0 ? (await readExact(size)) || new Uint8Array(0) : new Uint8Array(0);
    await skipExact(paddedSize - size);

    if (typeFlag === "L") {
      pendingLongName = decodeCString(payload);
      continue;
    }
    if (typeFlag === "x") {
      const text = new TextDecoder("utf-8").decode(payload);
      for (const line of text.split("\n")) {
        const sp = line.indexOf(" ");
        if (sp !== -1) {
          const kv = line.slice(sp + 1);
          if (kv.startsWith("path=")) {
            pendingPaxPath = kv.slice(5);
          }
        }
      }
      continue;
    }

    const fullPath =
      pendingPaxPath ??
      pendingLongName ??
      (prefix ? `${prefix}/${name}` : name);
    pendingLongName = null;
    pendingPaxPath = null;

    if (typeFlag === "5") {
      insertEntry(rootDir.contents, fullPath, true, null);
    } else if (typeFlag === "0") {
      insertEntry(rootDir.contents, fullPath, false, payload);
    }
  }

  insertEntry(rootDir.contents, "tmp/work", true, null);
  insertEntry(rootDir.contents, "tmp/out", true, null);
  return { rootfs: new PreopenDirectory("/", rootDir.contents), fromCache };
}

async function bootSession({ rootfsUrl, chapterModule }) {
  if (!runCmd) {
    const t0 = performance.now();
    hsSearchDir = null;
    self.postMessage({
      type: "progress",
      phase: "download",
      loadedBytes: 0,
      totalBytes: 0,
    });
    const { rootfs, fromCache } = await fetchAndExtractTarGz(rootfsUrl, (p) =>
      self.postMessage({ type: "progress", ...p })
    );
    if (!hsSearchDir) {
      throw new Error(
        "Could not locate wasm32-wasi dynamic library directory in rootfs"
      );
    }

    self.postMessage({ type: "progress", phase: "link" });
    const dyld = await dyldMain({
      rpc: new DyLDBrowserHost({
        rootfs,
        stdout: (msg) => stdoutLines.push(msg),
        stderr: (msg) => stderrLines.push(msg),
      }),
      searchDirs: ["/tmp/clib", hsSearchDir],
      mainSoPath: "/tmp/libplfh_ghci.so",
      args: ["libplfh_ghci.so", "+RTS", "-H64m", "-RTS"],
      isIserv: false,
    });

    self.postMessage({ type: "progress", phase: "boot" });
    const runner = await dyld.exportFuncs.bootPlfhGhci("/tmp/hslib/lib");
    await runner("setflags", defaultFlags, "");
    drainOutput();
    runCmd = runner;
    const bootMs = Math.round(performance.now() - t0);
    self.postMessage({ type: "ready", bootMs, fromCache });
  }

  const targetCtx = chapterModule || "__default__";
  if (targetCtx !== currentChapter) {
    currentChapter = targetCtx;
    const mods = chapterModule
      ? `Prelude Data.Type.Equality GHC.Sigma HaskLib.Nat ${chapterModule}`
      : "Prelude Data.Type.Equality GHC.Sigma HaskLib.Nat";
    await runCmd("context", "", mods);
    drainOutput();
  }
}

function stripLeadingCommentsAndPragmas(src) {
  return src
    .replace(/^\s*(\{-#[\s\S]*?#-}\s*|--[^\n]*\n\s*|\{-[\s\S]*?-}\s*)*/g, "")
    .trimStart();
}

// Extract top-level definitions from a Haskell snippet so `import Chapter hiding (...)`
// avoids shadowing collisions (including constructors via `Name (..)`).
function extractDefinedEntities(code) {
  const typesWithCtors = new Set();
  const plainNames = new Set();
  const skipKw = new Set([
    "module",
    "import",
    "infix",
    "infixl",
    "infixr",
    "instance",
    "default",
    "foreign",
    "deriving",
    "where",
  ]);

  for (const rawLine of code.split("\n")) {
    if (/^\s*(--|\{-|$)/.test(rawLine) || /^\s+/.test(rawLine)) continue;
    let m;
    if (
      (m = rawLine.match(
        /^(?:data|newtype|class)\s+(?:family\s+|instance\s+)?([A-Z][A-Za-z0-9_']*)/
      ))
    ) {
      typesWithCtors.add(m[1]);
      continue;
    }
    if (
      (m = rawLine.match(
        /^type\s+(?:family\s+|instance\s+)?([A-Z][A-Za-z0-9_']*|\([^)]+\))/
      ))
    ) {
      plainNames.add(m[1]);
      continue;
    }
    if (
      (m = rawLine.match(
        /^([a-z_][A-Za-z0-9_']*)\s*(?:::|@|\s+[A-Za-z0-9_('`~]|=)/
      ))
    ) {
      if (!skipKw.has(m[1])) {
        plainNames.add(m[1]);
      }
      continue;
    }
    if ((m = rawLine.match(/^(\([^)\s]+\))\s*(?:::|=)/))) {
      plainNames.add(m[1]);
    }
  }

  for (const t of typesWithCtors) {
    plainNames.delete(t);
  }

  const allNames = new Set([...typesWithCtors, ...plainNames]);
  return { typesWithCtors, plainNames, allNames };
}

const HASKLIB_NAT_EXPORTS = new Set([
  "Nat",
  "Zero",
  "Succ",
  "plus",
  "eqSize",
  "eqSizeRefl",
  "plusZero",
  "plusSucc",
  "congFirst",
  "(+)",
]);

function makeHidingClause(typesWithCtors, plainNames, allowedExports) {
  const specs = [];
  for (const t of typesWithCtors) {
    if (!allowedExports || allowedExports.has(t)) {
      specs.push(`${t} (..)`);
    }
  }
  for (const n of plainNames) {
    if (!allowedExports || allowedExports.has(n)) {
      specs.push(n);
    }
  }
  return specs.length > 0 ? ` hiding (${specs.join(", ")})` : "";
}

// Strip redefined symbols from explicit parenthesized chapter import lists
// (e.g. `import HaskLib.Nat (Nat (..), plus)` when the snippet defines `plus`).
function filterExplicitImport(impStmt, redefinedNames) {
  if (redefinedNames.size === 0) return impStmt;
  if (/^\s*import\s+qualified\b/.test(impStmt) || /\bhiding\b/.test(impStmt)) {
    return impStmt;
  }
  const open = impStmt.indexOf("(");
  const close = impStmt.lastIndexOf(")");
  if (open === -1 || close === -1 || close < open) return impStmt;

  const prefix = impStmt.slice(0, open);
  const inner = impStmt.slice(open + 1, close);
  const suffix = impStmt.slice(close + 1);

  // Split top-level comma-separated import items (respecting nested parens like `Nat (..)`).
  const items = [];
  let depth = 0;
  let cur = "";
  for (const ch of inner) {
    if (ch === "(") depth++;
    else if (ch === ")") depth--;
    if (ch === "," && depth === 0) {
      items.push(cur);
      cur = "";
    } else {
      cur += ch;
    }
  }
  if (cur.trim()) items.push(cur);

  const kept = items.filter((raw) => {
    const t = raw.trim().replace(/^type\s+/, "");
    const m = t.match(/^([A-Za-z_][A-Za-z0-9_']*|\([^)]+\))/);
    return !m || !redefinedNames.has(m[1]);
  });

  if (kept.length === 0) return "";
  return `${prefix}(${kept.map((s) => s.trim()).join(", ")})${suffix}`;
}

function buildModuleSource(
  code,
  chapterModule,
  chapterPragmas = [],
  chapterImports = [],
  chapterExports = null
) {
  const body = stripLeadingCommentsAndPragmas(code);
  const modMatch = body.match(/^module\s+([A-Za-z0-9_.]+)/);
  if (modMatch) {
    const modName = modMatch[1];
    const relPath = modName.replace(/\./g, "/") + ".hs";
    return {
      filePath: `/tmp/work/${relPath}`,
      modName,
      fullSource: code.includes("DependentTypes")
        ? code
        : `{-# LANGUAGE DependentTypes #-}\n${code}`,
    };
  }

  const snippetPragmas = [];
  const restLines = [];
  for (const line of code.split("\n")) {
    if (/^\s*\{-#\s*(LANGUAGE|OPTIONS_GHC)\b/.test(line)) {
      snippetPragmas.push(line);
    } else {
      restLines.push(line);
    }
  }

  const snippetImports = [];
  const declLines = [];
  let inImport = false;
  for (const line of restLines) {
    if (/^\s*import\s+/.test(line)) {
      snippetImports.push(line);
      inImport = true;
    } else if (inImport && /^\s+/.test(line) && line.trim().length > 0) {
      snippetImports.push(line);
    } else {
      inImport = false;
      declLines.push(line);
    }
  }

  const declBody = declLines.join("\n");
  const { typesWithCtors, plainNames, allNames } = extractDefinedEntities(declBody);
  const exportSet = Array.isArray(chapterExports) ? new Set(chapterExports) : null;
  const chapterHiding = makeHidingClause(typesWithCtors, plainNames, exportSet);
  const natHiding = makeHidingClause(typesWithCtors, plainNames, HASKLIB_NAT_EXPORTS);

  const filteredChapterImports = chapterImports
    .map((imp) => filterExplicitImport(imp, allNames))
    .filter((s) => s.trim().length > 0);

  const allImportsText =
    filteredChapterImports.join("\n") + "\n" + snippetImports.join("\n");
  const hasEquality = /\bData\.Type\.Equality\b/.test(allImportsText);
  const hasSigma = /\bGHC\.Sigma\b/.test(allImportsText);
  const hasHaskLibNat = /\bHaskLib\.Nat\b/.test(allImportsText);

  const header = [
    "{-# LANGUAGE AllowAmbiguousTypes, DependentTypes, LambdaCase #-}",
    ...chapterPragmas,
    ...snippetPragmas,
    "module PlfhInteractive where",
    ...filteredChapterImports,
    ...(!hasEquality
      ? ["import Data.Type.Equality ((:~:) (Refl), sym, trans)"]
      : []),
    ...(!hasSigma ? ["import GHC.Sigma (Sigma (Pair))"] : []),
    ...(!hasHaskLibNat ? [`import HaskLib.Nat${natHiding}`] : []),
    ...(chapterModule ? [`import ${chapterModule}${chapterHiding}`] : []),
    ...snippetImports,
    "",
    declBody,
    "",
  ].join("\n");

  return {
    filePath: "/tmp/work/PlfhInteractive.hs",
    modName: "PlfhInteractive",
    fullSource: header,
  };
}

async function handleRepl(line) {
  const trimmed = line.trim();
  if (!trimmed) {
    return { status: "OK", stdout: "", stderr: "" };
  }
  let m;
  let status;
  if ((m = trimmed.match(/^:(?:t|type)\s+([\s\S]+)$/))) {
    status = await runCmd("type", m[1].trim(), "");
  } else if ((m = trimmed.match(/^:(?:k!|kind!)\s+([\s\S]+)$/))) {
    status = await runCmd("kind!", m[1].trim(), "");
  } else if ((m = trimmed.match(/^:(?:k|kind)\s+([\s\S]+)$/))) {
    status = await runCmd("kind", m[1].trim(), "");
  } else if ((m = trimmed.match(/^:(?:i|info)\s+([\s\S]+)$/))) {
    status = await runCmd("info", m[1].trim(), "");
  } else if ((m = trimmed.match(/^:browse!?\s*([\s\S]*)$/))) {
    const targetMod =
      m[1].trim() || (currentChapter && currentChapter !== "__default__" ? currentChapter : "HaskLib.Nat");
    status = await runCmd("browse", targetMod, "");
  } else if ((m = trimmed.match(/^:set\s+([\s\S]+)$/))) {
    status = await runCmd("setflags", `${defaultFlags} ${m[1].trim()}`, "");
  } else if (
    /^(?:data|newtype|type|class|instance)\b/.test(trimmed) ||
    trimmed.includes("\n")
  ) {
    status = await runCmd("decls", trimmed, "");
  } else {
    status = await runCmd("eval", trimmed, "");
  }
  const { stdout, stderr } = drainOutput();
  return { status, stdout, stderr };
}

let queue = Promise.resolve();

self.addEventListener("message", (ev) => {
  const msg = ev.data;
  queue = queue
    .then(async () => {
      const t0 = performance.now();
      try {
        if (msg.type === "boot") {
          await bootSession(msg);
          self.postMessage({
            id: msg.id,
            ok: true,
            status: "OK",
            stdout: "",
            stderr: "",
            elapsedMs: Math.round(performance.now() - t0),
          });
          return;
        }

        await bootSession(msg);

        if (msg.type === "checkBlock") {
          const extra = msg.extraGhcArgs ? ` ${msg.extraGhcArgs}` : "";
          await runCmd("setflags", `${defaultFlags}${extra}`, "");
          interactiveMode = false;
          drainOutput();

          const { filePath, modName, fullSource } = buildModuleSource(
            msg.code,
            msg.chapterModule || currentChapter,
            msg.chapterPragmas || [],
            msg.chapterImports || [],
            msg.chapterExports ?? null
          );
          await runCmd("write", filePath, fullSource);
          const mode = msg.typecheckOnly ? "typecheck" : "load";
          const status = await runCmd(mode, filePath, modName);
          const { stdout, stderr } = drainOutput();
          self.postMessage({
            id: msg.id,
            ok: status === "OK",
            status,
            stdout,
            stderr,
            elapsedMs: Math.round(performance.now() - t0),
          });
          return;
        }

        if (msg.type === "repl") {
          if (!interactiveMode) {
            await runCmd("setflags", replFlags, "");
            interactiveMode = true;
            drainOutput();
          }
          const { status, stdout, stderr } = await handleRepl(msg.line);
          self.postMessage({
            id: msg.id,
            ok: status === "OK",
            status,
            stdout,
            stderr,
            elapsedMs: Math.round(performance.now() - t0),
          });
          return;
        }

        if (msg.type === "raw") {
          const status = await runCmd(
            msg.mode,
            msg.arg1 || "",
            msg.arg2 || ""
          );
          const { stdout, stderr } = drainOutput();
          self.postMessage({
            id: msg.id,
            ok: status === "OK",
            status,
            stdout,
            stderr,
            elapsedMs: Math.round(performance.now() - t0),
          });
          return;
        }

        throw new Error(`Unknown worker message type: ${msg.type}`);
      } catch (err) {
        const { stdout, stderr } = drainOutput();
        self.postMessage({
          id: msg.id,
          ok: false,
          status: "ERR:worker",
          stdout,
          stderr: stderr
            ? `${stderr}\n${err.message || err}`
            : String(err.message || err),
          elapsedMs: Math.round(performance.now() - t0),
        });
      }
    })
    .catch((err) => console.error("Worker queue error:", err));
});
