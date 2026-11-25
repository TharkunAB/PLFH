#!/usr/bin/env python3
"""Extract checked Haskell modules and negative controls from PLFH literate Markdown chapters.

Optionally syncs standalone .hs modules, negative controls, and minimal compiler-bug
reproducers to the GHC fork's docs/dependent-haskell/plfh/ directory so the compiler
team can replay every result directly with plain GHC.
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CONTENT_DIR = ROOT / "content"
CLIENTS_DIR = ROOT / "clients"
HS_DIR = ROOT / "hs"
NEG_DIR = HS_DIR / "negative"
REPRO_DIR = ROOT / "reproducers"
HASKLIB_REF_DIR = ROOT / "reference" / "hasklib"

HASKLIB_FILES = (
    ("hasklib", "HaskLib.hs"),
    ("hasklib", "HaskLib/Nat.hs"),
    ("hasklib", "HaskLib/List.hs"),
    ("hasklib", "HaskLib/Size.hs"),
    ("hasklib", "HaskLib/List/Prefix.hs"),
    ("examples/open-evaluation", "PreludeMapLengthSize.hs"),
    ("examples/open-evaluation", "PreludeZipRuntime.hs"),
    ("examples/open-evaluation", "PreludeZipMapRuntime.hs"),
)

FRONTMATTER_RE = re.compile(r"^---\n(.*?)\n---\n", re.DOTALL)
FENCE_OPEN_RE = re.compile(r"^```(.*)$")


def parse_frontmatter(text: str) -> dict[str, str]:
    m = FRONTMATTER_RE.match(text)
    if not m:
        return {}
    meta: dict[str, str] = {}
    for line in m.group(1).splitlines():
        if ":" in line:
            k, v = line.split(":", 1)
            meta[k.strip()] = v.strip().strip('"').strip("'")
    return meta


def parse_fence_info(info: str) -> tuple[str, set[str], dict[str, str]]:
    """Parse ```haskell or ```{.haskell .wip name="Foo" expect="GHC-83865"}."""
    info = info.strip()
    if not info:
        return "", set(), {}
    if info.startswith("{") and info.endswith("}"):
        inner = info[1:-1].strip()
        classes: set[str] = set()
        attrs: dict[str, str] = {}
        lang = ""
        for tok in re.findall(r'[A-Za-z0-9_-]+="[^"]*"|[A-Za-z0-9_-]+=\S+|\.\S+|\S+', inner):
            if tok.startswith("."):
                cls = tok[1:]
                if not lang and cls in ("haskell", "bash", "sh", "nix", "text"):
                    lang = cls
                else:
                    classes.add(cls)
            elif "=" in tok:
                k, v = tok.split("=", 1)
                attrs[k] = v.strip('"').strip("'")
        return lang, classes, attrs
    parts = info.split()
    lang = parts[0]
    classes = set()
    attrs = {}
    for tok in parts[1:]:
        if "=" in tok:
            k, v = tok.split("=", 1)
            attrs[k] = v.strip('"').strip("'")
        else:
            classes.add(tok)
    return lang, classes, attrs


def extract_chapter(md_path: Path) -> tuple[Path | None, list[tuple[str, str, str]]]:
    text = md_path.read_text(encoding="utf-8")
    meta = parse_frontmatter(text)
    mod_name = meta.get("module")
    rel_md = md_path.relative_to(ROOT).as_posix()

    lines = text.splitlines()
    in_fence = False
    fence_lang = ""
    fence_classes: set[str] = set()
    fence_attrs: dict[str, str] = {}
    fence_start_line = 0
    buf: list[str] = []

    module_chunks: list[tuple[int, list[str]]] = []
    neg_controls: list[tuple[str, str, str]] = []  # (name, expect, code)

    for idx, line in enumerate(lines, start=1):
        if not in_fence:
            m = FENCE_OPEN_RE.match(line)
            if m and m.group(1).strip():
                lang, classes, attrs = parse_fence_info(m.group(1))
                in_fence = True
                fence_lang = lang
                fence_classes = classes
                fence_attrs = attrs
                fence_start_line = idx + 1
                buf = []
            elif line.strip() == "```":
                in_fence = True
                fence_lang = ""
                fence_classes = set()
                fence_attrs = {}
                fence_start_line = idx + 1
                buf = []
        else:
            if line.strip() == "```":
                if fence_lang == "haskell":
                    if "fail" in fence_classes:
                        name = fence_attrs.get("name")
                        expect = fence_attrs.get("expect", "")
                        if name:
                            code = "\n".join(buf) + "\n"
                            neg_controls.append((name, expect, code))
                    elif not (fence_classes & {"wip", "exercise", "ignore", "spec"}):
                        module_chunks.append((fence_start_line, buf))
                in_fence = False
                buf = []
            else:
                buf.append(line)

    out_path: Path | None = None
    if mod_name and module_chunks:
        out_path = HS_DIR / Path(*mod_name.split(".")).with_suffix(".hs")
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_lines = [
            f"-- Generated from {rel_md} by scripts/extract_and_sync.py",
            "-- Do not edit directly; edit the literate Markdown chapter instead.",
            "",
        ]
        # Keep leading LANGUAGE / OPTIONS_GHC pragmas at top of file before LINE pragmas
        first_line, first_chunk = module_chunks[0]
        pragma_end = 0
        while pragma_end < len(first_chunk) and (
            first_chunk[pragma_end].startswith("{-#") or first_chunk[pragma_end].strip() == ""
        ):
            pragma_end += 1
        if pragma_end > 0:
            out_lines.extend(first_chunk[:pragma_end])
            rest = first_chunk[pragma_end:]
            if rest:
                out_lines.append(f'{{# LINE {first_line + pragma_end} "{rel_md}" #}}'.replace("{#", "{-#").replace("#}", "#-}"))
                out_lines.extend(rest)
                out_lines.append("")
        else:
            out_lines.append(f'{{-# LINE {first_line} "{rel_md}" #-}}')
            out_lines.extend(first_chunk)
            out_lines.append("")

        for start_line, chunk in module_chunks[1:]:
            out_lines.append(f'{{-# LINE {start_line} "{rel_md}" #-}}')
            out_lines.extend(chunk)
            out_lines.append("")

        out_path.write_text("\n".join(out_lines), encoding="utf-8")

    return out_path, neg_controls


def write_negative_controls(neg_controls: list[tuple[str, str, str]]) -> list[Path]:
    written: list[Path] = []
    if not neg_controls:
        return written
    NEG_DIR.mkdir(parents=True, exist_ok=True)
    for name, expect, code in neg_controls:
        p = NEG_DIR / f"{name}.hs"
        header = f"-- EXPECT-ERROR: {expect}\n" if expect else ""
        # Place EXPECT-ERROR comment after leading pragmas so GHC pragmas stay at top
        code_lines = code.splitlines()
        i = 0
        while i < len(code_lines) and code_lines[i].startswith("{-#"):
            i += 1
        final = "\n".join(code_lines[:i] + ([header.strip()] if header else []) + code_lines[i:]) + "\n"
        p.write_text(final, encoding="utf-8")
        written.append(p)
    return written


def sync_to_ghc(ghc_plfh_dir: Path) -> None:
    ghc_plfh_dir.mkdir(parents=True, exist_ok=True)
    for sub in ("hs", "reproducers"):
        src = ROOT / sub
        dst = ghc_plfh_dir / sub
        if dst.exists():
            shutil.rmtree(dst)
        if src.exists():
            shutil.copytree(src, dst)
    print(f"Synced hs/ and reproducers/ -> {ghc_plfh_dir}")


def sync_hasklib_reference(dh_docs_dir: Path) -> None:
    copied = 0
    for subdir, rel in HASKLIB_FILES:
        src = dh_docs_dir / subdir / rel
        if not src.exists():
            continue
        dst = HASKLIB_REF_DIR / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, dst)
        copied += 1
    if copied:
        print(f"Synced {copied} HaskLib reference file(s) -> {HASKLIB_REF_DIR.relative_to(ROOT)}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--sync-ghc",
        type=Path,
        default=None,
        help="Path to GHC repo's docs/dependent-haskell/plfh directory to mirror hs/ and reproducers/",
    )
    parser.add_argument(
        "--sync-hasklib",
        type=Path,
        default=None,
        help="Path to GHC repo's docs/dependent-haskell directory to snapshot HaskLib sources into reference/hasklib/",
    )
    args = parser.parse_args()

    # Clean old generated hs/ files before regenerating
    if HS_DIR.exists():
        shutil.rmtree(HS_DIR)

    # Copy hand-maintained client modules (e.g. InductionClient.hs)
    if CLIENTS_DIR.exists():
        shutil.copytree(CLIENTS_DIR, HS_DIR)

    extracted_modules: list[Path] = []
    all_negs: list[tuple[str, str, str]] = []

    for md_path in sorted(CONTENT_DIR.rglob("*.md")):
        mod_path, negs = extract_chapter(md_path)
        if mod_path:
            extracted_modules.append(mod_path)
        all_negs.extend(negs)

    neg_paths = write_negative_controls(all_negs)
    print(f"Extracted {len(extracted_modules)} module(s) and {len(neg_paths)} negative control(s).")
    for p in extracted_modules:
        print(f"  module: {p.relative_to(ROOT)}")
    for p in neg_paths:
        print(f"  neg:    {p.relative_to(ROOT)}")

    if args.sync_ghc:
        sync_to_ghc(args.sync_ghc)

    if args.sync_hasklib:
        sync_hasklib_reference(args.sync_hasklib)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
