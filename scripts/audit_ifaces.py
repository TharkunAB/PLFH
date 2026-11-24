#!/usr/bin/env python3
"""Audit compiled GHC .hi interfaces under PLFH/ for accidentally quantified
function-kinded type variables (e.g. unqualified `substTerm`/`substSingle`
silently bound as fresh universal tyvars in GADT constructors)."""

import pathlib
import re
import subprocess
import sys

# Explicit allowlist of intentional higher-order type parameters (predicates,
# binary relations, type constructors, reduction relations).
ALLOWED_HO_TYVARS = {
    "a", "b", "c", "d", "e", "f", "g", "h", "k", "m", "n", "p", "q", "r",
    "rel", "step",
}

BINDER_HEAD_RE = re.compile(r"^\s*([a-z][A-Za-z0-9_']*)\s*::\s*(.*)$")


def extract_balanced_binders(hdr: str) -> list[tuple[str, str]]:
    """Extract top-level `(name :: kind)` and `{name :: kind}` binders with
    arbitrary nested parentheses inside `kind`."""
    results: list[tuple[str, str]] = []
    i = 0
    n = len(hdr)
    while i < n:
        ch = hdr[i]
        if ch in "({":
            close = ")" if ch == "(" else "}"
            depth = 1
            j = i + 1
            while j < n and depth > 0:
                if hdr[j] == ch:
                    depth += 1
                elif hdr[j] == close:
                    depth -= 1
                j += 1
            if depth == 0:
                inner = hdr[i + 1 : j - 1]
                m = BINDER_HEAD_RE.match(inner)
                if m:
                    results.append((m.group(1), m.group(2).strip()))
            i = j
        else:
            i += 1
    return results


def main() -> int:
    if len(sys.argv) != 3:
        print(f"usage: {sys.argv[0]} <ghc> <build-dir>", file=sys.stderr)
        return 2
    ghc = sys.argv[1]
    build_dir = pathlib.Path(sys.argv[2])
    plfh_dir = build_dir / "PLFH"
    if not plfh_dir.is_dir():
        print(f"ERROR: {plfh_dir} not found", file=sys.stderr)
        return 2

    his = sorted(plfh_dir.rglob("*.hi"))
    findings: list[tuple[str, str, str]] = []
    seen_allowed: set[str] = set()

    for hi in his:
        rel = hi.relative_to(build_dir).as_posix()
        proc = subprocess.run(
            [ghc, "--show-iface", str(hi)],
            capture_output=True,
            text=True,
            check=True,
        )
        text = re.sub(r"\n\s+", " ", proc.stdout)
        # Note: in GHC --show-iface, module-qualified names contain `.` inside
        # kinds (e.g. `PLFH.Part2.Untyped.UTerm`), so the terminator of a
        # `forall` binder list is `. ` (dot followed by space or end-of-line),
        # NOT a bare `.` inside a qualified identifier!
        for chunk in re.finditer(r"\bforall\b(.*?)\.(?:\s|$)", text):
            hdr = chunk.group(1)
            for name, kind in extract_balanced_binders(hdr):
                if "->" in kind:
                    if name in ALLOWED_HO_TYVARS:
                        seen_allowed.add(name)
                    else:
                        findings.append((rel, name, kind))

    if findings:
        print("  [FAIL] Interface soundness audit detected suspicious function-kinded type variables:")
        for rel, name, kind in findings:
            print(f"    - {rel}: ({name} :: {kind})")
        return 1

    print(
        f"  [PASS] Interface soundness audit: {len(his)} .hi files clean "
        f"(0 unintended function tyvars; allowed HO params seen: {sorted(seen_allowed)})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
