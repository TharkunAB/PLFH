#!/usr/bin/env bash
# Verify extracted PLFH chapters, negative controls, fixed-reproducer regressions,
# runtime smoke tests, and minimal open compiler-bug reproducers using the
# Dependent Haskell GHC fork.
#
# On this host (when ghc-build-job is present and PLFH_NO_PUEUE != 1), submits the entire
# verification suite as ONE job to the shared pueue queue so it completes in a single slot.
#
# Environment variables:
#   PLFH_GHC        Path to stage1/bin/ghc (or verified component ghc) from Tritlo/ghc
#   PLFH_GHC_LIBDIR Optional -B<libdir> when running a relinked component compiler
#   PLFH_GHC_REPO   Path to Tritlo/ghc checkout (for HaskLib & ghc-build-job)
#   PLFH_NO_PUEUE   Set to 1 to run ghc directly instead of via ghc-build-job / pueue
set -euo pipefail
export LC_ALL=C

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
PLFH_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
GHC_REPO=${PLFH_GHC_REPO:-/home/tritlo/Code/ghc}

# Prefer the latest verified published component binary on dependent-haskell:
#   056871faa9 (two-binder SourceClosure & substDouble for More + 4570cbe2f8),
#   falling back to 4570cbe2f8, 8632606465, fb64eaff81, ad1a979ead, 2deac8b91e, 9d310102c7, 35916907b9, da06279b7a, f0bc12e601, 6c8ab7f7de, 3326acd9b1, e7a798a060, c97f70ecdc, 2e4fbb752a, 1f873969e5, 63e2f0974b, 9cc4065fab, or 590.
COMP_056="$GHC_REPO/_build/on-demand/plfh-more-witness-integration-20261124/joint.heqcOi/component/ghc"
COMP_457="$GHC_REPO/_build/on-demand/plfh-joint-witness-7ec3.1prHXyxM/checked.YSXkDVmS/component/ghc"
COMP_863="$GHC_REPO/_build/on-demand/plfh-progress-backends-fb64-20261124/mixed-bytecode/relink.0sLsma/component/ghc"
COMP_FB6="$GHC_REPO/_build/on-demand/plfh-beta-forward-c752-20261124/relink.R6vWzk/component/ghc"
COMP_AD1="$GHC_REPO/_build/on-demand/plfh-r23-ordinary-cong-167834fb-20261124/candidate/component/ghc"
COMP_2DE="$GHC_REPO/_build/on-demand/plfh-vector-diagnostic-compat-33a76c71.5Cha2t4T/final.j4SL5TOU/component/ghc"
COMP_9D3="$GHC_REPO/_build/on-demand/plfh-retained-columns-and-constructors-7c18bfb.lOliSoZj/final.rAKHTW1r/component/ghc"
COMP_359="$GHC_REPO/_build/on-demand/plfh-r23-matchability-20261124/tuple/component/ghc"
COMP_DA0="$GHC_REPO/_build/on-demand/plfh-connectives-swap-combined.a9mMutyA/broad.iwYHO6WH/compiler/ghc"
COMP_F0B="$GHC_REPO/_build/on-demand/plfh-r13-rev-local-9111-20261124/checked/component/ghc"
COMP_6C8="$GHC_REPO/_build/on-demand/plfh-iso-transitivity-8def3bbd.ezUTMZSt/final.lamb4bMy/compiler/ghc"
COMP_332="$GHC_REPO/_build/on-demand/plfh-r11-nested-gadt-8b37-20261124/checked/component/ghc"
COMP_E7A="$GHC_REPO/_build/on-demand/plfh-indexed-app-forward-34582-20261124/checked/component/ghc"
COMP_C97="$GHC_REPO/_build/on-demand/plfh-integration-601-20261124/check.hAzvA2/compiler/ghc"
COMP_2E4="$GHC_REPO/_build/on-demand/plfh-pow-progress-combined-20261124/checked/component/ghc"
COMP_1F8="$GHC_REPO/_build/on-demand/r13-pow-open-eq-20261124/relink.yk1Z2S/component/ghc"
COMP_63E="$GHC_REPO/_build/on-demand/r13-monus-open-eq-20261124/forward-0043/relink.KarCex/component/ghc"
COMP_9CC="$GHC_REPO/_build/on-demand/r03-nested-dep-case-20261124/audit-692/checked/component/ghc"
COMP_LIB="$GHC_REPO/_build/on-demand/r17-schema-transformer-post-588-20261124/source/_build/stage1/lib"
LEGACY_590="$GHC_REPO/_build/on-demand/r17-schema-transformer-post-588-20261124/source/_build/stage1/bin/ghc"

DEFAULT_COMPILER=""
DEFAULT_LIBDIR=""
if [[ -x "$COMP_056" ]]; then
  DEFAULT_COMPILER="$COMP_056"
  DEFAULT_LIBDIR="$COMP_LIB"
elif [[ -x "$COMP_457" ]]; then
  DEFAULT_COMPILER="$COMP_457"
  DEFAULT_LIBDIR="$COMP_LIB"
elif [[ -x "$COMP_863" ]]; then
  DEFAULT_COMPILER="$COMP_863"
  DEFAULT_LIBDIR="$COMP_LIB"
elif [[ -x "$COMP_FB6" ]]; then
  DEFAULT_COMPILER="$COMP_FB6"
  DEFAULT_LIBDIR="$COMP_LIB"
elif [[ -x "$COMP_AD1" ]]; then
  DEFAULT_COMPILER="$COMP_AD1"
  DEFAULT_LIBDIR="$COMP_LIB"
elif [[ -x "$COMP_2DE" ]]; then
  DEFAULT_COMPILER="$COMP_2DE"
  DEFAULT_LIBDIR="$COMP_LIB"
elif [[ -x "$COMP_9D3" ]]; then
  DEFAULT_COMPILER="$COMP_9D3"
  DEFAULT_LIBDIR="$COMP_LIB"
elif [[ -x "$COMP_359" ]]; then
  DEFAULT_COMPILER="$COMP_359"
  DEFAULT_LIBDIR="$COMP_LIB"
elif [[ -x "$COMP_DA0" ]]; then
  DEFAULT_COMPILER="$COMP_DA0"
  DEFAULT_LIBDIR="$COMP_LIB"
elif [[ -x "$COMP_F0B" ]]; then
  DEFAULT_COMPILER="$COMP_F0B"
  DEFAULT_LIBDIR="$COMP_LIB"
elif [[ -x "$COMP_6C8" ]]; then
  DEFAULT_COMPILER="$COMP_6C8"
  DEFAULT_LIBDIR="$COMP_LIB"
elif [[ -x "$COMP_332" ]]; then
  DEFAULT_COMPILER="$COMP_332"
  DEFAULT_LIBDIR="$COMP_LIB"
elif [[ -x "$COMP_E7A" ]]; then
  DEFAULT_COMPILER="$COMP_E7A"
  DEFAULT_LIBDIR="$COMP_LIB"
elif [[ -x "$COMP_C97" ]]; then
  DEFAULT_COMPILER="$COMP_C97"
  DEFAULT_LIBDIR="$COMP_LIB"
elif [[ -x "$COMP_2E4" ]]; then
  DEFAULT_COMPILER="$COMP_2E4"
  DEFAULT_LIBDIR="$COMP_LIB"
elif [[ -x "$COMP_1F8" ]]; then
  DEFAULT_COMPILER="$COMP_1F8"
  DEFAULT_LIBDIR="$COMP_LIB"
elif [[ -x "$COMP_63E" ]]; then
  DEFAULT_COMPILER="$COMP_63E"
  DEFAULT_LIBDIR="$COMP_LIB"
elif [[ -x "$COMP_9CC" ]]; then
  DEFAULT_COMPILER="$COMP_9CC"
  DEFAULT_LIBDIR="$COMP_LIB"
elif [[ -x "$LEGACY_590" ]]; then
  DEFAULT_COMPILER="$LEGACY_590"
else
  DEFAULT_COMPILER="$GHC_REPO/_build/stage1/bin/ghc"
fi

COMPILER=${PLFH_GHC:-$DEFAULT_COMPILER}
GHC_LIBDIR=${PLFH_GHC_LIBDIR:-}
if [[ -z "$GHC_LIBDIR" ]] && [[ "$COMPILER" == "$COMP_359" || "$COMPILER" == "$COMP_DA0" || "$COMPILER" == "$COMP_F0B" || "$COMPILER" == "$COMP_6C8" || "$COMPILER" == "$COMP_332" || "$COMPILER" == "$COMP_E7A" || "$COMPILER" == "$COMP_C97" || "$COMPILER" == "$COMP_2E4" || "$COMPILER" == "$COMP_1F8" || "$COMPILER" == "$COMP_63E" || "$COMPILER" == "$COMP_9CC" ]]; then
  GHC_LIBDIR="$DEFAULT_LIBDIR"
fi

if [[ "${PLFH_NO_PUEUE:-0}" != "1" ]] && [[ -x "$GHC_REPO/docs/dependent-haskell/tools/ghc-build-job" ]]; then
  jid=$(cd "$GHC_REPO" && CAPPED_MEM=5G docs/dependent-haskell/tools/ghc-build-job plfh-suite \
    /usr/bin/env "PLFH_NO_PUEUE=1" "PLFH_GHC=$COMPILER" "PLFH_GHC_LIBDIR=$GHC_LIBDIR" "PLFH_GHC_REPO=$GHC_REPO" \
    bash "$SCRIPT_DIR/check_plfh.sh" "$@")
  echo "Submitted PLFH verification suite as pueue job $jid"
  env -u XDG_RUNTIME_DIR pueue wait -q "$jid"
  env -u XDG_RUNTIME_DIR pueue log --full --json "$jid" | jq -r --arg id "$jid" '.[$id].output'
  status=$(env -u XDG_RUNTIME_DIR pueue log --json "$jid" | jq -r --arg id "$jid" '.[$id].task.status.Done.result')
  [[ "$status" == "Success" ]]
  exit $?
fi

if ! [[ -x "$COMPILER" ]]; then
  echo "ERROR: Dependent Haskell GHC binary not found at: $COMPILER" >&2
  echo "Set PLFH_GHC=/path/to/ghc/_build/stage1/bin/ghc" >&2
  exit 2
fi

GHC_CMD=("$COMPILER")
if [[ -n "$GHC_LIBDIR" ]]; then
  GHC_CMD+=("-B$GHC_LIBDIR")
fi

COMMIT=$("${GHC_CMD[@]}" --info | awk -F'"' '/Project Git commit id/{print $4}')
VERSION=$("${GHC_CMD[@]}" --info | awk -F'"' '/Project version/{print $4}')
echo "=== PLFH Verification ==="
echo "Compiler: $COMPILER"
if [[ -n "$GHC_LIBDIR" ]]; then
  echo "Libdir:   $GHC_LIBDIR"
fi
echo "Version:  $VERSION"
if [[ "$COMPILER" == "$COMP_056" ]]; then
  echo "Commit:   056871faa950d8974764c97d19d96f9d29ef2815 / 60b64904a4 (verified component; base libdir seed: $COMMIT)"
elif [[ "$COMPILER" == "$COMP_457" ]]; then
  echo "Commit:   4570cbe2f8b2e57190e8b36c4aca603bb65256f7 / f0d893681e (verified component; base libdir seed: $COMMIT)"
elif [[ "$COMPILER" == "$COMP_863" ]]; then
  echo "Commit:   8632606465b9c50069fda938753ac75fe72c85f8 / 5ead8de5e4 (verified component; base libdir seed: $COMMIT)"
elif [[ "$COMPILER" == "$COMP_FB6" ]]; then
  echo "Commit:   fb64eaff8171a630b136167bf45c4af8e8333f5f / d7b9870ed0 (verified component; base libdir seed: $COMMIT)"
elif [[ "$COMPILER" == "$COMP_AD1" ]]; then
  echo "Commit:   ad1a979ead80254776043bbc8d79d963aec50e1c / 726cad5c17 (verified component; base libdir seed: $COMMIT)"
elif [[ "$COMPILER" == "$COMP_2DE" ]]; then
  echo "Commit:   2deac8b91ead030898938358ab2f67904d819270 / 781a6c6a8f (verified component; base libdir seed: $COMMIT)"
elif [[ "$COMPILER" == "$COMP_9D3" ]]; then
  echo "Commit:   9d310102c7222750985c6918102a8db75f44ace2 (verified component; base libdir seed: $COMMIT)"
elif [[ "$COMPILER" == "$COMP_359" ]]; then
  echo "Commit:   35916907b952a29fa44613222079d35cd1237b12 (verified component; base libdir seed: $COMMIT)"
elif [[ "$COMPILER" == "$COMP_DA0" ]]; then
  echo "Commit:   da06279b7a4ba86fef478e3f988297ebd3306fd2 (verified component; base libdir seed: $COMMIT)"
elif [[ "$COMPILER" == "$COMP_F0B" ]]; then
  echo "Commit:   f0bc12e601f2323fa91e958f4afc947fbd48bf15 (verified component; base libdir seed: $COMMIT)"
elif [[ "$COMPILER" == "$COMP_6C8" ]]; then
  echo "Commit:   6c8ab7f7deb9bbd0ef5e2fa03a5ece733f638492 / d8eec2036d (verified component; base libdir seed: $COMMIT)"
elif [[ "$COMPILER" == "$COMP_332" ]]; then
  echo "Commit:   3326acd9b1fea98090eb5e8f3f89b5a85e44d849 / 0eb794cd38 (verified component; base libdir seed: $COMMIT)"
elif [[ "$COMPILER" == "$COMP_E7A" ]]; then
  echo "Commit:   e7a798a060b754abb0f9d9dcc9cedddd6b1bdaf5 / 5a7d9d7de8 (verified component; base libdir seed: $COMMIT)"
elif [[ "$COMPILER" == "$COMP_C97" ]]; then
  echo "Commit:   c97f70ecdcbded27a1d705c2e9b4d42a5ddeb028 (verified component; base libdir seed: $COMMIT)"
elif [[ "$COMPILER" == "$COMP_2E4" ]]; then
  echo "Commit:   2e4fbb752a2fca6d9d4ac4b7901e2aa07b3c1534 / 3a6446c77e (verified component; base libdir seed: $COMMIT)"
elif [[ "$COMPILER" == "$COMP_1F8" ]]; then
  echo "Commit:   1f873969e589e84b632e5d0304399ab4d2c997e3 (verified component; base libdir seed: $COMMIT)"
elif [[ "$COMPILER" == "$COMP_63E" ]]; then
  echo "Commit:   63e2f0974b174dc86bef79c3a84d1d76fea3dadf / 76e67f4fdb (verified component; base libdir seed: $COMMIT)"
elif [[ "$COMPILER" == "$COMP_9CC" ]]; then
  echo "Commit:   9cc4065fab4f2f106859b39daa9bdad23f00f0fd (verified component; base libdir seed: $COMMIT)"
else
  echo "Commit:   $COMMIT"
fi
echo ""

# Audit: reject forbidden proof shortcuts in checked modules under hs/PLFH/
if [[ -d "$PLFH_ROOT/hs/PLFH" ]]; then
  if rg -n '\b(undefined|unsafeCoerce)\b|-fdefer-type-errors' "$PLFH_ROOT/hs/PLFH" >/dev/null 2>&1; then
    echo "ERROR: Forbidden proof shortcut found in hs/PLFH:" >&2
    rg -n '\b(undefined|unsafeCoerce)\b|-fdefer-type-errors' "$PLFH_ROOT/hs/PLFH" >&2
    exit 1
  fi
fi

WORK=$(mktemp -d)
trap 'rm -rf -- "$WORK"' EXIT

HASKLIB_SRC=${PLFH_HASKLIB:-}
OPEN_EVAL_SRC="$GHC_REPO/docs/dependent-haskell/examples/open-evaluation"
if [[ -z "$HASKLIB_SRC" ]]; then
  if [[ "$COMPILER" == *r17-schema-transformer-post-588* ]] && [[ -d "$GHC_REPO/_build/on-demand/hasklib-book-nat-rewrite-20261124/source/docs/dependent-haskell/hasklib" ]]; then
    HASKLIB_SRC="$GHC_REPO/_build/on-demand/hasklib-book-nat-rewrite-20261124/source/docs/dependent-haskell/hasklib"
    OPEN_EVAL_SRC="$GHC_REPO/_build/on-demand/hasklib-book-nat-rewrite-20261124/source/docs/dependent-haskell/examples/open-evaluation"
  else
    HASKLIB_SRC="$GHC_REPO/docs/dependent-haskell/hasklib"
  fi
fi

INCLUDES=(
  "-i"
  "-i$HASKLIB_SRC"
  "-i$OPEN_EVAL_SRC"
  "-i$PLFH_ROOT/hs"
)

BUILD_DIR="$WORK/build"
mkdir -p "$BUILD_DIR"

PASS=0
FAIL=0

echo "--- Checked Modules (native -O0 + Core/STG Lint) ---"
mapfile -t MODULES < <(find "$PLFH_ROOT/hs/PLFH" -name '*.hs' 2>/dev/null | sort)
for mod in "${MODULES[@]}"; do
  rel=${mod#"$PLFH_ROOT/"}
  slug=$(echo "$rel" | tr '/.' '__')
  if "${GHC_CMD[@]}" --make -v0 -O0 \
    -fomit-interface-pragmas -fno-write-if-simplified-core \
    -dcore-lint -dstg-lint -package-env - "${INCLUDES[@]}" \
    -outputdir "$BUILD_DIR" "$mod" >"$WORK/$slug.log" 2>&1; then
    echo "  [PASS] $rel"
    PASS=$((PASS + 1))
  else
    echo "  [FAIL] $rel"
    cat "$WORK/$slug.log"
    FAIL=$((FAIL + 1))
  fi
done

echo ""
echo "--- Interface Soundness Audit (.hi files: no silent function tyvars) ---"
if python3 "$SCRIPT_DIR/audit_ifaces.py" "$COMPILER" "$BUILD_DIR"; then
  PASS=$((PASS + 1))
else
  FAIL=$((FAIL + 1))
fi

echo ""
echo "--- Negative Controls (must fail with expected diagnostic) ---"
mapfile -t NEGS < <(find "$PLFH_ROOT/hs/negative" -name '*.hs' 2>/dev/null | sort)
for neg in "${NEGS[@]}"; do
  rel=${neg#"$PLFH_ROOT/"}
  slug=$(echo "$rel" | tr '/.' '__')
  expect=$(awk '/^-- EXPECT-ERROR:/{print $3; exit}' "$neg")
  if "${GHC_CMD[@]}" --make -v0 -O0 \
    -fomit-interface-pragmas -fno-write-if-simplified-core \
    -package-env - "${INCLUDES[@]}" -outputdir "$BUILD_DIR" "$neg" >"$WORK/$slug.log" 2>&1; then
    echo "  [UNEXPECTED PASS] $rel — expected $expect"
    FAIL=$((FAIL + 1))
  elif [[ -n "$expect" ]] && ! grep -q "$expect" "$WORK/$slug.log"; then
    echo "  [WRONG DIAGNOSTIC] $rel — expected $expect, got:"
    cat "$WORK/$slug.log"
    FAIL=$((FAIL + 1))
  else
    echo "  [PASS-NEG] $rel rejected with ${expect:-error}"
    PASS=$((PASS + 1))
  fi
done

if [[ -f "$PLFH_ROOT/hs/PLFH/RuntimeSmokeTest.hs" ]]; then
  echo ""
  echo "--- Runtime Smoke Test Execution ---"
  SMOKE_BIN="$WORK/plfh-smoke"
  if "${GHC_CMD[@]}" --make -v0 -O0 \
    -fomit-interface-pragmas -fno-write-if-simplified-core \
    -dcore-lint -dstg-lint -package-env - "${INCLUDES[@]}" \
    -outputdir "$BUILD_DIR" -main-is PLFH.RuntimeSmokeTest.main \
    -o "$SMOKE_BIN" "$PLFH_ROOT/hs/PLFH/RuntimeSmokeTest.hs" >"$WORK/smoke_build.log" 2>&1 \
    && "$SMOKE_BIN" >"$WORK/smoke_run.log" 2>&1; then
    cat "$WORK/smoke_run.log"
    PASS=$((PASS + 1))
  else
    echo "  [FAIL] RuntimeSmokeTest build or execution failed"
    cat "$WORK/smoke_build.log" "$WORK/smoke_run.log" 2>/dev/null || true
    FAIL=$((FAIL + 1))
  fi
fi

if [[ -d "$PLFH_ROOT/reproducers/fixed" ]]; then
  echo ""
  echo "--- Fixed Reproducers (regression checks: must PASS at -O0 and -O2!) ---"
  FIXED_BUILD_O0="$WORK/fixed-O0"
  FIXED_BUILD_O2="$WORK/fixed-O2"
  mkdir -p "$FIXED_BUILD_O0" "$FIXED_BUILD_O2"
  mapfile -t FIXED_REPROS < <(find "$PLFH_ROOT/reproducers/fixed" -maxdepth 1 -name '*.hs' 2>/dev/null | sort)
  for rep in "${FIXED_REPROS[@]}"; do
    rel=${rep#"$PLFH_ROOT/"}
    slug=$(echo "$rel" | tr '/.' '__')
    if "${GHC_CMD[@]}" --make -v0 -O0 \
      -fomit-interface-pragmas -fno-write-if-simplified-core \
      -dcore-lint -dstg-lint \
      -package-env - "${INCLUDES[@]}" "-i$PLFH_ROOT/reproducers" "-i$PLFH_ROOT/reproducers/fixed" \
      -outputdir "$FIXED_BUILD_O0" "$rep" >"$WORK/${slug}_O0.log" 2>&1 \
      && "${GHC_CMD[@]}" --make -v0 -O2 \
      -fomit-interface-pragmas -fno-write-if-simplified-core \
      -dcore-lint -dstg-lint \
      -package-env - "${INCLUDES[@]}" "-i$PLFH_ROOT/reproducers" "-i$PLFH_ROOT/reproducers/fixed" \
      -outputdir "$FIXED_BUILD_O2" "$rep" >"$WORK/${slug}_O2.log" 2>&1; then
      echo "  [PASS-FIXED] $rel (-O0 & -O2)"
      PASS=$((PASS + 1))
    else
      echo "  [REGRESSION] $rel failed!"
      cat "$WORK/${slug}_O0.log" "$WORK/${slug}_O2.log" 2>/dev/null || true
      FAIL=$((FAIL + 1))
    fi
  done
fi

if [[ -d "$PLFH_ROOT/reproducers" ]]; then
  echo ""
  echo "--- Minimal Blocker Reproducers (open compiler gaps) ---"
  REPRO_BUILD_O0="$WORK/repro-O0"
  REPRO_BUILD_O2="$WORK/repro-O2"
  mkdir -p "$REPRO_BUILD_O0" "$REPRO_BUILD_O2"
  mapfile -t REPROS < <(find "$PLFH_ROOT/reproducers" -maxdepth 1 -name '*.hs' 2>/dev/null | sort)
  for rep in "${REPROS[@]}"; do
    rel=${rep#"$PLFH_ROOT/"}
    slug=$(echo "$rel" | tr '/.' '__')
    if [[ "$(basename "$rep")" == ReproOps* ]]; then
      continue
    fi
    if "${GHC_CMD[@]}" --make -v0 -O0 \
      -fomit-interface-pragmas -fno-write-if-simplified-core \
      -dcore-lint -dstg-lint \
      -package-env - "${INCLUDES[@]}" "-i$PLFH_ROOT/reproducers" \
      -outputdir "$REPRO_BUILD_O0" "$rep" >"$WORK/${slug}_O0.log" 2>&1; then
      if "${GHC_CMD[@]}" --make -v0 -O2 \
        -fomit-interface-pragmas -fno-write-if-simplified-core \
        -dcore-lint -dstg-lint \
        -package-env - "${INCLUDES[@]}" "-i$PLFH_ROOT/reproducers" \
        -outputdir "$REPRO_BUILD_O2" "$rep" >"$WORK/${slug}_O2.log" 2>&1; then
        echo "  [FIXED?!] $rel now PASSES at -O0 & -O2 — update chapter & PLFH-NOTES.md!"
      else
        first_err=$(rg -m1 'Core Lint errors|panic!|error: \[GHC-[0-9]+\]|error:' "$WORK/${slug}_O2.log" || head -n 1 "$WORK/${slug}_O2.log")
        echo "  [BLOCKED-O2] $rel (passes -O0, blocked at -O2) — $first_err"
      fi
    else
      first_err=$(rg -m1 'Core Lint errors|panic!|error: \[GHC-[0-9]+\]|error:' "$WORK/${slug}_O0.log" || head -n 1 "$WORK/${slug}_O0.log")
      if rg -q '\[GHC-76037\]|\[GHC-87110\]|\[GHC-61689\]' "$WORK/${slug}_O0.log"; then
        echo "  [HARNESS-FAIL] $rel failed with import/scope error — $first_err"
        FAIL=$((FAIL + 1))
      else
        echo "  [BLOCKED] $rel — $first_err"
      fi
    fi
  done
fi

echo ""
echo "Summary: $PASS passed, $FAIL failed."
exit $FAIL
