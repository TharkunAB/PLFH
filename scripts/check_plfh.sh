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

# Prefer the consolidated verified normal stage1 build under _build/current/
# once it includes Wave 8+9A consolidated (`f0c3001e54`), otherwise prefer the
# verified wave8-two-stage Stage 1 build or the wave8-consolidated component
# (`f0c3001e54`), falling back to Wave 5+6 consolidated (`91a63517fc`).
CURRENT_PASS="$GHC_REPO/_build/current/verified.pass"
CURRENT_GHC="$GHC_REPO/_build/current/source/_build/stage1/bin/ghc"
CURRENT_LIB="$GHC_REPO/_build/current/source/_build/stage1/lib"
CURRENT_HASKLIB="$GHC_REPO/_build/current/source/docs/dependent-haskell/hasklib"
CURRENT_SRC="$GHC_REPO/_build/current/compiler.source"
WAVE8_REV="f0c3001e54db37adc2aaa1887778e0b6281a0317"
WAVE8_TWOSTAGE_PASS="$GHC_REPO/_build/on-demand/wave8-two-stage/qualified.pass"
WAVE8_TWOSTAGE_GHC="$GHC_REPO/_build/on-demand/wave8-two-stage/source/_build/stage1/bin/ghc"
WAVE8_TWOSTAGE_LIB="$GHC_REPO/_build/on-demand/wave8-two-stage/source/_build/stage1/lib"
WAVE8_TWOSTAGE_HASKLIB="$GHC_REPO/_build/on-demand/wave8-two-stage/source/docs/dependent-haskell/hasklib"
WAVE8_TWOSTAGE_OPENEVAL="$GHC_REPO/_build/on-demand/wave8-two-stage/source/docs/dependent-haskell/examples/open-evaluation"
WAVE8_GHC="$GHC_REPO/_build/on-demand/wave8-consolidated/component/ghc"
WAVE8_LIB="$GHC_REPO/_build/on-demand/wave8-consolidated/component/lib"
WAVE8_HASKLIB="$GHC_REPO/_build/on-demand/wave8-consolidated/source/docs/dependent-haskell/hasklib"
WAVE8_OPENEVAL="$GHC_REPO/_build/on-demand/wave8-consolidated/source/docs/dependent-haskell/examples/open-evaluation"
WAVE56_REV="91a63517fc25c63f96967d2faf159f2baca98bed"
WAVE56_GHC="$GHC_REPO/_build/on-demand/wave5-6-consolidated/component/ghc"
WAVE56_LIB="$GHC_REPO/_build/on-demand/wave5-6-consolidated/component/lib"
WAVE56_HASKLIB="$GHC_REPO/_build/on-demand/wave5-6-consolidated/source/docs/dependent-haskell/hasklib"
WAVE56_OPENEVAL="$GHC_REPO/_build/on-demand/wave5-6-consolidated/source/docs/dependent-haskell/examples/open-evaluation"
WAVE34A_GHC="$GHC_REPO/_build/on-demand/wave3-4a-consolidated/component/ghc"
WAVE34A_LIB="$GHC_REPO/_build/on-demand/wave3-4a-consolidated/component/lib"
WAVE34A_HASKLIB="$GHC_REPO/_build/on-demand/wave3-4a-consolidated/source/docs/dependent-haskell/hasklib"
WAVE34A_OPENEVAL="$GHC_REPO/_build/on-demand/wave3-4a-consolidated/source/docs/dependent-haskell/examples/open-evaluation"
WAVE4_GHC="$GHC_REPO/_build/on-demand/wave4-preview/component/ghc"
WAVE4_LIB="$GHC_REPO/_build/on-demand/wave4-preview/component/lib"
WAVE2C_GHC="$GHC_REPO/_build/on-demand/wave2-consolidated/component/ghc"
WAVE2C_LIB="$GHC_REPO/_build/on-demand/wave2-consolidated/component/lib"
WAVE2_GHC="$GHC_REPO/_build/on-demand/wave2-preview/component/ghc"
WAVE2_LIB="$GHC_REPO/_build/on-demand/wave2-preview/component/lib"
WAVE1_GHC="$GHC_REPO/_build/on-demand/wave1-consolidated/component/ghc"
WAVE1_LIB="$GHC_REPO/_build/on-demand/wave1-consolidated/component/lib"

DEFAULT_COMPILER=""
DEFAULT_LIBDIR=""
DEFAULT_HASKLIB=""
DEFAULT_OPENEVAL=""
if [[ -f "$CURRENT_PASS" && -x "$CURRENT_GHC" && -f "$CURRENT_SRC" ]] \
   && git -C "$GHC_REPO" merge-base --is-ancestor "$WAVE8_REV" "$(cat "$CURRENT_SRC" 2>/dev/null)" 2>/dev/null; then
  DEFAULT_COMPILER="$CURRENT_GHC"
  DEFAULT_LIBDIR="$CURRENT_LIB"
  DEFAULT_HASKLIB="$CURRENT_HASKLIB"
  DEFAULT_OPENEVAL="$GHC_REPO/_build/current/source/docs/dependent-haskell/examples/open-evaluation"
elif [[ -f "$WAVE8_TWOSTAGE_PASS" && -x "$WAVE8_TWOSTAGE_GHC" ]]; then
  DEFAULT_COMPILER="$WAVE8_TWOSTAGE_GHC"
  DEFAULT_LIBDIR="$WAVE8_TWOSTAGE_LIB"
  DEFAULT_HASKLIB="$WAVE8_TWOSTAGE_HASKLIB"
  DEFAULT_OPENEVAL="$WAVE8_TWOSTAGE_OPENEVAL"
elif [[ -x "$WAVE8_GHC" ]]; then
  DEFAULT_COMPILER="$WAVE8_GHC"
  DEFAULT_LIBDIR="$WAVE8_LIB"
  if find -L "$WAVE8_LIB" -name 'Exists.hi' 2>/dev/null | grep -q .; then
    DEFAULT_HASKLIB="$WAVE8_HASKLIB"
    DEFAULT_OPENEVAL="$WAVE8_OPENEVAL"
  else
    # Wave 8C HaskLib.Sigma imports GHC.Exists, which lives in Stage 1 base
    # once wave8-two-stage promotes _build/current.
    DEFAULT_HASKLIB="$WAVE56_HASKLIB"
    DEFAULT_OPENEVAL="$WAVE56_OPENEVAL"
  fi
elif [[ -f "$CURRENT_PASS" && -x "$CURRENT_GHC" && -f "$CURRENT_SRC" ]] \
   && git -C "$GHC_REPO" merge-base --is-ancestor "$WAVE56_REV" "$(cat "$CURRENT_SRC" 2>/dev/null)" 2>/dev/null; then
  DEFAULT_COMPILER="$CURRENT_GHC"
  DEFAULT_LIBDIR="$CURRENT_LIB"
elif [[ -x "$WAVE56_GHC" ]]; then
  DEFAULT_COMPILER="$WAVE56_GHC"
  DEFAULT_LIBDIR="$WAVE56_LIB"
  DEFAULT_HASKLIB="$WAVE56_HASKLIB"
  DEFAULT_OPENEVAL="$WAVE56_OPENEVAL"
elif [[ -x "$WAVE34A_GHC" ]]; then
  DEFAULT_COMPILER="$WAVE34A_GHC"
  DEFAULT_LIBDIR="$WAVE34A_LIB"
  DEFAULT_HASKLIB="$WAVE34A_HASKLIB"
  DEFAULT_OPENEVAL="$WAVE34A_OPENEVAL"
elif [[ -x "$WAVE4_GHC" ]]; then
  DEFAULT_COMPILER="$WAVE4_GHC"
  DEFAULT_LIBDIR="$WAVE4_LIB"
elif [[ -x "$WAVE2C_GHC" ]]; then
  DEFAULT_COMPILER="$WAVE2C_GHC"
  DEFAULT_LIBDIR="$WAVE2C_LIB"
elif [[ -x "$WAVE2_GHC" ]]; then
  DEFAULT_COMPILER="$WAVE2_GHC"
  DEFAULT_LIBDIR="$WAVE2_LIB"
elif [[ -x "$WAVE1_GHC" ]]; then
  DEFAULT_COMPILER="$WAVE1_GHC"
  DEFAULT_LIBDIR="$WAVE1_LIB"
elif [[ -f "$CURRENT_PASS" && -x "$CURRENT_GHC" ]]; then
  DEFAULT_COMPILER="$CURRENT_GHC"
  DEFAULT_LIBDIR="$CURRENT_LIB"
elif [[ -x "$CURRENT_GHC" ]]; then
  DEFAULT_COMPILER="$CURRENT_GHC"
  DEFAULT_LIBDIR="$CURRENT_LIB"
else
  DEFAULT_COMPILER="$GHC_REPO/_build/stage1/bin/ghc"
fi

COMPILER=${PLFH_GHC:-$DEFAULT_COMPILER}
GHC_LIBDIR=${PLFH_GHC_LIBDIR:-}
if [[ -z "$GHC_LIBDIR" ]] && [[ "$COMPILER" == "$DEFAULT_COMPILER" ]]; then
  GHC_LIBDIR="$DEFAULT_LIBDIR"
fi

if [[ "${PLFH_NO_PUEUE:-0}" != "1" ]] && [[ -x "$GHC_REPO/docs/dependent-haskell/tools/ghc-build-job" ]]; then
  jid=$(cd "$GHC_REPO" && CAPPED_MEM=5G docs/dependent-haskell/tools/ghc-build-job plfh-suite \
    /usr/bin/env "PLFH_NO_PUEUE=1" "PLFH_GHC=$COMPILER" "PLFH_GHC_LIBDIR=$GHC_LIBDIR" "PLFH_GHC_REPO=$GHC_REPO" "PLFH_HASKLIB=${PLFH_HASKLIB:-}" \
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
if [[ "$COMPILER" == "$CURRENT_GHC" ]]; then
  CURRENT_REV=$(cat "$GHC_REPO/_build/current/compiler.source" 2>/dev/null || echo "$COMMIT")
  echo "Commit:   $CURRENT_REV (consolidated _build/current stage1; ghc --info: $COMMIT)"
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
  if [[ -n "$DEFAULT_HASKLIB" && "$COMPILER" == "$DEFAULT_COMPILER" && -d "$DEFAULT_HASKLIB" ]]; then
    HASKLIB_SRC="$DEFAULT_HASKLIB"
    if [[ -d "$DEFAULT_OPENEVAL" ]]; then
      OPEN_EVAL_SRC="$DEFAULT_OPENEVAL"
    fi
  elif [[ "$COMPILER" == *r17-schema-transformer-post-588* ]] && [[ -d "$GHC_REPO/_build/on-demand/hasklib-book-nat-rewrite-20261124/source/docs/dependent-haskell/hasklib" ]]; then
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
