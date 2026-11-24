#!/usr/bin/env bash
# Verify extracted PLFH chapters, negative controls, and minimal compiler-bug reproducers
# using the Dependent Haskell GHC fork.
#
# On this host (when ghc-build-job is present and PLFH_NO_PUEUE != 1), submits the entire
# verification suite as ONE job to the shared pueue queue so it completes in a single slot.
#
# Environment variables:
#   PLFH_GHC       Path to stage1/bin/ghc from Tritlo/ghc (dependent-haskell)
#   PLFH_GHC_REPO  Path to Tritlo/ghc checkout (for HaskLib & ghc-build-job)
#   PLFH_NO_PUEUE  Set to 1 to run ghc directly instead of via ghc-build-job / pueue
set -euo pipefail
export LC_ALL=C

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
PLFH_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
GHC_REPO=${PLFH_GHC_REPO:-/home/tritlo/Code/ghc}
DEFAULT_COMPILER="$GHC_REPO/_build/on-demand/r04-r16-r17-post-585-20261123/source/_build/stage1/bin/ghc"
if ! [[ -x "$DEFAULT_COMPILER" ]]; then
  DEFAULT_COMPILER="$GHC_REPO/_build/on-demand/r04-r05-r17-combined-584-20261123/source/_build/stage1/bin/ghc"
fi
COMPILER=${PLFH_GHC:-$DEFAULT_COMPILER}

if [[ "${PLFH_NO_PUEUE:-0}" != "1" ]] && [[ -x "$GHC_REPO/docs/dependent-haskell/tools/ghc-build-job" ]]; then
  jid=$(cd "$GHC_REPO" && CAPPED_MEM=4G docs/dependent-haskell/tools/ghc-build-job plfh-suite \
    /usr/bin/env "PLFH_NO_PUEUE=1" "PLFH_GHC=$COMPILER" "PLFH_GHC_REPO=$GHC_REPO" \
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

COMMIT=$("$COMPILER" --info | awk -F'"' '/Project Git commit id/{print $4}')
VERSION=$("$COMPILER" --info | awk -F'"' '/Project version/{print $4}')
echo "=== PLFH Verification ==="
echo "Compiler: $COMPILER"
echo "Version:  $VERSION"
echo "Commit:   $COMMIT"
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

INCLUDES=(
  "-i"
  "-i$GHC_REPO/docs/dependent-haskell/hasklib"
  "-i$GHC_REPO/docs/dependent-haskell/examples/open-evaluation"
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
  if "$COMPILER" --make -v0 -O0 \
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
echo "--- Negative Controls (must fail with expected diagnostic) ---"
mapfile -t NEGS < <(find "$PLFH_ROOT/hs/negative" -name '*.hs' 2>/dev/null | sort)
for neg in "${NEGS[@]}"; do
  rel=${neg#"$PLFH_ROOT/"}
  slug=$(echo "$rel" | tr '/.' '__')
  expect=$(awk '/^-- EXPECT-ERROR:/{print $3; exit}' "$neg")
  if "$COMPILER" --make -v0 -O0 \
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

if [[ -d "$PLFH_ROOT/reproducers" ]]; then
  echo ""
  echo "--- Minimal Blocker Reproducers (tracking compiler gaps) ---"
  REPRO_BUILD="$WORK/repro-build"
  mkdir -p "$REPRO_BUILD"
  mapfile -t REPROS < <(find "$PLFH_ROOT/reproducers" -name '*.hs' 2>/dev/null | sort)
  for rep in "${REPROS[@]}"; do
    rel=${rep#"$PLFH_ROOT/"}
    slug=$(echo "$rel" | tr '/.' '__')
    if [[ "$(basename "$rep")" == ReproOps* ]]; then
      continue
    fi
    if "$COMPILER" --make -v0 -O0 \
      -fomit-interface-pragmas -fno-write-if-simplified-core \
      -dcore-lint -dstg-lint \
      -package-env - "${INCLUDES[@]}" "-i$PLFH_ROOT/reproducers" \
      -outputdir "$REPRO_BUILD" "$rep" >"$WORK/$slug.log" 2>&1; then
      echo "  [FIXED?!] $rel now PASSES — update chapter & PLFH-NOTES.md!"
    else
      first_err=$(rg -m1 'Core Lint errors|panic!|error: \[GHC-[0-9]+\]|error:' "$WORK/$slug.log" || head -n 1 "$WORK/$slug.log")
      echo "  [BLOCKED] $rel — $first_err"
    fi
  done
fi

echo ""
echo "Summary: $PASS passed, $FAIL failed."
exit $FAIL
