#!/usr/bin/env bash
# Verify extracted PLFH chapters, interface soundness, negative controls,
# and runtime smoke tests using the Dependent Haskell GHC fork.
#
# On this host (when ghc-build-job is present and PLFH_NO_PUEUE != 1), submits the entire
# verification suite as ONE job to the shared pueue queue so it completes in a single slot.
#
# Environment variables:
#   PLFH_GHC            Path to stage1/bin/ghc from TharkunAB/ghc
#   PLFH_GHC_LIBDIR     Optional -B<libdir>
#   PLFH_GHC_REPO       Path to TharkunAB/ghc checkout (for _build/current & ghc-build-job)
#   PLFH_DEPENDENT_BASE Path to TharkunAB/dependent-base src/ (defaults to sibling checkout or reference/dependent-base)
#   PLFH_NO_PUEUE       Set to 1 to run ghc directly instead of via ghc-build-job / pueue
set -euo pipefail
export LC_ALL=C

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
PLFH_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
GHC_REPO=${PLFH_GHC_REPO:-/home/tritlo/Code/ghc}

# Prefer the consolidated verified Stage 1 build under _build/current/
# requiring at least Wave 18b consolidated (`d97fedfd48`).
CURRENT_PASS="$GHC_REPO/_build/current/verified.pass"
CURRENT_GHC="$GHC_REPO/_build/current/source/_build/stage1/bin/ghc"
CURRENT_LIB="$GHC_REPO/_build/current/source/_build/stage1/lib"
CURRENT_SRC="$GHC_REPO/_build/current/compiler.source"
WAVE18_REV="d97fedfd48b57be36accb610d5bdc2fd0ce26c5a"

DEFAULT_COMPILER=""
DEFAULT_LIBDIR=""
if [[ -f "$CURRENT_PASS" && -x "$CURRENT_GHC" && -f "$CURRENT_SRC" ]] \
   && git -C "$GHC_REPO" merge-base --is-ancestor "$WAVE18_REV" "$(cat "$CURRENT_SRC" 2>/dev/null)" 2>/dev/null; then
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

GHC_BUILD_JOB=""
if [[ -x "/home/tritlo/Code/heavy-management/bin/ghc-build-job" ]]; then
  GHC_BUILD_JOB="/home/tritlo/Code/heavy-management/bin/ghc-build-job"
elif [[ -x "$GHC_REPO/docs/dependent-haskell/tools/ghc-build-job" ]]; then
  GHC_BUILD_JOB="$GHC_REPO/docs/dependent-haskell/tools/ghc-build-job"
fi

if [[ "${PLFH_NO_PUEUE:-0}" != "1" ]] && [[ -n "$GHC_BUILD_JOB" ]]; then
  jid=$(cd "$GHC_REPO" && CAPPED_MEM=5G "$GHC_BUILD_JOB" plfh-suite \
    /usr/bin/env "PLFH_NO_PUEUE=1" "PLFH_GHC=$COMPILER" "PLFH_GHC_LIBDIR=$GHC_LIBDIR" "PLFH_GHC_REPO=$GHC_REPO" "PLFH_DEPENDENT_BASE=${PLFH_DEPENDENT_BASE:-}" \
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

DEPENDENT_BASE_SRC=${PLFH_DEPENDENT_BASE:-}
if [[ -z "$DEPENDENT_BASE_SRC" ]]; then
  if [[ -d "/home/tritlo/Code/dependent-base/src" ]]; then
    DEPENDENT_BASE_SRC="/home/tritlo/Code/dependent-base/src"
  else
    DEPENDENT_BASE_SRC="$PLFH_ROOT/reference/dependent-base"
  fi
fi

if [[ ! -d "$DEPENDENT_BASE_SRC" ]]; then
  echo "ERROR: dependent-base source directory not found at: $DEPENDENT_BASE_SRC" >&2
  exit 2
fi

INCLUDES=(
  "-package" "base"
  "-package" "ghc-experimental"
  "-package" "ghc-internal"
  "-i"
  "-i$DEPENDENT_BASE_SRC"
  "-i$PLFH_ROOT/hs"
)

BUILD_DIR="$WORK/build"
mkdir -p "$BUILD_DIR"

PASS=0
FAIL=0

echo "--- Checked Modules (native + Core/STG Lint) ---"
mapfile -t MODULES < <(find "$PLFH_ROOT/hs/PLFH" -name '*.hs' 2>/dev/null | sort)
for mod in "${MODULES[@]}"; do
  rel=${mod#"$PLFH_ROOT/"}
  slug=$(echo "$rel" | tr '/.' '__')
  if "${GHC_CMD[@]}" --make -v0 \
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
if runhaskell --ghc-arg=-package-env=- "$SCRIPT_DIR/audit_ifaces.hs" "$COMPILER" "$BUILD_DIR"; then
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
  if "${GHC_CMD[@]}" --make -v0 \
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
  if "${GHC_CMD[@]}" --make -v0 \
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

echo ""
echo "Summary: $PASS passed, $FAIL failed."
exit $FAIL
