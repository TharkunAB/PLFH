#!/usr/bin/env bash
# Stage a locally built wasm32-wasi Dependent GHCi browser bundle into wasm/
# (for local Hakyll preview) or publish rootfs.tar.gz to GitHub Release `wasm-latest`.
#
# Usage:
#   bash scripts/stage_wasm_bundle.sh [BUNDLE_DIR] [--publish-release]
#
# Default BUNDLE_DIR:
#   /home/tritlo/Code/ghc/_build/on-demand/wasm-spike-20261124/plfh-browser-bundle
set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
PLFH_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
DEFAULT_BUNDLE="/home/tritlo/Code/ghc/_build/on-demand/wasm-spike-20261124/plfh-browser-bundle"

BUNDLE_DIR="$DEFAULT_BUNDLE"
PUBLISH_RELEASE=0

for arg in "$@"; do
  case "$arg" in
    --publish-release)
      PUBLISH_RELEASE=1
      ;;
    *)
      BUNDLE_DIR="$arg"
      ;;
  esac
done

ROOTFS="$BUNDLE_DIR/rootfs.tar.gz"
if [[ ! -f "$ROOTFS" ]]; then
  echo "ERROR: $ROOTFS does not exist yet." >&2
  echo "Wait for the wasm32-wasi build to finish, then re-run this script." >&2
  exit 1
fi

mkdir -p "$PLFH_ROOT/wasm"

# Refresh vendored GHC Wasm runtime shims if present in the bundle directory.
for shim in browser_wasi_shim.mjs dyld.mjs post-link.mjs prelude.mjs; do
  if [[ -f "$BUNDLE_DIR/$shim" ]]; then
    cp -f "$BUNDLE_DIR/$shim" "$PLFH_ROOT/wasm/$shim"
  fi
done

cp -f "$ROOTFS" "$PLFH_ROOT/wasm/rootfs.tar.gz"
echo "Staged $PLFH_ROOT/wasm/rootfs.tar.gz ($(du -h "$PLFH_ROOT/wasm/rootfs.tar.gz" | cut -f1))"

if [[ "$PUBLISH_RELEASE" -eq 1 ]]; then
  echo "Publishing rootfs.tar.gz to GitHub Release wasm-latest on Tritlo/PLFH..."
  if gh release view wasm-latest -R Tritlo/PLFH >/dev/null 2>&1; then
    gh release upload wasm-latest "$PLFH_ROOT/wasm/rootfs.tar.gz" -R Tritlo/PLFH --clobber
  else
    gh release create wasm-latest "$PLFH_ROOT/wasm/rootfs.tar.gz" \
      -R Tritlo/PLFH \
      --title "PLFH Dependent GHCi Wasm Bundle (latest)" \
      --notes "Prebuilt wasm32-wasi Dependent Haskell GHCi 10.1 rootfs (libplfh_ghci.so + HaskLib + precompiled plfh-book-0.1)."
  fi
  echo "Published! Trigger or push to main to deploy _site/wasm/rootfs.tar.gz to GitHub Pages."
fi
