#!/usr/bin/env bash
# Upload the wasm32-wasi Dependent GHCi rootfs to Cloudflare R2 and update
# the GitHub Pages PLFH_WASM_ROOTFS_URL repository variable.
#
# Each upload uses a content-addressed key (plfh/rootfs-<sha256-12>.tar.gz)
# so Cloudflare edge caching and the browser Cache API stay immutable and
# automatically refresh whenever a new compiler bundle ships.
#
# Usage:
#   ./release.sh [BUNDLE_DIR_OR_TARBALL] [--force] [--deploy] [--dry-run]
#                [--no-sync-shims] [--no-gh-var]
set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)

DEFAULT_SOURCE="${PLFH_WASM_BUNDLE:-/home/tritlo/Code/ghc/_build/on-demand/wasm-spike-20261124/plfh-browser-bundle}"
BUCKET="${PLFH_R2_BUCKET:-tharkun-cdn}"
CDN_BASE="${PLFH_CDN_BASE:-https://cdn.tharkun.se}"
KEY_PREFIX="${PLFH_R2_PREFIX:-plfh}"
GH_REPO="${PLFH_GH_REPO:-Tritlo/PLFH}"
SITE_ORIGIN="${PLFH_SITE_ORIGIN:-https://plfh.tharkun.se}"

SOURCE="$DEFAULT_SOURCE"
FORCE=0
DEPLOY=0
DRY_RUN=0
SYNC_SHIMS=1
SET_GH_VAR=1

for arg in "$@"; do
  case "$arg" in
    --force)          FORCE=1 ;;
    --deploy)         DEPLOY=1 ;;
    --dry-run)        DRY_RUN=1 ;;
    --no-sync-shims)  SYNC_SHIMS=0 ;;
    --no-gh-var)      SET_GH_VAR=0 ;;
    -h|--help)
      sed -n '2,12p' "$0" | sed 's/^# \{0,1\}//'
      exit 0
      ;;
    -*)
      echo "ERROR: unknown option: $arg" >&2
      exit 2
      ;;
    *)
      SOURCE="$arg"
      ;;
  esac
done

BUNDLE_DIR=""
if [[ -d "$SOURCE" ]]; then
  BUNDLE_DIR="$SOURCE"
  ROOTFS="$SOURCE/rootfs.tar.gz"
elif [[ -f "$SOURCE" ]]; then
  ROOTFS="$SOURCE"
else
  echo "ERROR: source not found: $SOURCE" >&2
  exit 1
fi

if [[ ! -f "$ROOTFS" ]]; then
  echo "ERROR: rootfs tarball not found: $ROOTFS" >&2
  exit 1
fi

HASH=$(sha256sum "$ROOTFS" | cut -c1-12)
SIZE_HUMAN=$(du -h "$ROOTFS" | cut -f1)
OBJECT_KEY="${KEY_PREFIX}/rootfs-${HASH}.tar.gz"
PUBLIC_URL="${CDN_BASE%/}/${OBJECT_KEY}"

echo "Bundle:  $ROOTFS ($SIZE_HUMAN, sha256=${HASH})"
echo "Target:  r2://${BUCKET}/${OBJECT_KEY}"
echo "CDN URL: $PUBLIC_URL"

# 1. Refresh vendored GHC Wasm runtime shims when releasing from a bundle directory.
if [[ -n "$BUNDLE_DIR" && "$SYNC_SHIMS" -eq 1 ]]; then
  updated_shims=()
  for shim in browser_wasi_shim.mjs dyld.mjs post-link.mjs prelude.mjs; do
    src="$BUNDLE_DIR/$shim"
    dst="$SCRIPT_DIR/wasm/$shim"
    if [[ -f "$src" ]] && ! cmp -s "$src" "$dst" 2>/dev/null; then
      if [[ "$DRY_RUN" -eq 1 ]]; then
        echo "[dry-run] cp -f $src $dst"
      else
        cp -f "$src" "$dst"
      fi
      updated_shims+=("$shim")
    fi
  done
  if [[ ${#updated_shims[@]} -gt 0 ]]; then
    echo "Updated shims in wasm/: ${updated_shims[*]} (remember to commit them)."
  fi
fi

# 2. Upload to Cloudflare R2 (skip if identical content-hashed object already exists).
already_live=0
if [[ "$FORCE" -eq 0 ]] && curl -fsSI "$PUBLIC_URL" >/dev/null 2>&1; then
  already_live=1
  echo "CDN already serves $PUBLIC_URL (pass --force to overwrite)."
fi

if [[ "$already_live" -eq 0 ]]; then
  if [[ "$DRY_RUN" -eq 1 ]]; then
    echo "[dry-run] cf r2 objects put \"$OBJECT_KEY\" --bucket-name \"$BUCKET\" --file \"$ROOTFS\" --content-type application/gzip"
  else
    echo "Uploading to R2..."
    cf r2 objects put "$OBJECT_KEY" \
      --bucket-name "$BUCKET" \
      --file "$ROOTFS" \
      --content-type application/gzip
  fi
fi

# 3. Verify public HTTPS reachability and CORS header for the book origin.
if [[ "$DRY_RUN" -eq 0 ]]; then
  echo "Verifying CDN reachability and CORS for $SITE_ORIGIN..."
  headers=$(curl -fsSI -H "Origin: $SITE_ORIGIN" "$PUBLIC_URL")
  if ! grep -qi "^access-control-allow-origin:" <<<"$headers"; then
    echo "ERROR: $PUBLIC_URL did not return an Access-Control-Allow-Origin header for $SITE_ORIGIN." >&2
    printf '%s\n' "$headers" >&2
    exit 1
  fi
  echo "CDN check passed:"
  grep -iE '^(HTTP/|content-type:|content-length:|access-control-allow-origin:|etag:)' <<<"$headers" | sed 's/^/  /'
fi

# 4. Update GitHub Actions repository variable PLFH_WASM_ROOTFS_URL.
if [[ "$SET_GH_VAR" -eq 1 ]]; then
  if [[ "$DRY_RUN" -eq 1 ]]; then
    echo "[dry-run] gh variable set PLFH_WASM_ROOTFS_URL --body \"$PUBLIC_URL\" -R \"$GH_REPO\""
  else
    gh variable set PLFH_WASM_ROOTFS_URL --body "$PUBLIC_URL" -R "$GH_REPO"
    echo "Updated $GH_REPO variable PLFH_WASM_ROOTFS_URL=$PUBLIC_URL"
  fi
fi

# 5. Optionally trigger a GitHub Pages rebuild immediately.
if [[ "$DEPLOY" -eq 1 ]]; then
  if [[ "$DRY_RUN" -eq 1 ]]; then
    echo "[dry-run] gh workflow run pages.yml -R \"$GH_REPO\""
  else
    gh workflow run pages.yml -R "$GH_REPO"
    echo "Triggered pages.yml workflow on $GH_REPO."
  fi
fi
