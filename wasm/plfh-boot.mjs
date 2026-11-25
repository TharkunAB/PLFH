// Bootstrap script for PLFH interactive Dependent Haskell pages.
// Reads module and bundle URLs from <body data-plfh-*> (with optional ?rootfs= override).

import { enhancePlfhPage } from "./plfh-ghci-client.mjs";

const ds = document.body?.dataset || {};
const params = new URLSearchParams(window.location.search);
const rootfsOverride = params.get("rootfs");

const workerUrl = new URL("./plfh-ghci-worker.mjs", import.meta.url).href;
const rootfsUrl =
  rootfsOverride ||
  ds.plfhRootfs ||
  new URL("./rootfs.tar.gz", import.meta.url).href;

window.plfhClient = enhancePlfhPage({
  workerUrl,
  rootfsUrl,
  chapterModule: ds.plfhModule || null,
});
