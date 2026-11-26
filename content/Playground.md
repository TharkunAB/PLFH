---
title: "Dependent Haskell Playground"
description: "Write, typecheck, fill typed holes, and evaluate Dependent Haskell (-XDependentTypes) in your browser via WebAssembly GHC 10.1."
prev: /Overview/
next: /
src: content/Playground.md
playground: true
---

Write, check, and run Dependent Haskell (`-XDependentTypes`, GHC 10.1) in your
browser through WebAssembly. Pick a preset or edit the code, then press
**`Ctrl/Cmd+Enter`** or click **Check & Load in GHCi**.

<div id="plfh-standalone-playground" class="plfh-playground-root"></div>

### Preloaded environment and shortcuts

The WebAssembly session preloads [`dependent-base`](/DependentBase/),
[`dependent-obs-eq`](https://github.com/TharkunAB/dependent-obs-eq),
[`dependent-proof-search`](https://github.com/TharkunAB/dependent-proof-search),
`transformers`, `mtl`, and all 25 `PLFH.*` chapter modules.

- **Agda-mode highlighting:** Edited code dims until GHC checks it, then lights
  up with `RenamedSource` semantic colors, green typed-hole goal boxes, and red
  error spans.
- **Typed holes & ProofSearch:** Select **Agda-mode & ProofSearch** (or replace
  any proof with `_`) to split stuck equations across constructors, refine
  subgoals (`cong Succ _`), or synthesize proofs with
  `Dependent.Plugin.ProofSearch`.
- **Observational Equality (ObsEq):** Select **Observational Equality (ObsEq)**
  to check non-structural functions with `Dependent.Plugin.ObsEq`, or break an
  equation to see a shrunk counterexample.
- **Interactive prompt:** Use `ghci>` below the editor for `:t`, `:k!`, `:i`,
  `:browse Prelude.Dependent`, or runtime evaluation.

See the [Dependent Haskell Overview](/Overview/) for the guided walkthrough, or
browse [`dependent-base`](/DependentBase/) and the [Source Browser](/Source/).
