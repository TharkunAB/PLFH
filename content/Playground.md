---
title: "Dependent Haskell Playground"
description: "Write, typecheck, fill typed holes, and evaluate Dependent Haskell (-XDependentTypes) in your browser via WebAssembly GHC 10.1."
prev: /Overview/
next: /
src: content/Playground.md
playground: true
---

Experiment with Dependent Haskell (`-XDependentTypes`, GHC `10.1` from
[`TharkunAB/ghc`](https://github.com/TharkunAB/ghc/tree/dependent-haskell))
directly in your browser through WebAssembly. The session preloads
[`dependent-base`](/DependentBase/),
[`dependent-obs-eq`](https://github.com/TharkunAB/dependent-obs-eq)
(`Dependent.ObsEq` and `Dependent.Plugin.ObsEq`),
[`dependent-proof-search`](https://github.com/TharkunAB/dependent-proof-search)
(`Dependent.Plugin.ProofSearch`), `transformers`, `mtl`, and all 25 `PLFH.*`
chapter modules.

Pick a preset below or write your own module, then press **`Ctrl/Cmd+Enter`**
or click **Check & Load in GHCi**. Like Emacs `agda-mode`, edited code dims
until GHC checks it, then lights up with `RenamedSource` semantic colors, green
typed-hole goal boxes, and red error spans.

- Select **Routes & Monad Stack** to run type-safe web routes as ordinary
  values paired with runtime-selected `transformers` stacks.
- Select **Agda-mode & ProofSearch** (or replace any proof with `_`) to split
  stuck equations across constructors, refine subgoals step by step (`cong Succ
  _`), or synthesize proofs with `Dependent.Plugin.ProofSearch`.
- Select **Observational Equality (ObsEq)** to check non-structural functions
  with `Dependent.Plugin.ObsEq`, or break an equation to see a shrunk
  counterexample.
- Use the `ghci>` prompt below the editor for `:t`, `:k!`, `:i`,
  `:browse Prelude.Dependent`, or runtime evaluation.

<div id="plfh-standalone-playground" class="plfh-playground-root"></div>

See the [Dependent Haskell Overview](/Overview/) for the guided walkthrough,
proposals, and papers, or browse [`dependent-base`](/DependentBase/) and the
[Source Browser](/Source/).
