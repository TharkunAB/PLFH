---
title: "Dependent Haskell Playground"
prev: /Overview/
next: /
src: content/Playground.md
playground: true
---

Experiment with **Dependent Haskell** (`-XDependentTypes`, GHC `10.1` from
[`Tritlo/ghc`](https://github.com/Tritlo/ghc/tree/dependent-haskell)) directly
in your browser via WebAssembly—zero server backend required. All of
[`HaskLib`](/HaskLib/) and every precompiled `PLFH.*` chapter module is
available to import.

- Pick an example below or write your own module, then press **`Ctrl/Cmd+Enter`**
  or click **Check & Load in GHCi**.
- **Try Agda-mode typed holes:** select the **Agda-mode Case Split & Holes**
  preset (or replace any proof with `_`) to split stuck equations across
  constructors, refine proof subgoals step-by-step (`cong Succ _`), or fill
  goals directly via 1-step synthesis (`cong Succ (plusAssoc m n p)`).
- Use the **`ghci>`** prompt below the editor for `:t`, `:k!`, `:i`,
  `:browse HaskLib.Nat`, or runtime evaluation.

<div id="plfh-standalone-playground" class="plfh-playground-root"></div>

See the [Dependent Haskell Overview](/Overview/) for the papers and GHC
proposals behind these features, or browse [`HaskLib`](/HaskLib/) and the
[Source Browser](/Source/) to see what modules are preloaded.
