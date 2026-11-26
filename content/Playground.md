---
title: "Dependent Haskell Playground"
prev: /Overview/
next: /
src: content/Playground.md
playground: true
---

Experiment with **Dependent Haskell** (`-XDependentTypes`, GHC `10.1` from
[`TharkunAB/ghc`](https://github.com/TharkunAB/ghc/tree/dependent-haskell),
tag `dependent-haskell-alpha`) directly in your browser via WebAssembly—zero
server backend required. All of [`dependent-base`](/DependentBase/)
(`Prelude.Dependent`, `Data.*.Dependent`) and every precompiled `PLFH.*`
chapter module is available to import, alongside the
[`Dependent.Plugin.ProofSearch`](https://github.com/TharkunAB/dependent-proof-search)
hole-fit plugin.

- Pick an example below or write your own module, then press **`Ctrl/Cmd+Enter`**
  or click **Check & Load in GHCi**. Like Emacs `agda-mode`, code dims while
  edited and lights up with compiler-exact `RenamedSource` semantic colors,
  green typed-hole goal boxes, and red error spans whenever GHC checks it.
- **Browse the [Roadmap Showcase](/Showcase/):** explore the interactive
  50-card roadmap dependency graph, design decisions, and scrollable live
  walkthrough linking directly to GHC proposals and Serokell roadmap items.
- **Try Agda-mode typed holes & `Dependent.Plugin.ProofSearch`:** select the
  **Agda-mode Case Split & Holes** preset (or replace any proof with `_`) to
  split stuck equations across constructors, refine proof subgoals step-by-step
  (`cong Succ _`, `trans (plusSuc m k) _`), or synthesize proofs directly via
  `Dependent.Plugin.ProofSearch` (`cong Succ (plusAssoc m n p)`).
- **Try runtime `Type` case, dependent `(.)`, `OverloadedRecordDot`, and
  operator sections:** select **Type Case, Record Dot & Sections** to match on
  retained `foreach (a :: Type)` arguments, project dependent fields with
  `.vecItems` and `Sigma` `.second`, and pass sections such as `(x :)` directly
  to `cong`.
- Use the **`ghci>`** prompt below the editor for `:t`, `:k!`, `:i`,
  `:browse Prelude.Dependent`, or runtime evaluation.

<div id="plfh-standalone-playground" class="plfh-playground-root"></div>

See the [Dependent Haskell Overview](/Overview/) for the papers and GHC
proposals behind these features, or browse [`dependent-base`](/DependentBase/)
and the [Source Browser](/Source/) to see what modules are preloaded.
