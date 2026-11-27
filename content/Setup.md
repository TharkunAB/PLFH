---
title: "Setup: Building Dependent Haskell GHC"
description: "Build the Dependent Haskell GHC 10.1 fork (TharkunAB/ghc), install dependent-base and plugins via dependent.head.hackage, and use -XDependentTypes in GHCi."
prev: /preface/
next: /naturals/
src: content/Setup.md
---

PLFH compiles against the Dependent Haskell fork of GHC
([`TharkunAB/ghc`](https://github.com/TharkunAB/ghc/tree/dependent-haskell),
branch `dependent-haskell`, tag `dependent-haskell-alpha`, GHC `10.1`). You can
run every chapter and example directly in your browser on this site, or build
the compiler locally to work from the command line and GHCi. If you discover a
compiler bug or unexpected behavior, please
[file an issue on `TharkunAB/ghc`](https://github.com/TharkunAB/ghc/issues).

## Prerequisites

To build GHC from source you need:

- A bootstrap GHC (`>= 9.12`, for example `9.14.1` via `ghcup`),
  `cabal-install` (`>= 3.14`), `alex`, and `happy`.
- Standard GHC build tools: `autoconf`, `automake`, `make`, `gcc`, `gmp`,
  `libffi`, `ncurses`, `python3`, and `git`.

If you use Nix, the repository provides a
[`shell.nix`](https://github.com/TharkunAB/PLFH/blob/main/shell.nix) with these
bootstrap tools preinstalled (`nix-shell`).

## Compiling the Dependent Haskell GHC fork

Clone the `dependent-haskell` branch with its Git submodules, then configure
and build with Hadrian:

```bash
git clone --recursive -b dependent-haskell https://github.com/TharkunAB/ghc.git
cd ghc
./boot
./configure
hadrian/build -j --flavour=quick --docs=none
```

When Hadrian finishes:

- The stage-1 compiler is at `_build/stage0/bin/ghc`.
- The self-hosted stage-2 compiler is at `_build/stage1/bin/ghc`, with its
  libraries in `_build/stage1/lib`.

Check the build:

```bash
_build/stage1/bin/ghc --version
```

## Companion libraries and plugins

Three companion repositories work with this compiler:

- [`TharkunAB/dependent-base`](https://github.com/TharkunAB/dependent-base):
  standard library (`Prelude.Dependent`, `Data.Function.Dependent`,
  `Data.Nat.Dependent`, `Data.List.Dependent`, `Data.Vec.Dependent`,
  `Data.Fin.Dependent`, `Data.Sigma.Dependent`, `Data.Exists.Dependent`,
  `Data.Type.Equality.Dependent`, `Data.Decision`).
- [`TharkunAB/dependent-proof-search`](https://github.com/TharkunAB/dependent-proof-search):
  hole-fit plugin (`-fplugin=Dependent.Plugin.ProofSearch`) for congruence and
  transitivity subgoal refinements and bounded proof search.
- [`TharkunAB/dependent-obs-eq`](https://github.com/TharkunAB/dependent-obs-eq):
  typechecker plugin (`-fplugin=Dependent.Plugin.ObsEq`, idea by Jules
  `@analytichegel`) for QuickCheck observational-equality testing and
  counterexample shrinking.

## Installing packages with `dependent.head.hackage` {#dependent-hackage}

The [`TharkunAB/dependent-hackage`](https://github.com/TharkunAB/dependent-hackage)
repository publishes a TUF-signed static Hackage overlay at
`https://cdn.tharkun.se/dependent-hackage/`. It layers `dependent-base`,
`dependent-proof-search`, `dependent-obs-eq`, GHC `10.1` compatibility patches,
and patched ecosystem tools (`fourmolu`, `cabal-gild`, `ghc-exactprint`) on top
of Hackage and `head.hackage`.

Add both overlays to your `cabal.project`:

```cabal
repository head.hackage.ghc.haskell.org
  url: https://ghc.gitlab.haskell.org/head.hackage/
  secure: True
  key-threshold: 3
  root-keys:
    f76d08be13e9a61a377a85e2fb63f4c5435d40f8feb3e12eb05905edb8cdea89
    26021a13b401500c8eb2761ca95c61f2d625bfef951b939a8124ed12ecf07329
    7541f32a4ccca4f97aea3b22f5e593ba2c0267546016b992dfadcd2fe944e55d

repository dependent.head.hackage
  url: https://cdn.tharkun.se/dependent-hackage/
  secure: True
  key-threshold: 3
  root-keys:
    1ad4d9522ed07750746d4c5fca5fe2dc72f47ba643f9eb337a7b332cb50db4c3
    650abe1aaf95bfe819c0b6d5f41f756ac71652ea3e62064ad4eb00805bcec45d
    fc14639fb76e8b8d3e6b9fcfbdc16c8a095483438642a8291a6da37c8d9643cb

active-repositories:
  hackage.haskell.org,
  head.hackage.ghc.haskell.org:merge,
  dependent.head.hackage:override
```

Fetch the overlay index and build with your stage-2 compiler:

```bash
cabal update dependent.head.hackage
cabal build -w /path/to/ghc/_build/stage1/bin/ghc
```

## Language extension and flags

Every Dependent Haskell module in PLFH starts with one umbrella pragma
(following GHC Proposals `#378` and `#102`):

```haskell
{-# LANGUAGE DependentTypes #-}
```

No extra interface or optimization flags are required: modules compile with
plain `ghc`, `ghc -O2`, or `ghc --interactive`.

`-XDependentTypes` enables retained dependent binders (`foreach (m n p :: T) ->
...`, or `∏` with `-XUnicodeSyntax`), open and closed evaluation of ordinary
Haskell functions in types, automatic source-equation publication in `.hi`
interfaces, type-level `let`/`case`/lambdas, and `exists`/`some` syntax. It
implies `GADTs`, `DataKinds`, `PolyKinds`, `TypeOperators`, `RankNTypes`,
`ScopedTypeVariables`, `TypeApplications`, `TypeAbstractions`,
`StandaloneKindSignatures`, `EmptyCase`, `Modifiers`, `RequiredTypeArguments`,
`ExplicitNamespaces`, and `NoListTuplePuns` (so `[]` and `:` work in types
without leading ticks; modules that write `(a, b)` or `[a]` in types add
`ListTuplePuns` after `DependentTypes`).

Useful optional flags:

- `-freport-totality`: opt-in advisory structural totality checking.
- `-frefinement-level-hole-fits=2 -fabstract-refinement-hole-fits`: refinement
  hole fits for interactive typed-hole proofs.
- `-fplugin=Dependent.Plugin.ProofSearch`: bounded proof search and subgoal
  refinements on typed holes.
- `-fplugin=Dependent.Plugin.ObsEq`: observational-equality testing on open
  uninterpreted function calls.

## Running Dependent Haskell in GHCi

Start the stage-2 compiler with `dependent-base` and PLFH on the search path:

```bash
_build/stage1/bin/ghc --interactive \
  -package base -package ghc-experimental -package ghc-internal \
  -i -i/path/to/dependent-base/src \
  -i/path/to/PLFH/hs
```

At the prompt:

```text
ghci> :seti -XDependentTypes
ghci> :load PLFH.Part1.Induction
ghci> :t plusComm
```

## Using the in-browser GHCi (WebAssembly)

Every chapter page, the [Overview](/overview/), and the
[Playground](/playground/) include an in-browser `wasm32-wasi` GHCi session. It
loads lazily on your first click, caches the compiler bundle in your browser,
and ships with `dependent-base`, `dependent-obs-eq`, `Dependent.Plugin.ObsEq`,
`Dependent.Plugin.ProofSearch`, `transformers`, `mtl`, and all 25 PLFH chapters
precompiled.

In any editable code block, write a typed hole (`_` or `_qed`) and press
`Ctrl/Cmd+Enter`. GHC highlights verified code using `RenamedSource` semantic
tokens, marks typed holes in green goal boxes, and displays clickable case-split
and hole-fit chips.
