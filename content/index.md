---
title: "Table of Contents"
src: content/index.md
---

This book is an introduction to programming language theory using
**Dependent Haskell** (`-XDependentTypes` in
[`Tritlo/ghc`, branch `dependent-haskell`](https://github.com/Tritlo/ghc/tree/dependent-haskell)),
adapted from Philip Wadler, Wen Kokke, and Jeremy G. Siek's
[*Programming Language Foundations in Agda*](https://plfa.inf.ed.ac.uk/)
([`dev` branch](https://github.com/plfa/plfa.github.io/tree/dev), commit `c088569657`,
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)).

Every plain Haskell code block in this book is extracted into a standalone
`.hs` module and checked with GHC's Core Lint and STG Lint. Where Dependent
Haskell cannot yet express a PLFA theorem directly without workarounds,
we mark it with a **[WIP NOTICE]** and publish a minimal reproducer for the
compiler team.

Comments, bug reports, and pull requests are welcome on
[GitHub](https://github.com/Tritlo/PLFH).

## Front matter

- [Dependent Haskell Overview](/Overview/): Core concepts, GHC proposals (`#378`, `#281`, `#242`, ...), foundational papers, and the Serokell roadmap
- [Interactive Playground](/Playground/): Try Dependent Haskell, typed-hole refinement, and GHCi directly in your browser (WebAssembly)
- [Preface](/Preface/): Propositions as Types, totality discipline, and yardstick goals
- [Setup](/Setup/): Compiling `Tritlo/ghc`, `shell.nix`, flags, GHCi, and Hakyll preview

## Part 1: Logical Foundations

- [Naturals](/Naturals/): Natural numbers, `times`, `monus`, `pow`, `Bin` <span class="badge badge-pass">Checked</span>
- [Induction](/Induction/): Proof by induction (`+-assoc`, `HaskLib.rewrite`, `+-comm`, `cong`/`+-rearrange`, `+-swap`, `*-comm`, **`0∸n≡0`**, **`∸-+-assoc`**, **`+*^`**, `Bin-laws`) <span class="badge badge-pass">Checked</span>
- [Relations](/Relations/): Inductive relations (`_≤_`, `_<_`, trichotomy, `DiffWitness`, `Even`/`Odd`, canonical `One`/`Can` bijection) <span class="badge badge-pass">Checked</span>
- [Equality](/Equality/): Equality, `RequiredTypeArguments` chains, unified `substP`, `evenComm` (`substP @Even`), and unified `Leibniz` equality (`leibnizSym` + direct `@(EqP x)`) <span class="badge badge-pass">Checked</span>
- [Isomorphism](/Isomorphism/): Polymorphic `_≃_` (`Iso`, **`isoRefl`**, `isoSym`, **`isoTrans`**), `_≲_` (`Embed`, **`embedRefl`**, **`embedTrans`**, `binEmbedding`), and `_⇔_` (`Iff`) <span class="badge badge-pass">Checked</span>
- [Connectives](/Connectives/): Conjunction, disjunction, truth, falsehood, polymorphic **`prodCommIso`/`sumCommIso`**, currying, distributivity, exponential laws <span class="badge badge-pass">Checked</span>
- [Negation](/Negation/): Intuitionistic negation, De Morgan, order-negation laws, and classical equivalences (EM ⇔ DNE ⇔ Peirce ⇔ ImpOr ⇔ DeMorganNot) <span class="badge badge-pass">Checked</span>
- [Quantifiers](/Quantifiers/): Erased `Exists`, retained `Sigma` (`some`), and `Even`/`Odd` existential witnesses <span class="badge badge-pass">Checked</span>
- [Decidable](/Decidable/): Negation, decidable equality/ordering/parity/`Bin`, `Reflects`, and inline `Sigma` (`plusExists`) <span class="badge badge-pass">Checked</span>
- [Lists](/Lists/): Prelude `List a`, `(++)`, `map`, `HaskLib` length laws, `shunt`, `rev`/`revAppend`/`revInvolutive`/`shuntRev`/`reverses`, `downFrom`, **`foldrPlusSeed`/`foldrPlusAppend`** (`HaskLib.List.foldr`), matchability-poly `All`/`Any`/`In`, `notAnyIffAllNot`, `allToIn`/`inToAll`, **`anyIsoWitness`** (`Iso (Any p xs) (AnyWitness p xs)`), `decAll`/`decAny`/`decIn` <span class="badge badge-pass">Checked</span>

## Part 2: Programming Language Foundations

- [Lambda](/Lambda/): Simply-typed lambda calculus syntax, values, same-module `substTerm`, reduction (`Step`/`Steps`), and typing <span class="badge badge-pass">Checked</span>
- [Properties](/Properties/): Canonical forms, **Progress**, **Determinism**, **8-constructor Preservation**, `preserveSteps`, **verified evaluator `eval`**, and **well-typed terms don't get stuck (`wttdgs`)** <span class="badge badge-pass">Checked</span>
- [DeBruijn](/DeBruijn/): Intrinsically-typed terms, renaming, substitution, promoted `Value`, **`checkValue`**, **same-module 8-rule `Step` (`substSingle`)**, **unconditional `progress`**, and **6-line intrinsic `eval`** <span class="badge badge-pass">Checked</span>
- [Inference](/Inference/): **Sound & complete bidirectional `Dec`-based STLC type inference** (`synthesize`, `inherit`, `eraseSynth`/`eraseInherit`, `synthUnique`, plus `infer`/`check`) <span class="badge badge-pass">Checked</span>
- [Untyped](/Untyped/): Well-scoped untyped lambda calculus, sound relational `SubstAtU`, promoted `Neutral`/`Normal`/`BetaStep`, and **constructive normal-order `stepNormal`/`evalNormal`** <span class="badge badge-pass">Checked</span>
- [More](/More/): Extended STLC (`let`, `Unit`, `Prod`, `Sum`, `Void`, `List`), `singleSubst`/`doubleSubst`, **27-rule functional `Step`**, and **complete 19-branch `progress`** <span class="badge badge-pass">Checked</span>
- [Bisimulation](/Bisimulation/): Relating `let` to `(λx. n) m` (`SimRel`, `simRefl`/`simTrans`, bidirectional `simValue`/`simValueInv`, `valNoStep`, **20-constructor `simRename`**, **20-constructor `simExt`/`simSubst`**, **unconditional `simSubstSingle`/`simSubstDouble`**, and **unconditional 27-rule `sim` & `simInv`**) <span class="badge badge-pass">Checked</span>
- [BigStep](/BigStep/): Call-by-name big-step semantics (`Env`, `Clos`, `EvalBig`, **`evalDeterm`**, **`omegaDiverges`**, **same-module functional `EvalFun` (`lookupEnv`)**, **unconditional `cbnToReduce`**) <span class="badge badge-pass">Checked</span>
- [Substitution](/Substitution/): Constructive σ-calculus over `Untyped.substU` (**`subId`**, **`renSubst`**, **`substRename`**, **`renameSubst`**, **`subSub`**, pointwise σ-algebra laws, **`substCommute`**, and **Barendregt's `substitution` lemma**; explicit extensionality note) <span class="badge badge-pass">Checked</span>
- [Confluence](/Confluence/): Parallel reduction, **`parRefl`**, **`betaToPar`**, **`parShift`/`parSubst`**, **`parDiamond`**, **Strip Lemma**, **Par Confluence**, **unconditional Church-Rosser**, and **`uniqueNormalForm`** <span class="badge badge-pass">Checked</span>

## Part 3: Denotational Semantics

- [Denotational](/Denotational/): Filter model (GADT `Value`, `Sub`, `dom`/`cod`, nested `subInvDist`, **`subInv`**, **`arrSubArrInv`**, `Denotes`, `envSubMono`) <span class="badge badge-pass">Checked</span>
- [Compositional](/Compositional/): Semantic curry & application (**`lamEquiv`/`lamCong`**, **`appEquiv`/`appCong`**), `UCtx`/`plug`, and **full `compositionality`** <span class="badge badge-pass">Checked</span>
- [Soundness](/Soundness/): **100% unconditional** weakening, strengthening, substitution, forward preservation, subject expansion, and **`denotEquivSteps`** <span class="badge badge-pass">Checked</span>
- [Adequacy](/Adequacy/): **`decAboveFun`**, `LogVLam`/`LogE`, full **`subLogVLam`**, full **`fundamental`**, **unconditional `adequacyBigStep`/`adequacy`/`reduceToCbn`/`cbnToReduce`**, and **`omegaNotAboveFun`** <span class="badge badge-pass">Checked</span>
- [ContextualEquivalence](/ContextualEquivalence/): Open-term **`CtxEquiv`** (`UCtx`/`plug`), **unconditional `denotEqualCtxBigStep`**, **unconditional `denotEqualCtxEquiv`**, and **unconditional `betaCtxEquiv`** <span class="badge badge-pass">Checked</span>

## Yardstick, Reference & Backmatter

- [HaskLib Reference](/HaskLib/): Exported API, `Nat` / `List` laws, GHCi tips, and links to `HaskLib` source
- [Source Browser](/Source/): Syntax-highlighted `.hs` source for all chapters, clients, `HaskLib`, negative controls, and reproducers
- [Yardstick Status](/Status/): Full theorem-by-theorem ledger, HaskLib reuse, negative controls, and minimal compiler reproducers
- [How to Cite & Licence](/Citing/): CC BY 4.0 licence and attribution to upstream PLFA
