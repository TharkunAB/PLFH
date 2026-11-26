---
title: "Chapter Coverage"
description: "Chapter-by-chapter mapping of all 25 PLFA chapters to their checked Dependent Haskell modules in PLFH."
prev: /ContextualEquivalence/
next: /Citing/
src: content/Status.md
---

This page maps each chapter of *Programming Language Foundations in Agda*
(PLFA) to its checked Dependent Haskell module in PLFH.

All 25 chapters compile under
[`TharkunAB/ghc`](https://github.com/TharkunAB/ghc/tree/dependent-haskell)
(GHC `10.1`, branch `dependent-haskell`, tag `dependent-haskell-alpha`) with
[`TharkunAB/dependent-base`](https://github.com/TharkunAB/dependent-base) and
pass GHC's Core Lint and STG Lint at both `-O0` and `-O2`. Every proof module
is written by structural recursion without typed holes, `-fdefer-type-errors`,
`undefined`, `error`, or `unsafeCoerce`.

Companion plugins live in
[`TharkunAB/dependent-proof-search`](https://github.com/TharkunAB/dependent-proof-search)
and [`TharkunAB/dependent-obs-eq`](https://github.com/TharkunAB/dependent-obs-eq).

## Chapter-by-chapter coverage

| Chapter | PLFA declarations covered | PLFH module | Notes |
| --- | --- | --- | --- |
| [Naturals](/Naturals/) | `ℕ`, `_+_`, decimal numerals, `_*_`, `_∸_`, `_^_`, `Bin`, `inc`, `to`, `from` | `PLFH.Part1.Naturals` + `Data.Nat.Dependent` | Reuses `Data.Nat.Dependent` (`Num`/`FromNatural` numerals); proves `plus`, `times`, `monus`, and `pow` examples inline |
| [Induction](/Induction/) | `+-assoc`, `+-identityʳ`, `+-suc`, `+-comm`, `cong`, `+-rearrange`, `+-swap`, `*-distrib-+`, `*-assoc`, `*-comm`, `monus`/`pow` laws, `Bin` laws | `PLFH.Part1.Induction` | Proves all PLFA Induction theorems and exercises inline with visible `cong` and `Data.Type.Equality.Dependent.rewrite` |
| [Relations](/Relations/) | `_≤_`, `inv-*`, `≤-refl/trans/antisym`, `Total`, `+-mono-*`, `*-mono-≤`, `_<_`, `Trichotomy`, `DiffWitness`, `Even`/`Odd`, `One`/`Can`, `toBinCan`, `toFromCan` | `PLFH.Part1.Relations` | Full `Nat ≃ Can Bin` bijection, monotonicity, and multi-column total and trichotomy proofs |
| [Equality](/Equality/) | `_≡_`, `sym`, `trans`, `cong`, `cong-app`, `substP`, equational chains, `evenComm`, `Leibniz`, `leibnizSym`, `leibnizToEq` | `PLFH.Part1.Equality` | Matchability-polymorphic `substP` and `Leibniz` accepting both constructors and type lambdas |
| [Isomorphism](/Isomorphism/) | `Iso` (`_≃_`), `Embed` (`_≲_`), `Iff` (`_⇔_`), reflexivity/symmetry/transitivity, `binEmbedding` | `PLFH.Part1.Isomorphism` | Equivalence and preorder laws using `Data.Function.Dependent.(.)` plus `binEmbedding` |
| [Connectives](/Connectives/) | `×`, `⊎`, `⊤`, `⊥`, commutative semiring `Iso`s, `sumZeroRIso`/`sumZeroLIso`, exponential & congruence laws | `PLFH.Part1.Connectives` | All 12 commutative semiring laws proved as polymorphic `Iso`; exponential laws use `Iff` (function-space `Iso` requires function extensionality) |
| [Negation](/Negation/) | `¬`, double/triple negation, `¬¬` monad, De Morgan, `EM ⇔ DNE ⇔ Peirce ⇔ ImpOr ⇔ DeMorganNot`, order negation | `PLFH.Part1.Negation` | All five classical principles proved mutually equivalent alongside intuitionistic and order-negation laws |
| [Quantifiers](/Quantifiers/) | `Exists`, `existsDistribSum`, `existsCurry`, `forallDistribProd`, quantifier De Morgan, `EvenSigma`, `evenIffWitness`, `oddIffWitness` | `PLFH.Part1.Quantifiers` | Proposal `#473` erased `GHC.Exists.Exists` / `Data.Exists.Dependent`, retained `Sigma` (`some`), and both parity equivalences |
| [Decidable](/Decidable/) | `Dec`, logical combinators, `_≟_`, `_≤?_`, `_<?_`, `decEven`/`decOdd`, `decEqBin`/`decOne`/`decCan`, `Reflects`, `plusExists` | `PLFH.Part1.Decidable` | Direct two-column decision procedures and inline `foreach ... -> some ...` witnesses |
| [Lists](/Lists/) | `++-assoc`, `++-identityʳ`, `lengthAppendLaw`, `lengthMapLaw`, `lengthReverse`, `map` laws, `shunt`, `rev`, `revInvolutive`, `downFrom`, `foldr` laws, `All`/`Any`/`In`, `anyIsoWitness`, `decAll`/`decAny`/`decIn` | `PLFH.Part1.Lists` + `Data.List.Dependent` | Uses stock `Prelude` `List a`, `(++)`, `map`, and `Data.List.Dependent.foldr` under `-fno-enable-rewrite-rules` |
| [Lambda](/Lambda/) | `Term`, `Type`, `Context`, `Value`, `substTerm`, `Step`, `Steps`, `_∋_⦂_`, `_⊢_⦂_`, `twoChurchTyped`, `addTyped`, `stepExample` | `PLFH.Part2.Lambda` | Named STLC with recursion (`TMu`) and runtime evaluation |
| [Properties](/Properties/) | `Canonical`, `Progress`, `valueCannotStep`, `stepDeterm`, `renameTyping`, `weakenTyping`, `substTyping`, `preserve`, `preserveSteps`, `eval`, `wttdgs` | `PLFH.Part2.Properties` | Progress, determinism, 8-constructor preservation, multi-step preservation, verified evaluator, and unstuckness |
| [DeBruijn](/DeBruijn/) | Intrinsically-typed `Term g a`, `rename`, `subst`, `substSingle`, `Value`, `checkValue`, 8-rule `Step`, `progress`, 6-line `eval` | `PLFH.Part2.DeBruijn` | Intrinsically-typed STLC with capture-avoiding `substSingle`, 7-constructor progress, and executable evaluator |
| [Inference](/Inference/) | `decEqTy`, `lookupDec`, `TermPos`/`TermNeg`, `Synth`/`Inherit`, `eraseSynth`/`eraseInherit`, `synthUnique`, `synthesize`, `inherit` | `PLFH.Part2.Inference` | Sound and complete bidirectional `Dec`-based STLC type synthesis and checking |
| [Untyped](/Untyped/) | `Fin`, `UTerm`, `shiftFin`, `renameU`, `substU`, `substSingleU`, `Neutral`, `Normal`, `BetaStep`, Church numerals, `stepNormal`, `evalNormal` | `PLFH.Part2.Untyped` | Well-scoped untyped lambda calculus and constructive normal-order evaluator |
| [More](/More/) | Extended STLC (`Let`, `Unit`, `Prod`, `Sum`, `Void`, `List`), `singleSubst`/`doubleSubst`, 27-rule `Step`, 19-branch `progress`, `listCaseBoth` | `PLFH.Part2.More` | All 27 reduction rules and exhaustive 19-constructor progress |
| [Bisimulation](/Bisimulation/) | 20-constructor `SimRel`, `simRefl`/`simTrans`, `simValue`/`simValueInv`, `simRename`, `simSubst`, `simSubstSingle`/`Double`, 27-rule `sim`/`simInv`, `simSteps`, `letDesugarSim` | `PLFH.Part2.Bisimulation` | Complete 27-rule lock-step bisimulation between `let` and `(λx. n) m` |
| [BigStep](/BigStep/) | `Env`, `Clos`, `lookupEnv`, `EnvLookup`, `EvalBig`, `evalDeterm`, `omegaDiverges`, `EvalFun`, `CloseEnv`, `cbnToReduce`, `evalKIdOmega` | `PLFH.Part2.BigStep` | Call-by-name determinism, divergence of `Ω`, functional `lookupEnv`, and bridge to small-step reduction |
| [Substitution](/Substitution/) | `Rename`, `Subst`, `ids`, `shift`, `ren`, `consSubst`, `seqSubst`, `subId`, `renSubst`, `substRename`, `renameSubst`, `subSub`, pointwise σ-algebra, `substCommute`, Barendregt's `substitution` | `PLFH.Part2.Substitution` | Constructive term-level σ-calculus without axioms; notes PLFA's `postulate extensionality` for function-to-function σ-algebra equalities |
| [Confluence](/Confluence/) | `Par`, `parRefl`, `betaToPar`, `parRename`, `parSubst`, `parDiamond`, `strip`, `parConfluence`, `churchRosser`, `uniqueNormalForm` | `PLFH.Part2.Confluence` | Complete Church-Rosser confluence and uniqueness of normal forms reusing `Substitution` |
| [Denotational](/Denotational/) | GADT `Value`, `Sub`, `subRefl`, `dom`/`cod`, `subInv`, `arrSubArrInv`, `ValEnv`, `Denotes`, `envSubMono`, `DenEq` | `PLFH.Part3.Denotational` | Filter model, subtyping inversion, and monotonicity |
| [Compositional](/Compositional/) | `LamDen`, `lamEquiv`/`lamCong`, `AppDen`, `appEquiv`/`appCong`, `UCtx`, `plug`, `compositionality` | `PLFH.Part3.Compositional` | Lambda and application compositionality plus 4-line open-context compositionality |
| [Soundness](/Soundness/) | `denotRename`, `denotRenameReflect`, `denotSubst`, `denotSubstReflect`, `betaPres`, `betaReflect`, `denotPreserve`, `denotReflect`, `denotEquivSteps` | `PLFH.Part3.Soundness` | Forward preservation, subject expansion, and soundness of β-reduction |
| [Adequacy](/Adequacy/) | `AboveFun`, `decAboveFun`, `WHNF`, `HaltsV`, `logVLam`/`LogE`, `subLogVLam`, `subLogE`, `fundamental`, `adequacyBigStep`, `adequacy`, `reduceToCbn`, `cbnToReduce`, `omegaNotAboveFun` | `PLFH.Part3.Adequacy` | Big-step and small-step adequacy using a term-to-`Type` large elimination (`logVLam`) |
| [ContextualEquivalence](/ContextualEquivalence/) | `Terminates`, `terminatesLam`, `terminatesStep`, `CtxEquiv`, `plugTermW`, `denotEqualCtxBigStep`, `betaCtxBigStep`, `denotEqualCtxEquiv`, `betaCtxEquiv` | `PLFH.Part3.ContextualEquivalence` | Open-term contextual equivalence combining Compositionality, Soundness, Adequacy, and `cbnToReduce` |
