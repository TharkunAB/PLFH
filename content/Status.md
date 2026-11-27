---
title: "Chapter Coverage"
description: "Chapter-by-chapter mapping of all 25 PLFA chapters to their checked Dependent Haskell modules in PLFH."
prev: /source/
next: /citing/
src: content/Status.md
---

This page maps each chapter of *Programming Language Foundations in Agda*
(PLFA) to its checked Dependent Haskell module in PLFH.

All 25 chapters compile under
[`TharkunAB/ghc`](https://github.com/TharkunAB/ghc/tree/dependent-haskell)
(GHC 10.1, branch `dependent-haskell`) with
[`TharkunAB/dependent-base`](https://github.com/TharkunAB/dependent-base) and
pass GHC's Core Lint and STG Lint at both `-O0` and `-O2`. Every proof module
is written by structural recursion without typed holes, `-fdefer-type-errors`,
`undefined`, `error`, or `unsafeCoerce`.

## Chapter-by-chapter coverage

| Chapter | PLFA declarations covered | PLFH module | Notes |
| --- | --- | --- | --- |
| [Naturals](/naturals/) | `ℕ`, `_+_`, decimal numerals, `_*_`, `_∸_`, `_^_`, `Bin`, `inc`, `to`, `from` | `PLFH.Part1.Naturals` + `Data.Nat.Dependent` | Reuses `Data.Nat.Dependent` (`Num`/`FromNatural` numerals); proves `plus`, `times`, `monus`, and `pow` examples inline |
| [Induction](/induction/) | `+-assoc`, `+-identityʳ`, `+-suc`, `+-comm`, `cong`, `+-rearrange`, `+-swap`, `*-distrib-+`, `*-assoc`, `*-comm`, `monus`/`pow` laws, `Bin` laws | `PLFH.Part1.Induction` | Proves all PLFA Induction theorems and exercises inline with visible `cong` and `Data.Type.Equality.Dependent.rewrite` |
| [Relations](/relations/) | `_≤_`, `inv-*`, `≤-refl/trans/antisym`, `Total`, `+-mono-*`, `*-mono-≤`, `_<_`, `Trichotomy`, `DiffWitness`, `Even`/`Odd`, `One`/`Can`, `toBinCan`, `toFromCan` | `PLFH.Part1.Relations` | Full `Nat ≃ Can Bin` bijection, monotonicity, and multi-column total and trichotomy proofs |
| [Equality](/equality/) | `_≡_`, `sym`, `trans`, `cong`, `cong2P`, `cong-app`, `substP`, `beginLE`, `evenComm`, `Leibniz`, `leibnizSym`, `leibnizToEq` | `PLFH.Part1.Equality` | Matchability-polymorphic `substP` and `Leibniz`, plus `≤`-reasoning chains |
| [Isomorphism](/isomorphism/) | `Iso` (`_≃_`), `Embed` (`_≲_`), `Iff` (`_⇔_`), `FunExt`/`samePlus`, reflexivity/symmetry/transitivity, `binEmbedding` | `PLFH.Part1.Isomorphism` | Equivalence and preorder laws using `Data.Function.Dependent.(.)`, explicit `FunExt` demo, and `binEmbedding` |
| [Connectives](/connectives/) | `×`, `⊎`, `⊤`, `⊥`, commutative semiring `Iso`s, `etaProd`/`etaUnit`/`etaSum`/`etaArr`, `sumDistribProd`, exponential & congruence laws | `PLFH.Part1.Connectives` | All 12 commutative semiring laws proved as polymorphic `Iso`, η-rules, and `⊎-distrib-×` embedding |
| [Negation](/negation/) | `¬`, double/triple negation, `¬¬` monad, De Morgan, `EM ⇔ DNE ⇔ Peirce ⇔ ImpOr ⇔ DeMorganNot`, order negation | `PLFH.Part1.Negation` | Defines `Not` directly without forward imports; proves all five classical equivalences |
| [Quantifiers](/quantifiers/) | `Exists`, `existsDistribSum`, `sigmaDistribSum`, `existsCurry`, `forallDistribProd`, quantifier De Morgan, `oneIrr`/`canIrr`/`canBinEq`/`binIff`, `evenIffWitness`, `oddIffWitness` | `PLFH.Part1.Quantifiers` | Proposal `#473` erased `Exists`, retained `Sigma`/`DPair`, canonical binary proof irrelevance, and both parity equivalences |
| [Decidable](/decidable/) | `leBool`/`tBool`/`leBoolToLE`/`leToLeBool`, `Dec`, `eraseDec`/`toWitness`/`fromWitness`, logical combinators, `_≟_`, `_≤?_`, `_<?_`, `decEven`/`decOdd`, `decEqBin`/`decOne`/`decCan`, `Reflects`, `plusExists` | `PLFH.Part1.Decidable` | Boolean-to-evidence bridge via term-to-`Type` `tBool`, two-column decision procedures, and inline `some` witnesses |
| [Lists](/lists/) | `++-assoc`, `++-identityʳ`, `lengthAppendLaw`, `lengthMapLaw`, `lengthReverse`, `map` laws, `shunt`, `rev`, `revInvolutive`, `downFrom`, `MonoidLaws`, `foldrMonoidSeed`/`Append`, `All`, `Any`, `In`, `decAll`, `decAny`, `decIn` | `PLFH.Part1.Lists` + `Data.List.Dependent` | Generic monoid fold laws (`plusMonoid`, `timesMonoid`, `appendMonoid`) over stock `Prelude` lists |
| [Lambda](/lambda/) | `Term`, `Type`, `Context`, `Value`, `substTerm`, `Step`, `Steps`, `_∋_⦂_`, `_⊢_⦂_`, `twoChurchTyped`, `addTyped`, `stepExample` | `PLFH.Part2.Lambda` | Named STLC with recursion (`TMu`) and runtime evaluation |
| [Properties](/properties/) | `Canonical`, `Progress`, `valueCannotStep`, `stepDeterm`, `renameTyping`, `weakenTyping`, `substTyping`, `preserve`, `preserveSteps`, `eval`, `wttdgs` | `PLFH.Part2.Properties` | Progress, determinism, 8-constructor preservation, multi-step preservation, verified evaluator, and unstuckness |
| [DeBruijn](/debruijn/) | Intrinsically-typed `Term g a`, `rename`, `subst`, `substSingle`, `Value`, `checkValue`, 8-rule `Step`, `progress`, 6-line `eval` | `PLFH.Part2.DeBruijn` | Intrinsically-typed STLC with capture-avoiding `substSingle`, 7-constructor progress, and executable evaluator |
| [Inference](/inference/) | `decEqTy`, `lookupDec`, `TermPos`, `TermNeg`, `Synth`, `Inherit`, `eraseSynth`, `eraseInherit`, `synthUnique`, `synthesize`, `inherit` | `PLFH.Part2.Inference` | Sound and complete bidirectional `Dec`-based STLC type synthesis and checking |
| [Untyped](/untyped/) | `Fin`, `UTerm`, `shiftFin`, `renameU`, `substU`, `substSingleU`, `Neutral`, `Normal`, `BetaStep`, Church & Scott numerals, Curry's `sMu`, `sPlus`, `stepNormal`, `evalNormal` | `PLFH.Part2.Untyped` | Well-scoped untyped lambda calculus, Scott numerals with `sTwoPlusTwo`, and constructive normal-order evaluator |
| [More](/more/) | Extended STLC (`Let`, `Unit`, `Prod`, `Sum`, `Void`, `List`), `substSingle`, `substDouble`, 27-rule `Step`, `valueCannotStep`, 19-branch `progress`, `listCaseBoth` | `PLFH.Part2.More` | All 27 reduction rules, `valueCannotStep`, and exhaustive 19-constructor progress |
| [Bisimulation](/bisimulation/) | 20-constructor `SimRel`, `simRefl`, `simTrans`, `simValue`, `simValueInv`, `simRename`, `simSubst`, `simSubstSingle`, `simSubstDouble`, 27-rule `sim`, `simInv`, `simSteps`, `letDesugarSim` | `PLFH.Part2.Bisimulation` | Complete 27-rule lock-step bisimulation between `let` and `(λx. n) m` |
| [Substitution](/substitution/) | `Rename`, `Subst`, `ids`, `shift`, `ren`, `consSubst`, `seqSubst`, `subId`, `renSubst`, `substRename`, `renameSubst`, `subSub`, pointwise σ-algebra, `substCommute`, Barendregt's `substitution` | `PLFH.Part2.Substitution` | Constructive term-level σ-calculus without axioms; notes PLFA's `postulate extensionality` for function-to-function σ-algebra equalities |
| [BigStep](/bigstep/) | `Env`, `Clos`, `lookupEnv`, `EnvLookup`, `EvalBig`, `evalDeterm`, `omegaDiverges`, `EvalFun`, `CloseEnv`, `cbnToReduce`, `evalKIdOmega` | `PLFH.Part2.BigStep` | Call-by-name determinism, divergence of `Ω`, functional `lookupEnv`, and bridge to small-step reduction |
| [Confluence](/confluence/) | `Par`, `parRefl`, `betaToPar`, `parRename`, `parSubst`, `parDiamond`, `strip`, `parConfluence`, `churchRosser`, `uniqueNormalForm` | `PLFH.Part2.Confluence` | Complete Church-Rosser confluence and uniqueness of normal forms reusing `Substitution` |
| [Denotational](/denotational/) | GADT `Value`, `Sub`, `subRefl`, `dom`/`cod`, `subInv`, `arrSubArrInv`, `ValEnv`, `Denotes`, `envSubMono`, `DenEq` | `PLFH.Part3.Denotational` | Filter model, subtyping inversion, and monotonicity |
| [Compositional](/compositional/) | `LamDen`, `lamEquiv`/`lamCong`, `AppDen`, `appEquiv`/`appCong`, `VarDen`, `varInv`/`varEquiv`, `UCtx`, `plug`, `compositionality` | `PLFH.Part3.Compositional` | Lambda, application, and variable compositionality plus 4-line open-context `compositionality` |
| [Soundness](/soundness/) | `denotRename`, `denotRenameReflect`, `denotSubst`, `denotSubstReflect`, `betaPres`, `betaReflect`, `denotPreserve`, `denotReflect`, `denotEquivSteps` | `PLFH.Part3.Soundness` | Forward preservation, subject expansion, and soundness of β-reduction |
| [Adequacy](/adequacy/) | `AboveFun`, `decAboveFun`, `HaltsV`, `logVLam`/`LogE`, `subLogVLam`, `subLogE`, `fundamental`, `adequacyBigStep`, `adequacy`, `reduceToCbn`, `cbnToReduce`, `cbnIffReduce`, `omegaNotAboveFun` | `PLFH.Part3.Adequacy` | Big-step and small-step adequacy using a term-to-`Type` large elimination (`logVLam`) and `cbnIffReduce` |
| [ContextualEquivalence](/contextualequivalence/) | `Terminates`, `terminatesLam`, `terminatesStep`, `CtxEquiv`, `plugTermW`, `denotEqualCtxBigStep`, `betaCtxBigStep`, `denotEqualCtxEquiv`, `betaCtxEquiv` | `PLFH.Part3.ContextualEquivalence` | Open-term contextual equivalence combining Compositionality, Soundness, Adequacy, and `cbnToReduce` |
