---
title: "Verification & Coverage"
prev: /ContextualEquivalence/
next: /Citing/
src: content/Status.md
---

This page summarizes how PLFH is verified against
[`TharkunAB/ghc` (`dependent-haskell`)](https://github.com/TharkunAB/ghc/tree/dependent-haskell)
and maps each PLFA chapter to its checked Haskell module.

- **Compiler & library:** GHC `10.1.20261115.1` (`TharkunAB/ghc`, branch `dependent-haskell`, tag `dependent-haskell-alpha`, commit [`945ea7a737`](https://github.com/TharkunAB/ghc/tree/dependent-haskell)) with [`dependent-base`](https://github.com/TharkunAB/dependent-base) (`Prelude.Dependent`, `Data.Function.Dependent`, `Data.Nat.Dependent`, `Data.Type.Equality.Dependent`, `Data.Exists.Dependent`, `Data.List.Dependent`, `Data.Vec.Dependent`, `Data.Fin.Dependent`, `Data.Sigma.Dependent`, `Data.Decision`).
- **Verification pipeline:** Native `-O0 -fomit-interface-pragmas -fno-write-if-simplified-core -dcore-lint -dstg-lint` across all **25 chapters**, automated **`.hi` interface soundness audit** (`scripts/audit_ifaces.py`), **10 negative controls**, and an executable **runtime smoke test** (`clients/PLFH/RuntimeSmokeTest.hs`, `183` runtime checks).
- **Proof discipline:** Every proof module is checked with zero typed holes, zero `-fdefer-type-errors`, zero `undefined`/`error`, zero circular bindings, zero `unsafeCoerce`, and zero silently quantified function type variables in `.hi` interfaces.

## Chapter-by-Chapter Coverage

| Chapter | Key PLFA Declarations | PLFH Module | Notes |
| --- | --- | --- | --- |
| [Naturals](/Naturals/) | `ℕ`, `_+_`, decimal numerals, `_*_`, `_∸_`, `_^_`, `Bin`, `inc`, `to`, `from` | `PLFH.Part1.Naturals` + `Data.Nat.Dependent` | Reuses `Data.Nat.Dependent` (`Num`/`FromNatural` numerals); proves `plus`, `times`, `monus`, and `pow` examples inline |
| [Induction](/Induction/) | `+-assoc`, `+-identityʳ`, `+-suc`, `+-comm`, `cong`, `+-rearrange`, `+-swap`, `*-distrib-+`, `*-assoc`, `*-comm`, `monus`/`pow` laws, `Bin` laws | `PLFH.Part1.Induction` | All PLFA Induction theorems and exercises proved inline with visible `cong` and `Data.Type.Equality.Dependent.rewrite` |
| [Relations](/Relations/) | `_≤_`, `inv-*`, `≤-refl/trans/antisym`, `Total`, `+-mono-*`, `*-mono-≤`, `_<_`, `Trichotomy`, `DiffWitness`, `Even`/`Odd`, `One`/`Can`, `toBinCan`, `toFromCan` | `PLFH.Part1.Relations` | Full `Nat ≃ Can Bin` bijection, monotonicity, and multi-column total/trichotomy proofs |
| [Equality](/Equality/) | `_≡_`, `sym`, `trans`, `cong`, `cong-app`, `substP`, equational chains, `evenComm`, `Leibniz`, `leibnizSym`, `leibnizToEq` | `PLFH.Part1.Equality` | Matchability-polymorphic `substP` and `Leibniz` accepting both constructors and type lambdas |
| [Isomorphism](/Isomorphism/) | `Iso` (`_≃_`), `Embed` (`_≲_`), `Iff` (`_⇔_`), reflexivity/symmetry/transitivity, `binEmbedding` | `PLFH.Part1.Isomorphism` | Generic equivalence and preorder laws using `Data.Function.Dependent.(.)` plus `binEmbedding` (`NegBinReverseRoundTrip`) |
| [Connectives](/Connectives/) | `×`, `⊎`, `⊤`, `⊥`, commutative semiring `Iso`s, `sumZeroRIso`/`sumZeroLIso`, exponential & congruence laws | `PLFH.Part1.Connectives` | All 12 commutative semiring laws proved as polymorphic `Iso`; exponential laws use `Iff` (function-space `Iso` needs extensionality) |
| [Negation](/Negation/) | `¬`, double/triple negation, `¬¬` monad, De Morgan, `EM ⇔ DNE ⇔ Peirce ⇔ ImpOr ⇔ DeMorganNot`, order negation | `PLFH.Part1.Negation` | All five classical principles proved mutually equivalent alongside intuitionistic and order-negation laws |
| [Quantifiers](/Quantifiers/) | `Exists`, `existsDistribSum`, `existsCurry`, `forallDistribProd`, quantifier De Morgan, `EvenSigma`, `evenIffWitness`, `oddIffWitness` | `PLFH.Part1.Quantifiers` | Proposal `#473` erased `GHC.Exists.Exists` / `Data.Exists.Dependent` (`Pack`, `withExists`, `mapExists`), retained `Sigma` (`some`), and both parity equivalences |
| [Decidable](/Decidable/) | `Dec`, logical combinators, `_≟_`, `_≤?_`, `_<?_`, `decEven`/`decOdd`, `decEqBin`/`decOne`/`decCan`, `Reflects`, `plusExists` | `PLFH.Part1.Decidable` | Direct two-column decision procedures and inline `foreach ... -> some ...` witnesses |
| [Lists](/Lists/) | `++-assoc`, `++-identityʳ`, `lengthAppendLaw`, `lengthMapLaw`, `lengthReverse`, `map` laws, `shunt`, `rev`, `revInvolutive`, `downFrom`, `foldr` laws, `All`/`Any`/`In`, `anyIsoWitness`, `decAll`/`decAny`/`decIn` | `PLFH.Part1.Lists` + `Data.List.Dependent` | Uses stock `Prelude` `List a`, `(++)`, `map`, and `Data.List.Dependent.foldr` under `-fno-enable-rewrite-rules` (`-O2` list-fusion guard keeps strictness sound) |
| [Lambda](/Lambda/) | `Term`, `Type`, `Context`, `Value`, `substTerm`, `Step`, `Steps`, `_∋_⦂_`, `_⊢_⦂_`, `twoChurchTyped`, `addTyped`, `stepExample` | `PLFH.Part2.Lambda` | Named STLC with recursion (`TMu`), verified by `NegBetaMuTarget` and runtime evaluation |
| [Properties](/Properties/) | `Canonical`, `Progress`, `valueCannotStep`, `stepDeterm`, `renameTyping`, `weakenTyping`, `substTyping`, `preserve`, `preserveSteps`, `eval`, `wttdgs` | `PLFH.Part2.Properties` | Progress, determinism, 8-constructor preservation, multi-step preservation, verified evaluator, and unstuckness |
| [DeBruijn](/DeBruijn/) | Intrinsically-typed `Term g a`, `rename`, `subst`, `substSingle`, `Value`, `checkValue`, 8-rule `Step`, `progress`, 6-line `eval` | `PLFH.Part2.DeBruijn` | Intrinsically-typed STLC with capture-avoiding `substSingle` (`NegDeBruijnBadCapture`), 7-constructor progress, and executable evaluator |
| [Inference](/Inference/) | `decEqTy`, `lookupDec`, `TermPos`/`TermNeg`, `Synth`/`Inherit`, `eraseSynth`/`eraseInherit`, `synthUnique`, `synthesize`, `inherit` | `PLFH.Part2.Inference` | Sound and complete bidirectional `Dec`-based STLC type synthesis and checking |
| [Untyped](/Untyped/) | `Fin`, `UTerm`, `shiftFin`, `renameU`, `substU`, `substSingleU`, `Neutral`, `Normal`, `BetaStep`, Church numerals, `stepNormal`, `evalNormal` | `PLFH.Part2.Untyped` | Well-scoped untyped λ-calculus (`NegBadBetaStep`) and constructive normal-order evaluator |
| [More](/More/) | Extended STLC (`Let`, `Unit`, `Prod`, `Sum`, `Void`, `List`), `singleSubst`/`doubleSubst`, 27-rule `Step`, 19-branch `progress`, `listCaseBoth` | `PLFH.Part2.More` | All 27 reduction rules and exhaustive 19-constructor progress (`NegMoreConsTarget`) |
| [Bisimulation](/Bisimulation/) | 20-constructor `SimRel`, `simRefl`/`simTrans`, `simValue`/`simValueInv`, `simRename`, `simSubst`, `simSubstSingle`/`Double`, 27-rule `sim`/`simInv`, `simSteps`, `letDesugarSim` | `PLFH.Part2.Bisimulation` | Complete 27-rule lock-step bisimulation between `let` and `(λx. n) m` (`NegBisimBadTarget`) |
| [BigStep](/BigStep/) | `Env`, `Clos`, `lookupEnv`, `EnvLookup`, `EvalBig`, `evalDeterm`, `omegaDiverges`, `EvalFun`, `CloseEnv`, `cbnToReduce`, `evalKIdOmega` | `PLFH.Part2.BigStep` | Call-by-name determinism, divergence of `Ω`, functional `lookupEnv` (`NegBigStepBadLookup`), and bridge to small-step reduction |
| [Substitution](/Substitution/) | `Rename`, `Subst`, `ids`, `shift`, `ren`, `consSubst`, `seqSubst`, `subId`, `renSubst`, `substRename`, `renameSubst`, `subSub`, pointwise σ-algebra, `substCommute`, Barendregt's `substitution` | `PLFH.Part2.Substitution` | Constructive term-level σ-calculus with zero axioms; notes PLFA's `postulate extensionality` for function-to-function σ-algebra equalities |
| [Confluence](/Confluence/) | `Par`, `parRefl`, `betaToPar`, `parRename`, `parSubst`, `parDiamond`, `strip`, `parConfluence`, `churchRosser`, `uniqueNormalForm` | `PLFH.Part2.Confluence` | Complete Church–Rosser confluence and uniqueness of normal forms reusing `Substitution` |
| [Denotational](/Denotational/) | GADT `Value`, `Sub`, `subRefl`, `dom`/`cod`, `subInv`, `arrSubArrInv`, `ValEnv`, `Denotes`, `envSubMono`, `DenEq` | `PLFH.Part3.Denotational` | Filter model, subtyping inversion, and monotonicity |
| [Compositional](/Compositional/) | `LamDen`, `lamEquiv`/`lamCong`, `AppDen`, `appEquiv`/`appCong`, `UCtx`, `plug`, `compositionality` | `PLFH.Part3.Compositional` | Lambda and application compositionality plus 4-line open-context compositionality |
| [Soundness](/Soundness/) | `denotRename`, `denotRenameReflect`, `denotSubst`, `denotSubstReflect`, `betaPres`, `betaReflect`, `denotPreserve`, `denotReflect`, `denotEquivSteps` | `PLFH.Part3.Soundness` | Forward preservation, subject expansion, and soundness of β-reduction |
| [Adequacy](/Adequacy/) | `AboveFun`, `decAboveFun`, `WHNF`, `HaltsV`, `logVLam`/`LogE`, `subLogVLam`, `subLogE`, `fundamental`, `adequacyBigStep`, `adequacy`, `reduceToCbn`, `cbnToReduce`, `omegaNotAboveFun` | `PLFH.Part3.Adequacy` | Big-step and small-step adequacy using a term-to-`Type` large elimination (`logVLam`) |
| [ContextualEquivalence](/ContextualEquivalence/) | `Terminates`, `terminatesLam`, `terminatesStep`, `CtxEquiv`, `plugTermW`, `denotEqualCtxBigStep`, `betaCtxBigStep`, `denotEqualCtxEquiv`, `betaCtxEquiv` | `PLFH.Part3.ContextualEquivalence` | Open-term contextual equivalence combining Compositionality, Soundness, Adequacy, and `cbnToReduce` |

## Negative Controls (10 Verified Rejections)

Every negative control asserts a false proposition and is verified by `scripts/check_plfh.sh` to fail with `GHC-83865`:

| Control File | Claimed Falsehood | Expected Diagnostic |
| --- | --- | --- |
| `hs/negative/NegZeroSucc.hs` | `Zero :~: Succ Zero` | `GHC-83865` |
| `hs/negative/NegOneLeZero.hs` | `LE 1 0` | `GHC-83865` |
| `hs/negative/NegBinReverseRoundTrip.hs` | `toBin (fromBin Nil) :~: Nil` | `GHC-83865` |
| `hs/negative/NegIllTypedApp.hs` | `HasType CEmpty (App TZero TZero) TNat` | `GHC-83865` |
| `hs/negative/NegBetaMuTarget.hs` | `Step (TMu Zero TZero) (TCase ...)` (forged β-target) | `GHC-83865` |
| `hs/negative/NegDeBruijnBadCapture.hs` | `Step (App (Lam (Lam (Var (S Z)))) (Lam (Var (S Z)))) (Lam (Lam (Var (S Z))))` (forged capture) | `GHC-83865` |
| `hs/negative/NegMoreConsTarget.hs` | `Step (CaseLst (Cons (Suc Zero) ...) ... (Pair (Var (S Z)) (Var Z))) (Pair Zero ...)` (forged head) | `GHC-83865` |
| `hs/negative/NegBisimBadTarget.hs` | `Leg Step (App (Lam (Suc (Var Z))) Zero) Zero` (forged β-target) | `GHC-83865` |
| `hs/negative/NegBigStepBadLookup.hs` | `Eval ENil (((λx y. x) id) Ω) (MkClos OmegaTerm ENil)` (forged `lookupEnv` closure) | `GHC-83865` |
| `hs/negative/NegBadBetaStep.hs` | `BetaStep (UApp IdTerm IdTerm) OmegaTerm` | `GHC-83865` |
