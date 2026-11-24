---
title: "Yardstick Status Ledger"
prev: /ContextualEquivalence/
next: /Citing/
src: content/Status.md
---

This page tracks every PLFA declaration, theorem, and
exercise attempted in PLFH against the experimental Dependent Haskell compiler
([`Tritlo/ghc`, branch `dependent-haskell`](https://github.com/Tritlo/ghc/tree/dependent-haskell)).

- **Current published compiler & HaskLib:** GHC `10.1.20261115.1`, published commits [`692eae0778`](https://github.com/Tritlo/ghc/commit/692eae077896a00384fecf15a3d5d92d828a6415) + [`9cc4065fab`](https://github.com/Tritlo/ghc/commit/9cc4065fab4f2f106859b39daa9bdad23f00f0fd) + [`63e2f0974b`](https://github.com/Tritlo/ghc/commit/63e2f0974b174dc86bef79c3a84d1d76fea3dadf) / [`76e67f4fdb`](https://github.com/Tritlo/ghc/commit/76e67f4fdbc5d1c8dafc9d29da8e942e0fec1c85) (600-example Showcase on `dependent-haskell`; previous baselines: 590 `1a02a866e7`, 588 `d15cbd41fe`, 585 `db2586fdc2`) + live `HaskLib.Nat` (`Nat(..)`, `type (+)`, `eqSize`/`eqSizeRefl`, decimal literals) and `HaskLib.rewrite`.
- **Major milestone — 15 compiler fixes published & integrated (half of all 30 reproducers!):** Fifteen of our 30 tracked reproducers now pass at **both `-O0` and `-O2`** with `-dcore-lint -dstg-lint` and live as automated regression checks under [`reproducers/fixed/`](https://github.com/Tritlo/PLFH/tree/main/reproducers/fixed), unlocking:
  - **Full STLC Progress & 8-constructor Preservation** (`Lambda.Step` using ordinary same-module `substTerm` + `Properties.{progress,substTyping,preserve}` + negative control `NegBetaMuTarget`),
  - **Unconditional Big-Step Determinism & Unconditional Adequacy** (`BigStep.evalDeterm` → `Adequacy.{subLogVLam,fundamental,adequacyBigStep,adequacyIdApp}`),
  - **Full `Bisimulation.simValue`** (R11 Desugar Core Lint fixed!),
  - **Direct `Denotational` GADT `Value` & nested dependent `case` `subInvDist`** (R13 GADT syntax + R03 Desugar Core Lint fixed!),
  - **Simplified certified `Inference.infer`** (inline `case lTy of` refinement, no `matchArr`/`matchNat` or `@g @a @b` annotations!),
  - **Part 1 direct proofs:** `Induction.{cong,plusRearrange,plusSwap,zeroMonus,monusPlusAssoc}` (ordinary `monus` fixed in `63e2f0974b`!), `Equality.evenComm` via `substP @Even`, `Isomorphism.{isoSizeRefl,isoSizeSym}`, `Decidable.plusExists` (inline `some` under `foreach`), and `Lists.{lengthAppendLaw,lengthReverseLaw,shunt,shuntAppend,downFrom,zeros,lengthDownFrom,lengthZeros}`!
- **Verification mode:** Native `-O0 -fomit-interface-pragmas -fno-write-if-simplified-core -dcore-lint -dstg-lint` across all 27 modules, automated **`.hi` interface soundness audit** (`scripts/audit_ifaces.py`), **5 negative controls**, **15 fixed-reproducer regressions** checked at both `-O0` and `-O2`, executable **runtime smoke test** (`clients/PLFH/RuntimeSmokeTest.hs`, 56 `[RUN-OK]` checks), and **15 open blocker reproducers**.
- **Proof discipline:** Zero typed holes, zero `-fdefer-type-errors`, zero `undefined`/`error`, zero circular bindings, zero `unsafeCoerce`, zero silently quantified function type variables in `.hi` interfaces.
- **Policy on gaps:** Avoid workarounds; mark unsupported items `[WIP NOTICE]` and maintain a minimal standalone reproducer under [`reproducers/`](https://github.com/Tritlo/PLFH/tree/main/reproducers).

## Chapter-by-Chapter Declaration Ledger

| Chapter | PLFA Declaration | PLFH Module & Symbol | Category | Notes / Serokell Card |
| --- | --- | --- | --- | --- |
| [Naturals](/Naturals/) | `ℕ` (`zero`, `suc`), `_+_`, decimal numerals | `HaskLib.Nat.{Nat,plus,(+)}` | <span class="badge badge-reuse">HaskLib reuse</span> | `FromNatural` & `Num` enable `plus 2 3 :~: 5` and `(2 + 3 :: Nat) :~: 5`! |
| [Naturals](/Naturals/) | `2 + 3 ≡ 5`, `_*_`, `_∸_` (`monus`), `Bin`, `inc`, `to`, `from` | `PLFH.Part1.Naturals.*` | <span class="badge badge-pass">Direct port</span> | `monus` open equations fixed in `63e2f0974b`! `times` still needs named `n` (`R13_WildcardBreaksOpenEq.hs`) |
| [Naturals](/Naturals/) | `_^_` open type eval | `PLFH.Part1.Naturals.pow` | <span class="badge badge-wip">Blocker (open)</span> | Runtime OK; open type eval blocked (`R13_PowOpenEq.hs`) |
| [Induction](/Induction/) | `+-assoc`, `+-assoc′` (`HaskLib.rewrite`), `+-identityʳ`, `+-suc`, `+-comm`, **`cong` + `+-rearrange`**, **`+-swap`** (nested `rewrite`), `*-distrib-+`, `*-assoc`, `*-comm`, **`0∸n≡0`**, **`∸-+-assoc`**, `Bin-laws` | `PLFH.Part1.Induction.*` + `HaskLib.Nat.{plusZero,plusSucc}` | <span class="badge badge-pass">Direct port</span> | Direct `cong @(plus m)`, nested `rewrite`, and ordinary `monus` laws (`zeroMonus`, `monusPlusAssoc`) fixed on `63e2f0974b`! |
| [Induction](/Induction/) | `+*^` (exponentiation laws) | — | <span class="badge badge-wip">Blocker</span> | Blocked by open equations for `pow` (`R13_PowOpenEq.hs`) |
| [Relations](/Relations/) | `_≤_`, `inv-*`, `≤-refl/trans/antisym`, `Total`, `+-mono-*`, `_<_`, `<-trans`, `Trichotomy`, `ltToLe`/`leToLt`, `DiffWitness`, `Even`/`Odd` + sums + `evenOrOdd`/`notBothEvenOdd`, canonical `One`/`Can` + `incOne`/`incCan` + **`toBinCan`** + **`toFromCan`** | `PLFH.Part1.Relations.*` | <span class="badge badge-pass">Direct port</span> | Full `Nat ≃ Can Bin` bijection (`fromTo` + `toBinCan` + `toFromCan`) checked! |
| [Equality](/Equality/) | `_≡_`, `sym`, `trans`, `cong`, `cong-app`, `subst`, `RequiredTypeArguments` chains (`beginEq`/`stepEq`/`qedEq`), **`evenComm` (`substP @Even`)**, `Leibniz`, `LeibnizU`, `leibnizUSym` | `PLFH.Part1.Equality.*` | <span class="badge badge-pass">Direct port</span> | Direct `substP @Even (toEqP (plusComm m n)) ev` fixed (`R03_TcInstFunPanic.hs`); inline type lambda `@(\z -> EqP z x)` works (R17)! |
| [Isomorphism](/Isomorphism/) | `_⇔_` (`Iff`, refl/sym/trans), monomorphic **`IsoSize` (`isoSizeRefl`, `isoSizeSym`)** | `PLFH.Part1.Isomorphism.*` | <span class="badge badge-pass">Direct port</span> | Higher-rank `foreach` proof fields construct & eliminate cleanly (`R04_HigherRankForEachField.hs` fixed!) |
| [Isomorphism](/Isomorphism/) | Polymorphic `_≃_`, `_≲_` | — | <span class="badge badge-wip">Blocker</span> | Polymorphic retained function domain `foreach (to :: a -> b)` (`R04_PolyFunctionFieldInIso.hs`) |
| [Connectives](/Connectives/) | `×`, `⊎`, `⊤`, `⊥`, comm/assoc/zero/distrib/currying/exp/cong | `PLFH.Part1.Connectives.*` | <span class="badge badge-pass">Direct port</span> | All semiring, exponential & `Iff` congruence laws checked over `(,)`, `Either`, `()`, `Void` |
| [Negation](/Negation/) | `¬`, double/triple neg, `¬¬` monad, De Morgan, `EM ⇔ DNE ⇔ Peirce ⇔ ImpOr`, `emToDeMorganProd`, `ltIrrefl`/`ltAsym`/`notLtZero`/`ltToNotGe`/`leToNotGt`/`notLeToGt` | `PLFH.Part1.Negation.*` | <span class="badge badge-pass">Direct port</span> | All intuitionistic, classical & order-negation laws checked |
| [Quantifiers](/Quantifiers/) | `Exists`, `existsDistribSum`, `existsCurry`, `forallDistribProd`, quantifier De Morgan, `EvenSigma`, **`evenIffWitness`**, **`oddIffWitness`** | `PLFH.Part1.Quantifiers.*` | <span class="badge badge-pass">Direct port</span> | Retained `EvenSigma` (`some`) + both directions of parity witnesses checked! |
| [Decidable](/Decidable/) | `¬`, `Dec` + `decNot`/`And`/`Or`/`Imp`/`Iff`, `_≟_`, `_≤?_`, `_<?_`, `decEven`/`decOdd`, `decEqBin`/`decOne`/`decCan`, `Reflects`, `reflectsToDec`, `SizeWitness`, **`plusExists`** | `PLFH.Part1.Decidable.*` | <span class="badge badge-pass">Direct port</span> | Inline `foreach ... -> some ...` (`plusExists`) fixed (`R04_SigmaUnderForEach.hs`)! |
| [Lists](/Lists/) | `++-assoc`, `++-identityʳ`, `HaskLib` length laws (eta-reduced `lengthAppendLaw`/`lengthReverseLaw`), `map-++`/`compose`/`id`, **`shunt`/`shuntAppend`**, **`downFrom`/`zeros`/`lengthDownFrom`/`lengthZeros`**, `All`, `Any`, `In`, `allAppend`/`Inv`, `anyAppend*`/`Inv`, `decAll`, `decAny` | `PLFH.Part1.Lists.*` + `HaskLib` | <span class="badge badge-pass">Direct port</span> | Ordinary Prelude `[a]`, `(++)`, `map`! `downFrom` & `shuntAppend` (`-fno-enable-rewrite-rules`) checked! Uncovered `R04_EtaAliasForEachFunctionBinder.hs` on `lengthMapLaw = lengthMap` |
| [Lists](/Lists/) | `rev`, `foldr-monoid-++`, default `-O2` `shuntAppend`, `All (\x -> Not (p x))` | — | <span class="badge badge-wip">Blocker</span> | `R13_RevOpenEq.hs`, `R03_FoldrRetainedIndex.hs`, `R13_ShuntAccumOpenEq.hs` (`-O2`), `R23_MatchabilityInLeibniz.hs` |
| [Lambda](/Lambda/) | `Term`, `Type`, `Context`, `Value`, `substTerm`, **`Step`**, **`Steps`**, `_∋_⦂_`, `_⊢_⦂_` | `PLFH.Part2.Lambda.*` | <span class="badge badge-pass">Direct port</span> | **Full checked same-module `substTerm` in `BetaLam`/`BetaSuc`/`BetaMu`** (`692eae0778`), `.hi`-audited, verified by `NegBetaMuTarget` (`GHC-83865`)! |
| [Properties](/Properties/) | `Canonical`, `canonical`, **`Progress`/`progress`**, `extCtx`, `renameTyping`, `weakenTyping`, `dropTyping`, `swapTyping`, `NameDecision`/`decide`, **`substTyping`**, **`preserve`** | `PLFH.Part2.Properties.*` | <span class="badge badge-pass">Direct port</span> | **Full STLC Progress + Substitution Lemma + 8-constructor Preservation theorem** checked natively with `-dcore-lint -dstg-lint` (`692eae0778`)! |
| [DeBruijn](/DeBruijn/) | Intrinsically-typed `Term g a`, `rename`, `subst`, `substSingle`, promoted `Value` | `PLFH.Part2.DeBruijn.*` | <span class="badge badge-pass">Direct port</span> | Functional `Step` (`substSingle`, `R13_SubstSingleUOpenEq.hs`) and intrinsically-typed `progress` (`R03_ForEachGadt*.hs`) marked `[WIP NOTICE]` |
| [Inference](/Inference/) | `decEqTy`, `lookupCtx`, **`infer`**, **`check`** | `PLFH.Part2.Inference.*` | <span class="badge badge-pass">Direct port</span> | Full certified STLC inference & checking with direct inline `case lTy of` refinement (no `matchArr`/`matchNat` or `@g @a @b` needed on `692eae0778`!) |
| [Untyped](/Untyped/) | `Fin`, `UTerm`, `renameU`, `substU`, relational `SubstAtU`, promoted `Neutral`/`Normal`/`BetaStep`, `idAppStep`, `omegaStep` | `PLFH.Part2.Untyped.*` | <span class="badge badge-pass">Direct port</span> | Sound relational `SubstAtU` verified by `NegBadBetaStep`; functional `substSingleU` tracked in `R13_SubstSingleUOpenEq.hs`; normalizer blocked by `R03_ForEachGadt*.hs` |
| [More](/More/) | Extended STLC (`Let`, `Unit`, `Prod`, `Sum`, `Void`, `List`), `substSingle`/`substDouble`, promoted `Value` | `PLFH.Part2.More.*` | <span class="badge badge-pass">Direct port</span> | Functional `Step` (`substSingle`/`substDouble`, `R13_SubstSingleUOpenEq.hs`) marked `[WIP NOTICE]` |
| [Bisimulation](/Bisimulation/) | `SimRel`, `Leg`, `simValueLam`, **`simValue`** | `PLFH.Part2.Bisimulation.*` | <span class="badge badge-pass">Direct port</span> | Full `simValue` across promoted GADT indices passes Core/STG Lint (`R11_MixedKindCoercionCoreLint.hs` fixed!) |
| [BigStep](/BigStep/) | Call-by-name `Env`, `Clos`, `lookupEnv`, `EnvLookup`, `EvalBig`, `evalBigIsLam`, **`envLookupDeterm`**, **`evalDeterm`**, `evalIdApp`, `evalConstOmega` | `PLFH.Part2.BigStep.*` | <span class="badge badge-pass">Direct port</span> | **Full call-by-name determinism (`evalDeterm`) checked** (`R11_MixedKindCoercionCoreLint.hs` fixed!); functional `lookupEnv` in `EVar` remains `R13_LookupEnvOpenEq.hs` |
| [Substitution](/Substitution/) | `Rename`, `Subst`, `ids`, `shift`, `ren`, `consSubst`, `seqSubst` | `PLFH.Part2.Substitution.*` | <span class="badge badge-pass">Direct port</span> | Equational σ-calculus proofs wait on R03/R13 |
| [Confluence](/Confluence/) | `Par` (sound `SubstAtU`), `ParSteps`, `parToBetas`, `parsToBetas`, `omegaPar`, `Joinable`, **`strip`**, **`parConfluence`**, **`churchRosser`** | `PLFH.Part2.Confluence.*` | <span class="badge badge-pass">Direct port</span> | `churchRosser` proves full Church-Rosser for `BetaSteps` from `betaToPar` + 1-step diamond; `parRefl`/`parDiamond` remain open (R03/R13) |
| [Denotational](/Denotational/) | GADT `Value`, `ValW`, `Sub`, `subRefl`, `joinArrDist`, `ValMem`, `Fun`, ordinary `dom`/`cod`, **`subInvTrans`**, direct nested **`subInvDist`**, **`subInv`**, **`arrSubArrInv`**, `ValEnv`, `Denotes`, `denotDelta`/`Omega`, `envSubMono`, `upEnv`, `DenEq` | `PLFH.Part3.Denotational.*` | <span class="badge badge-pass">Direct port</span> | GADT `Value` (`R13_GadtSyntaxBreaksOpenEq.hs`) + direct nested dependent `case` `subInvDist` (`9cc4065fab`, `R03_NestedDepCaseCoreLint.hs`) both fixed! |
| [Compositional](/Compositional/) | `LamDen`, **`subLamDen`**, **`denLamToF`**, **`lamInversion`**, **`fToDenLam`**, **`lamEquiv`**, **`lamCong`**, `AppDen`, **`subAppDen`**, **`joinAppDen`**, **`denAppToAppDen`**, **`appDenToDenApp`**, **`appEquiv`**, **`appCong`**, `UCtx`, `plug` | `PLFH.Part3.Compositional.*` | <span class="badge badge-pass">Direct port</span> | **BOTH** lambda AND application compositionality (`lamEquiv`/`lamCong` + `appEquiv`/`appCong`) 100% checked! `compositionality` over `plug` remains open (R03/R13) |
| [Soundness](/Soundness/) | **`denotPreserve`**, **`denotPreserveMulti`**, **`denotReflect`**, **`denotReflectMulti`**, **`denotEquivSteps`** | `PLFH.Part3.Soundness.*` | <span class="badge badge-pass">Direct port</span> | **BOTH** forward preservation & backward subject expansion proved over sound `BetaStep` conditional on `BetaPres`/`BetaReflect` |
| [Adequacy](/Adequacy/) | `AboveFun`, **`notAboveFunBot`**, **`aboveFunJoin`**, **`decAboveFun`**, `WHNF`, `HaltsV`, **`LogE`/`LogVLam`**, `notAboveFunLogV`, **`haltsVJoin`**, **`subLogVLam`**, **`subLogE`**, **`fundamental`**, **unconditional `adequacyBigStep`**, **`adequacyIdApp`** | `PLFH.Part3.Adequacy.*` | <span class="badge badge-pass">Direct port</span> | **100% UNCONDITIONAL Big-Step Adequacy (`adequacyBigStep`)** via `BigStep.evalDeterm` — all 8 `Sub` rules, all 6 `Denotes` rules, executes at runtime on `id · id`! |
| [ContextualEquivalence](/ContextualEquivalence/) | `Terminates`, `denotEqualTerminates`, `denotEqualCtxEquiv`, `denotEqualCtxEquivFromSoundness` | `PLFH.Part3.ContextualEquivalence.*` | <span class="badge badge-pass">Direct port</span> | Connects directly to `Soundness.denotEquivSteps` (conditional on upstream Part 3 premises) |

## Negative Controls (5 Verified Rejections)

| Control File | Claimed Falsehood | Expected Diagnostic |
| --- | --- | --- |
| `hs/negative/NegZeroSucc.hs` | `'Zero :~: 'Succ 'Zero` | `GHC-83865` |
| `hs/negative/NegOneLeZero.hs` | `LE ('Succ 'Zero) 'Zero` | `GHC-83865` |
| `hs/negative/NegIllTypedApp.hs` | `HasType 'CEmpty ('App 'TZero 'TZero) 'TNat` | `GHC-83865` |
| `hs/negative/NegBetaMuTarget.hs` | `Step ('TMu 'Zero 'TZero) ('TCase ...)` (bogus β-target) | `GHC-83865` |
| `hs/negative/NegBadBetaStep.hs` | `BetaStep ('UApp IdTerm IdTerm) OmegaTerm` | `GHC-83865` |

## Fixed Reproducers (15 Verified Regressions at `-O0` & `-O2`)

All 15 fixed reproducers are preserved under [`reproducers/fixed/`](https://github.com/Tritlo/PLFH/tree/main/reproducers/fixed) and compiled at **both `-O0` and `-O2`** with `-dcore-lint -dstg-lint` on every test run so fixes can never regress:

| Reproducer (`reproducers/fixed/`) | Serokell Card | Historical Failure (`db2586fdc2`–`9cc4065fab`) | Published Fix (`692eae0778` / `9cc4065fab` / `63e2f0974b`) |
| --- | --- | --- | --- |
| `R03_TcInstFunPanic.hs` | R03 / Compiler bug | **GHC panic!** (`App.hs:3947`) | Fixed — `substP @Even (toEqP (plusComm m n)) ev` in `Equality` |
| `R05_SubstTyEtaAliasPanic.hs` | R05 / Compiler bug | **GHC panic!** (`Subst.hs:900`) | Fixed — eta-reduced `lengthReverseLaw = lengthReverse` in `Lists` |
| `R11_MixedKindCoercionCoreLint.hs` | R11 / Core Lint bug | **Core Lint error!** (Desugar) | Fixed — unlocks `Bisimulation.simValue`, `BigStep.evalDeterm`, & unconditional `Adequacy`! |
| `R03_NestedDepCaseCoreLint.hs` | R03 / Core Lint bug | **Core Lint error!** (Desugar) | Fixed (`9cc4065fab`) — direct nested dependent `case` in `Denotational.subInvDist` |
| `R13_GadtSyntaxBreaksOpenEq.hs` | R13 / R16 | `GHC-68947` | Fixed — GADT `Value` works directly with `dom`/`cod` in `Denotational` |
| `R13_EqSizeOpenEq.hs` | R13 / R16 | `GHC-70565` | Fixed — `eqSize` / `HaskLib.Nat.eqSizeRefl` |
| `R13_DownFromOpenEq.hs` | R13 / R16 | `GHC-68947` | Fixed — `downFrom` / `zeros` / `lengthDownFrom` in `Lists` |
| `R13_SubstTermOpenEq.hs` | R13 / R16 | `GHC-70565` | Fixed (`692eae0778`) — same-module `substTerm` unlocks STLC Progress & Preservation! |
| `R13_MonusOpenEq.hs` | R13 / R16 | `GHC-70565` | Fixed (`63e2f0974b`) — right-first `monus` equations unlock `zeroMonus` & `monusPlusAssoc` in `Induction`! |
| `R03_CongPartialApp.hs` | R03 / R17 / R23 | Untouchable meta | Fixed — `cong @(plus m)` in `Induction.plusRearrange` |
| `R03_WithEqualityUnderTrans.hs` | R03 | Untouchable meta | Fixed — `rewrite (plusComm m n) Refl` inside `trans` in `Induction.plusSwap` |
| `R03_CaseRefinementMultiIndexGadt.hs` | R03 | `GHC-83605` | Fixed — inline `case lTy of` refinement in `Inference.infer` |
| `R03_UntouchableUnderRetainedApp.hs` | R03 | `GHC-83865` | Fixed — `MkTyped b (App l' m')` without explicit `@g @a @b` in `Inference.infer` |
| `R04_SigmaUnderForEach.hs` | R04 | Rejected sum position | Fixed — inline `some (k :: Nat) \| k :~: plus m n` in `Decidable.plusExists` |
| `R04_HigherRankForEachField.hs` | R03 / R04 | `GHC-83865` (identical types!) | Fixed — `isoSizeRefl` & `isoSizeSym` over `MkIsoSize` in `Isomorphism` |

## Open Minimal Compiler-Gap Reproducers (15 Tracked)

Every open reproducer lives under [`reproducers/`](https://github.com/Tritlo/PLFH/tree/main/reproducers) and is mirrored to `docs/dependent-haskell/plfh/reproducers/` in `Tritlo/ghc`:

| Reproducer (`reproducers/`) | Serokell Card | Diagnostic (`63e2f0974b`) | Summary |
| --- | --- | --- | --- |
| `R03_ForEachGadtEqTypeFamily.hs` | R03 / Typechecker bug | `GHC-05617` | Given GADT equality (`u :~: v`, `u :~: 'Zero`) under retained `foreach` fails to rewrite closed type family `F u` (erased `forall` passes!) |
| `R04_EtaAliasForEachFunctionBinder.hs` | R04 / R05 / **NEW!** | `GHC-83865` (identical types!) | Eta-reduced alias `lengthMapLaw = lengthMap` with function-valued `foreach (f :: a -> b)` prints identical expected/actual types (while `lengthReverseLaw = lengthReverse` passes!) |
| `R13_ShuntAccumOpenEq.hs` | R13 / R16 | `GHC-83605` (`-O2` only) | Passes `-O0` and `-O2 -fno-enable-rewrite-rules` (checked in `Lists`), still blocked at default `-O2` by Prelude `(++)` rewrite-rule guard |
| `R13_WildcardBreaksOpenEq.hs` | R13 / R16 | `GHC-70565` | `timesWild Zero _ = Zero` fails open evaluation while `timesNamed Zero n = Zero` succeeds |
| `R13_PowOpenEq.hs` | R13 / R16 | `GHC-70565` | `pow` (recursion on 2nd arg) fails open evaluation |
| `R13_RevOpenEq.hs` | R13 / R16 | `GHC-70565` | Naive quadratic `rev (x:xs) = app (rev xs) [x]` fails open evaluation |
| `R13_SubstSingleUOpenEq.hs` | R13 / R16 | `GHC-68947` | Higher-order GADT-indexed `substSingleU` on `UTerm n` has no checked type-level equations |
| `R13_LookupEnvOpenEq.hs` | R13 / R16 | `GHC-68947` | GADT-indexed `lookupEnv e x` in `EVar` has no checked type-level equations |
| `R03_SecondColumnPattern.hs` | R03 | `GHC-83605` | Constructor equations cannot split a non-leading retained argument |
| `R03_FunctionColumnSplit.hs` | R03 | `GHC-83605` | Multi-equation constructor split after a retained function binder rejected |
| `R03_FoldrRetainedIndex.hs` | R03 | `GHC-83605` | `foldrL plus Zero xs` rejected as a retained runtime argument |
| `R03_ForEachGadtEquations.hs` | R03 | `GHC-83605` | `foreach (m :: Term 'CEmpty a)` equations rejected on indexed GADT domain |
| `R03_ForEachGadtCase.hs` | R03 | `GHC-83865` / mismatch | `case m of` on `foreach (m :: Term 'CEmpty a)` does not refine `m` |
| `R04_PolyFunctionFieldInIso.hs` | R03 / R04 | `GHC-83605` | Polymorphic `foreach (to :: a -> b)` rejected in `Iso` constructor |
| `R23_MatchabilityInLeibniz.hs` | R23 | `GHC-83865` | Matchable `EqP x :: a -> Type` cannot instantiate `a %U -> Type` directly |
