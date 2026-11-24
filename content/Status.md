---
title: "Yardstick Status Ledger"
prev: /ContextualEquivalence/
next: /Citing/
src: content/Status.md
---

This page tracks every PLFA (`v19.08` and `v22.08`) declaration, theorem, and
exercise attempted in PLFH against the experimental Dependent Haskell compiler
([`Tritlo/ghc`, branch `dependent-haskell`](https://github.com/Tritlo/ghc/tree/dependent-haskell)).

- **Current published compiler:** GHC `10.1.20261115.1`, commit `1a02a866e7` (590 checkpoint; previous baselines: 588 `d15cbd41fe`, 585 `db2586fdc2`) + `HaskLib.rewrite` (`0c52fec229`).
- **Pending compiler team fixes:** **8 of our first 23 reproducers** already pass on the compiler team's combined private candidate `d033d0132d` (5 queued in normal 594 build `984647892b` / job 2209: `R03_TcInstFunPanic.hs`, `R05_SubstTyEtaAliasPanic.hs`, `R03_CongPartialApp.hs`, `R03_WithEqualityUnderTrans.hs`, `R04_SigmaUnderForEach.hs`; plus 3 further fixes: `R13_EqSizeOpenEq.hs`, `R04_HigherRankForEachField.hs`, and `R11_MixedKindCoercionCoreLint.hs`!). As each combined checkpoint publishes, we upgrade the corresponding `[WIP NOTICE]` blocks while keeping historical failure records visible here.
- **Verification mode:** Native `-O0 -fomit-interface-pragmas -fno-write-if-simplified-core -dcore-lint -dstg-lint`.
- **Proof discipline:** Zero typed holes, zero `-fdefer-type-errors`, zero `undefined`/`error`, zero circular bindings, zero `unsafeCoerce`.
- **Policy on gaps:** Avoid workarounds; mark unsupported items `[WIP NOTICE]` and maintain a minimal standalone reproducer under [`reproducers/`](https://github.com/Tritlo/PLFH/tree/main/reproducers).

## Chapter-by-Chapter Declaration Ledger

| Chapter (Edition) | PLFA Declaration | PLFH Module & Symbol | Category | Notes / Serokell Card |
| --- | --- | --- | --- | --- |
| [Naturals](/Naturals/) (`19.08`) | `ℕ` (`zero`, `suc`), `_+_` | `HaskLib.Size.{Size,plus}` | <span class="badge badge-reuse">HaskLib reuse</span> | `HaskLib.Nat` + `FromNatural` decimal literals upcoming |
| [Naturals](/Naturals/) (`19.08`) | `2 + 3 ≡ 5`, `_*_`, `Bin`, `inc`, `to`, `from` | `PLFH.Part1.Naturals.*` | <span class="badge badge-pass">Direct port</span> | `times` needs named `n` (wildcard `_` hits R13/R16) |
| [Naturals](/Naturals/) (`19.08`) | `_^_`, `_∸_` open type eval | `PLFH.Part1.Naturals.{pow,monus}` | <span class="badge badge-wip">Blocker (open)</span> | Runtime OK; open type eval blocked (`R13_PowOpenEq.hs`, `R13_MonusOpenEq.hs`) |
| [Induction](/Induction/) (`19.08`) | `+-assoc`, `+-assoc′` (`HaskLib.rewrite`), `+-identityʳ`, `+-suc`, `+-comm`, `+-rearrange`, `+-swap`, `*-distrib-+`, `*-assoc`, `*-comm`, `Bin-laws` | `PLFH.Part1.Induction.*` + `HaskLib.Size.{plusZero,plusSucc}` | <span class="badge badge-pass">Direct port</span> | Uses `HaskLib.rewrite` (`0c52fec229`); `cong @(plus m)` & nested `withEquality` fixed in private 594 |
| [Induction](/Induction/) (`19.08`) | `0∸n≡0`, `∸-+-assoc`, `+*^` | — | <span class="badge badge-wip">Blocker</span> | Blocked by open equations for `monus` and `pow` (R13/R16) |
| [Relations](/Relations/) (`19.08`) | `_≤_`, `inv-*`, `≤-refl/trans/antisym`, `Total`, `+-mono-*`, `_<_`, `<-trans`, `Trichotomy`, `ltToLe`/`leToLt`, `DiffWitness`, `Even`/`Odd` + sums, canonical `One`/`Can` + `incOne`/`incCan` | `PLFH.Part1.Relations.*` | <span class="badge badge-pass">Direct port</span> | All checked directly! |
| [Equality](/Equality/) (`19.08`) | `_≡_`, `sym`, `trans`, `cong`, `cong-app`, `subst`, `RequiredTypeArguments` chains (`beginEq`/`stepEq`/`qedEq`), `evenComm`, `Leibniz`, `LeibnizU`, `leibnizUSym` | `PLFH.Part1.Equality.*` | <span class="badge badge-pass">Direct port</span> | Inline type lambda `@(\z -> EqP z x)` works (R17)! `substP @Even` panic fixed in private 594 |
| [Isomorphism](/Isomorphism/) (`19.08`) | `_⇔_` (`Iff`, refl/sym/trans), `IsoSize` decl | `PLFH.Part1.Isomorphism.*` | <span class="badge badge-pass">Direct port</span> | Monomorphic `IsoSize` declares cleanly |
| [Isomorphism](/Isomorphism/) (`19.08`) | Polymorphic `_≃_`, `_≲_`, `MkIsoSize` | — | <span class="badge badge-wip">Blocker</span> | `R04_PolyFunctionFieldInIso.hs` (open); `R04_HigherRankForEachField.hs` fixed in private `d033d0132d` |
| [Connectives](/Connectives/) (`19.08`) | `×`, `⊎`, `⊤`, `⊥`, comm/assoc/distrib/currying | `PLFH.Part1.Connectives.*` | <span class="badge badge-pass">Direct port</span> | All laws checked over standard `(,)`, `Either`, `()`, `Void` |
| [Negation](/Negation/) (`19.08`) | `¬`, double/triple neg, De Morgan, `EM ⇔ DNE ⇔ Peirce`, `ltIrrefl`/`ltAsym` | `PLFH.Part1.Negation.*` | <span class="badge badge-pass">Direct port</span> | All intuitionistic & classical equivalences checked |
| [Quantifiers](/Quantifiers/) (`19.08`) | `Exists`, `existsDistribSum`, quantifier De Morgan, `EvenSigma`, `evenToWitness` | `PLFH.Part1.Quantifiers.*` | <span class="badge badge-pass">Direct port</span> | Retained `EvenSigma` (`some`) + `evenToWitness` checked |
| [Decidable](/Decidable/) (`19.08`) | `¬`, `Dec`, `_≟_`, `_≤?_`, `decEven`, `decOdd`, `Reflects`, `reflectsToDec`, `SizeWitness` | `PLFH.Part1.Decidable.*` | <span class="badge badge-pass">Direct port</span> | Inline `foreach ... -> some ...` (`R04_SigmaUnderForEach.hs`) fixed in private 594 |
| [Lists](/Lists/) (`19.08`) | `++-assoc`, `++-identityʳ`, `HaskLib` length laws, `map-++`/`compose`/`id`, `All`, `Any`, `In`, `allAppend`/`Inv`, `anyAppend*`/`Inv`, `decAll`, `decAny` | `PLFH.Part1.Lists.*` + `HaskLib` | <span class="badge badge-pass">Direct port</span> | Uses ordinary Prelude `[a]`, `(++)`, `map`! Eta-alias panic fixed in private 594 |
| [Lists](/Lists/) (`19.08`) | `rev`, `shunt-++`, `downFrom`, `foldr-monoid-++`, `All (\x -> Not (p x))` | — | <span class="badge badge-wip">Blocker</span> | `R13_RevOpenEq.hs`, `R13_ShuntAccumOpenEq.hs`, `R13_DownFromOpenEq.hs`, `R03_FoldrRetainedIndex.hs`, `R23_MatchabilityInLeibniz.hs` |
| [Lambda](/Lambda/) (`19.08`) | `Term`, `Type`, `Context`, `Value`, `_—→_`, `_—↠_`, `_∋_⦂_`, `_⊢_⦂_` | `PLFH.Part2.Lambda.*` | <span class="badge badge-pass">Direct port</span> | Open reduction of `substTerm` blocked (`R13_SubstTermOpenEq.hs`) |
| [Properties](/Properties/) (`19.08`) | `Canonical`, `canonical`, **Progress**, `extCtx`, `renameTyping`, `weakenTyping`, `dropTyping`, `swapTyping` | `PLFH.Part2.Properties.*` | <span class="badge badge-pass">Direct port</span> | Full closed STLC Progress checked! Preservation blocked by `R13_SubstTermOpenEq.hs` |
| [DeBruijn](/DeBruijn/) (`19.08`) | Intrinsically-typed `Term g a`, `rename`, `subst`, promoted `Value`/`Step`/`Progress` | `PLFH.Part2.DeBruijn.*` | <span class="badge badge-pass">Direct port</span> | Intrinsically-typed `progress` blocked by `R03_ForEachGadt*.hs` |
| [Inference](/Inference/) (`19.08`) | `decEqTy`, `lookupCtx`, **`infer`**, **`check`** | `PLFH.Part2.Inference.*` | <span class="badge badge-pass">Direct port</span> | Full certified STLC inference & checking (verified at runtime too!) |
| [Untyped](/Untyped/) (`19.08`) | `Fin`, `UTerm`, `renameU`, `substU`, promoted `Neutral`/`Normal`/`BetaStep` | `PLFH.Part2.Untyped.*` | <span class="badge badge-pass">Direct port</span> | Normalizer over `foreach (t :: UTerm n)` blocked by `R03_ForEachGadt*.hs` |
| [More](/More/) (`19.08`) | Extended STLC (`Let`, `Unit`, `Prod`, `Sum`, `Void`, `List`), promoted `Value`/`Step` | `PLFH.Part2.More.*` | <span class="badge badge-pass">Direct port</span> | Full extended STLC compiles! |
| [Bisimulation](/Bisimulation/) (`19.08`) | `SimRel`, `Leg`, `simValueLam` | `PLFH.Part2.Bisimulation.*` | <span class="badge badge-pass">Direct port</span> | General `simValue` hits `R11_MixedKindCoercionCoreLint.hs` on 590 (fixed in private `f21ab22285`!) |
| [BigStep](/BigStep/) (`22.08`) | Call-by-name `Env`, `Clos`, `lookupEnv`, `EnvLookup`, `EvalBig`, `evalIdApp`, `evalConstOmega` | `PLFH.Part2.BigStep.*` | <span class="badge badge-pass">Direct port</span> | Functional `lookupEnv` hits `R13_LookupEnvOpenEq.hs`; `evalDeterm` hits `R11_MixedKindCoercionCoreLint.hs` |
| [Substitution](/Substitution/) (`22.08`) | `Rename`, `Subst`, `ids`, `shift`, `ren`, `consSubst`, `seqSubst` | `PLFH.Part2.Substitution.*` | <span class="badge badge-pass">Direct port</span> | Equational σ-calculus proofs wait on R03/R13 |
| [Confluence](/Confluence/) (`22.08`) | `Par`, `ParSteps`, `parToBetas`, `parsToBetas`, `Joinable`, **`strip`**, **`parConfluence`** | `PLFH.Part2.Confluence.*` | <span class="badge badge-pass">Direct port</span> | `parConfluence` proves **Diamond ⇒ Confluence** (takes 1-step diamond as hypothesis); `parRefl`/`parDiamond` remain open (R03/R11/R13) |
| [Denotational](/Denotational/) (`22.08`) | `Value`, `Sub`, `subRefl`, `joinArrDist`, `ValMem`, `Fun`, ordinary `dom`/`cod`, **`subInvTrans`**, **`subInv`**, **`arrSubArrInv`**, `ValEnv`, `Denotes`, `denotDelta`/`Omega`, `envSubMono`, `upEnv`, `DenEq` | `PLFH.Part3.Denotational.*` | <span class="badge badge-pass">Direct port</span> | Full `subInv` & `↦⊑↦-inv` checked! Uncovered `R13_GadtSyntaxBreaksOpenEq.hs` & `R03_NestedDepCaseCoreLint.hs` |
| [Compositional](/Compositional/) (`22.08`) | `LamDen`, **`subLamDen`**, **`denLamToF`**, **`lamInversion`**, **`fToDenLam`**, **`lamEquiv`**, **`lamCong`**, `AppDen`, `appDenToDenApp`, `appDenCong`, `UCtx`, `plug` | `PLFH.Part3.Compositional.*` | <span class="badge badge-pass">Direct port</span> | Full lambda compositionality & inversion checked! `denAppToAppDen` & `compositionality` over `plug` remain open (R03/R13) |
| [Soundness](/Soundness/) (`22.08`) | `denotPreserve`, `denotPreserveMulti` | `PLFH.Part3.Soundness.*` | <span class="badge badge-pass">Direct port</span> | Structural preservation proved conditional on `BetaPres` (using `lamInversion`); `substPres` & subject expansion open (R03/R13) |
| [Adequacy](/Adequacy/) (`22.08`) | `AboveFun`, `aboveFunSub`, **`notAboveFunBot`**, **`aboveFunJoin`**, **`decAboveFun`**, `WHNF`, `HaltsV`, **`LogE`/`LogV`**, `notAboveFunLogV` | `PLFH.Part3.Adequacy.*` | <span class="badge badge-pass">Direct port</span> | Full `AboveFun` decidability & negative-position `LogV`/`LogE` type family checked! `sub-𝕍`/fundamental lemma wait on `evalDeterm` (R11) & R03 |
| [ContextualEquivalence](/ContextualEquivalence/) (`22.08`) | `Terminates`, `denotEqualTerminates`, `denotEqualCtxEquiv` | `PLFH.Part3.ContextualEquivalence.*` | <span class="badge badge-pass">Direct port</span> | Exact reduction from compositionality, soundness, and adequacy checked (conditional on upstream Part 3 premises) |

## Negative Controls (Verified Rejections)

| Control File | Claimed Falsehood | Expected Diagnostic |
| --- | --- | --- |
| `hs/negative/NegZeroSucc.hs` | `'Zero :~: 'Succ 'Zero` | `GHC-83865` |
| `hs/negative/NegOneLeZero.hs` | `LE ('Succ 'Zero) 'Zero` | `GHC-83865` |
| `hs/negative/NegIllTypedApp.hs` | `HasType 'CEmpty ('App 'TZero 'TZero) 'TNat` | `GHC-83865` |

## Minimal Compiler-Gap Reproducers (27 Tracked)

Every reproducer lives under [`reproducers/`](https://github.com/Tritlo/PLFH/tree/main/reproducers) and is mirrored to `docs/dependent-haskell/plfh/reproducers/` in `Tritlo/ghc`:

| Reproducer | Serokell Card | Diagnostic (Published `1a02a866e7` / `d15cbd41fe`) | Private Status / Summary |
| --- | --- | --- | --- |
| `R03_TcInstFunPanic.hs` | R03 / Compiler bug | **GHC panic!** (`App.hs:3947`) | **Fixed in private 594 (`984647892b`)** — `substP @Even (toEqP (plusComm m n)) ev` |
| `R05_SubstTyEtaAliasPanic.hs` | R05 / Compiler bug | **GHC panic!** (`Subst.hs:900`) | **Fixed in private 594 (`984647892b`)** — eta-reduced `lengthReverseLaw = lengthReverse` |
| `R11_MixedKindCoercionCoreLint.hs` | R11 / Core Lint bug | **Core Lint error!** (Desugar) | **Fixed in private `f21ab22285` / `d033d0132d`** — matching two GADTs over promoted `Term`/`Env` (`simValue`, `envLookupDeterm`) |
| `R03_NestedDepCaseCoreLint.hs` | R03 / Core Lint bug | **Core Lint error!** (Desugar, NEW!) | **Open** — nested dependent `case` on two fields of a retained constructor leaves coercion variable `co_...` out of scope |
| `R13_GadtSyntaxBreaksOpenEq.hs` | R13 / R16 | `GHC-68947` (NEW!) | **Open** — identical plain ADT `Val` gets R13 equations under H98 syntax (`data ValH = ...`) but fails under GADT syntax (`data ValG where ...`) |
| `R13_WildcardBreaksOpenEq.hs` | R13 / R16 | `GHC-70565` | **Open** — `timesWild Zero _ = Zero` fails open evaluation while `timesNamed Zero n = Zero` succeeds |
| `R13_MonusOpenEq.hs` | R13 / R16 | `GHC-70565` | **Open** — `monus` fails open evaluation (even if first-arg-first) |
| `R13_PowOpenEq.hs` | R13 / R16 | `GHC-70565` | **Open** — `pow` (recursion on 2nd arg) fails open evaluation |
| `R13_EqSizeOpenEq.hs` | R13 / R16 | `GHC-70565` | **Fixed in private `d033d0132d`** — `eqSize` (unguarded tail recursion returning `Bool`) |
| `R13_RevOpenEq.hs` | R13 / R16 | `GHC-70565` | **Open** — naive quadratic `rev (x:xs) = app (rev xs) [x]` fails open evaluation |
| `R13_ShuntAccumOpenEq.hs` | R13 / R16 | `GHC-68947` (NEW!) | **Open** — tail-recursive accumulating `shunt (x:xs) ys = shunt xs (x : ys)` changes accumulator arg |
| `R13_DownFromOpenEq.hs` | R13 / R16 | `GHC-68947` (NEW!) | **Open** — `Size -> [Size]` recursion (`downFrom (Succ n) = n : downFrom n`, even `zeros`) |
| `R13_SubstTermOpenEq.hs` | R13 / R16 | `GHC-70565` | **Open** — `substTerm` (branching on computed `case eqSize x y of`) — blocks STLC Preservation |
| `R13_LookupEnvOpenEq.hs` | R13 / R16 | `GHC-68947` | **Open** — GADT-indexed `lookupEnv e x` in `EVar` has no checked type-level equations |
| `R03_SecondColumnPattern.hs` | R03 | `GHC-83605` | **Open** — constructor equations cannot split a non-leading retained argument |
| `R03_FunctionColumnSplit.hs` | R03 | `GHC-83605` | **Open** — multi-equation constructor split after a retained function binder rejected |
| `R03_CongPartialApp.hs` | R03 / R17 / R23 | Untouchable meta | **Fixed in private 594 (`984647892b`)** — `cong @(plus m)` |
| `R03_WithEqualityUnderTrans.hs` | R03 | Untouchable meta | **Fixed in private 594 (`984647892b`)** — `withEquality (plusComm m n) Refl` inside `trans` |
| `R03_FoldrRetainedIndex.hs` | R03 | `GHC-83605` | **Open** — `foldrL plus Zero xs` rejected as a retained runtime argument |
| `R03_ForEachGadtEquations.hs` | R03 | `GHC-83605` | **Open** — `foreach (m :: Term 'CEmpty a)` equations rejected on indexed GADT domain |
| `R03_ForEachGadtCase.hs` | R03 | `GHC-25897` / mismatch | **Open** — `case m of` on `foreach (m :: Term 'CEmpty a)` does not refine `m` |
| `R03_CaseRefinementMultiIndexGadt.hs` | R03 | `GHC-83605` | **Open** — nested `case mt of Just (MkTyped t m) -> case t of` fails on `Term g t` |
| `R03_UntouchableUnderRetainedApp.hs` | R03 | `GHC-83865` | **Open** — `MkTyped b (App lArr m)` inside `Refl` fails with untouchable `g0`/`a0` |
| `R04_SigmaUnderForEach.hs` | R04 | Rejected sum position | **Fixed in private 594 (`984647892b`)** — inline `some (k :: Size) \| k :~: plus m n` under `foreach` |
| `R04_PolyFunctionFieldInIso.hs` | R03 / R04 | `GHC-83605` | **Open** — polymorphic `foreach (to :: a -> b)` rejected in `Iso` constructor |
| `R04_HigherRankForEachField.hs` | R03 / R04 | `GHC-83865` (identical types!) | **Fixed in private `d033d0132d`** — `MkIsoSize idSize idSize idSizeId idSizeId` |
| `R23_MatchabilityInLeibniz.hs` | R23 | `GHC-83865` | **Open** — matchable `EqP x :: a -> Type` cannot instantiate `a %U -> Type` directly |
