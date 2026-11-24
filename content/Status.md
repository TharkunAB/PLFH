---
title: "Yardstick Status Ledger"
prev: /DeBruijn/
next: /Citing/
src: content/Status.md
---

This page tracks every PLFA `v19.08` declaration, theorem, and exercise
attempted in PLFH against the experimental Dependent Haskell compiler
([`Tritlo/ghc`, branch `dependent-haskell`](https://github.com/Tritlo/ghc/tree/dependent-haskell)).

- **Baseline compiler:** GHC `10.1.20261115.1`, commit `db2586fdc2f391829174a5652d8744e9a9b761f8`
- **Verification mode:** Native `-O0 -fomit-interface-pragmas -fno-write-if-simplified-core -dcore-lint -dstg-lint`
- **Proof discipline:** Zero typed holes, zero `-fdefer-type-errors`, zero `undefined`/`error`, zero circular bindings, zero `unsafeCoerce`.
- **Policy on gaps:** Avoid workarounds; mark unsupported items `[WIP NOTICE]` and maintain a minimal standalone reproducer under [`reproducers/`](https://github.com/Tritlo/PLFH/tree/main/reproducers).

## Chapter-by-Chapter Declaration Ledger

| Chapter | PLFA `v19.08` Declaration | PLFH Module & Symbol | Category | Notes / Serokell Card |
| --- | --- | --- | --- | --- |
| [Naturals](/Naturals/) | `ℕ` (`zero`, `suc`) | `HaskLib.Size.Size` (`Zero`, `Succ`) | <span class="badge badge-reuse">HaskLib reuse</span> | Same Peano datatype |
| [Naturals](/Naturals/) | `_+_` | `HaskLib.Size.plus` | <span class="badge badge-reuse">HaskLib reuse</span> | Recursion on first argument |
| [Naturals](/Naturals/) | `2 + 3 ≡ 5` | `PLFH.Part1.Naturals.twoPlusThree` | <span class="badge badge-pass">Direct port</span> | Checked via `Refl` |
| [Naturals](/Naturals/) | `_*_` | `PLFH.Part1.Naturals.times` | <span class="badge badge-pass">Direct port</span> | Requires named `n` (wildcard `_` hits R13/R16) |
| [Naturals](/Naturals/) | `_^_` | `PLFH.Part1.Naturals.pow` | <span class="badge badge-wip">Blocker (open)</span> | Runtime OK; open type eval blocked (`R13_PowOpenEq.hs`, R13/R16) |
| [Naturals](/Naturals/) | `_∸_` | `PLFH.Part1.Naturals.monus` | <span class="badge badge-wip">Blocker (open)</span> | Runtime OK; open type eval blocked (`R13_MonusOpenEq.hs`, R13/R16) |
| [Naturals](/Naturals/) | `Bin`, `inc`, `to`, `from` | `PLFH.Part1.Naturals.{Bin,inc,toBin,fromBin}` | <span class="badge badge-pass">Direct port</span> | All three functions get open source equations! |
| [Induction](/Induction/) | `+-assoc` | `PLFH.Part1.Induction.plusAssoc` | <span class="badge badge-pass">Direct port</span> | Exact spelling from `PROMPT.md`, imported & used in `InductionClient` |
| [Induction](/Induction/) | `+-assoc′` (`rewrite`) | `PLFH.Part1.Induction.plusAssocRewrite` | <span class="badge badge-pass">Direct port</span> | Uses `HaskLib.withEquality` |
| [Induction](/Induction/) | `+-identityʳ` | `HaskLib.Size.plusZero` (`plusIdentityR`) | <span class="badge badge-reuse">HaskLib reuse</span> | Reused directly from `HaskLib.Size` |
| [Induction](/Induction/) | `+-suc` | `HaskLib.Size.plusSucc` (`plusSuc`) | <span class="badge badge-reuse">HaskLib reuse</span> | Reused directly from `HaskLib.Size` |
| [Induction](/Induction/) | `+-comm` | `PLFH.Part1.Induction.plusComm` | <span class="badge badge-pass">Direct port</span> | Uses `case n of` (2nd-column equation split hits R03) |
| [Induction](/Induction/) | `+-rearrange` | `PLFH.Part1.Induction.plusRearrange` | <span class="badge badge-pass">Direct port</span> | Uses `congSecond @plus @m` (`cong @(plus m)` hits R03/R17/R23) |
| [Induction](/Induction/) | `+-swap` | `PLFH.Part1.Induction.plusSwap` | <span class="badge badge-pass">Direct port</span> | Uses `congFirst @plus @p` (nested `withEquality` hits R03) |
| [Induction](/Induction/) | `*-distrib-+`, `*-assoc`, `*-comm` | `PLFH.Part1.Induction.times*` | <span class="badge badge-pass">Direct port</span> | All 5 multiplication lemmas checked directly! |
| [Induction](/Induction/) | `0∸n≡0`, `∸-+-assoc`, `+*^` | — | <span class="badge badge-wip">Blocker</span> | Blocked by open source equations for `monus` and `pow` (R13/R16) |
| [Induction](/Induction/) | `Bin-laws` (`fromInc`, `fromTo`) | `PLFH.Part1.Induction.{fromInc,fromTo}` | <span class="badge badge-pass">Direct port</span> | Stretch exercise checked directly! |
| [Relations](/Relations/) | `_≤_`, `inv-s≤s`, `≤-refl`, `≤-trans`, `≤-antisym`, `Total`, `total` | `PLFH.Part1.Relations.*` | <span class="badge badge-pass">Direct port</span> | All checked directly |
| [Relations](/Relations/) | `+-monoʳ-≤`, `+-monoˡ-≤`, `+-mono-≤` | `PLFH.Part1.Relations.plusMono*` | <span class="badge badge-pass">Direct port</span> | Uses ordinary `plus` + `withEquality` |
| [Relations](/Relations/) | `_<_`, `<-trans`, `Trichotomy` | `PLFH.Part1.Relations.{LT',ltTrans,ltTrichotomy}` | <span class="badge badge-pass">Direct port</span> | Checked directly |
| [Relations](/Relations/) | `even`, `odd`, `even+even`, `odd+even`, `even+odd`, `odd+odd` | `PLFH.Part1.Relations.{Even,Odd,*Plus*}` | <span class="badge badge-pass">Direct port</span> | No `foreach` needed—GADT refinement suffices! |
| [Equality](/Equality/) | `_≡_`, `sym`, `trans`, `cong`, `cong-app`, `subst`, `even-comm` | `PLFH.Part1.Equality.*` | <span class="badge badge-pass">Direct port</span> | `substP @Even (toEqP (plusComm m n))` triggers a GHC panic (`R03_TcInstFunPanic.hs`); `withEquality` passes |
| [Equality](/Equality/) | Leibniz equality & symmetry | `PLFH.Part1.Equality.{Leibniz,LeibnizU,leibnizUSym}` | <span class="badge badge-pass">Direct port</span> | Inline type-level lambda `@(\z -> EqP z x)` works (R17)! Matchability subtyping noted (R23) |
| [Decidable](/Decidable/) | `¬`, `Dec`, `_≟_`, `_≤?_`, `Σ` | `PLFH.Part1.Decidable.*` | <span class="badge badge-pass">Direct port</span> | Inline `foreach ... -> some ...` hits R04 (`R04_SigmaUnderForEach.hs`); top-level `SizeWitness` passes |
| [Lists](/Lists/) | `++-assoc`, `++-identityʳ` | `PLFH.Part1.Lists.{appendAssoc,appendNilR}` | <span class="badge badge-pass">Direct port</span> | Uses **ordinary Prelude `(++)`**! |
| [Lists](/Lists/) | `length-++`, `length-map`, `length-reverse` | `HaskLib.{lengthAppend,lengthMap,lengthReverse}` | <span class="badge badge-reuse">HaskLib reuse</span> | Reused directly from `HaskLib` |
| [Lists](/Lists/) | `map-++`, `map-compose`, `map-id` | `PLFH.Part1.Lists.{mapAppend,mapCompose,mapId}` | <span class="badge badge-pass">Direct port</span> | Uses **ordinary Prelude `map` and `(.)`**! |
| [Lists](/Lists/) | `All`, `Any`, `_∈_`, `All-++`, `3 ∉ [0,1]` | `PLFH.Part1.Lists.{All,Any,In,allAppend,threeNotInList}` | <span class="badge badge-pass">Direct port</span> | Checked directly |
| [Lists](/Lists/) | `reverse`, `shunt-reverse`, `reverses` | — | <span class="badge badge-wip">Blocker</span> | `shunt` gets open eqs, but naive `rev` fails `GHC-70565` (`R13_RevOpenEq.hs`) |
| [Lists](/Lists/) | `foldr-monoid-++` | — | <span class="badge badge-wip">Blocker</span> | `foldrL plus Zero xs` rejected as retained index (`R03_FoldrRetainedIndex.hs`) |
| [Lambda](/Lambda/) | `Term`, `Type`, `Context`, `Value`, `_—→_`, `_—↠_`, `_∋_⦂_`, `_⊢_⦂_` | `PLFH.Part2.Lambda.*` | <span class="badge badge-pass">Direct port</span> | All syntax, reduction, and typing GADTs compile with `-dcore-lint -dstg-lint` |
| [Lambda](/Lambda/) | `_[_:=_]` open reduction | `PLFH.Part2.Lambda.substTerm` | <span class="badge badge-wip">Blocker (open)</span> | Accepted in `Step`, but open reduction fails `GHC-70565` (`R13_SubstTermOpenEq.hs`) |
| [Properties](/Properties/) | `Canonical`, `canonical` | `PLFH.Part2.Properties.{Canonical,canonical}` | <span class="badge badge-pass">Direct port</span> | Checked directly |
| [Properties](/Properties/) | `Progress`, `progress` | `PLFH.Part2.Properties.{Progress,progress}` | <span class="badge badge-pass">Direct port</span> | **Full closed well-typed Progress theorem checked!** |
| [Properties](/Properties/) | `ext`, `rename`, `weaken`, `drop`, `swap` | `PLFH.Part2.Properties.{extCtx,renameTyping,weakenTyping,dropTyping,swapTyping}` | <span class="badge badge-pass">Direct port</span> | All structural context lemmas checked directly |
| [Properties](/Properties/) | `subst` typing lemma & `preserve` | — | <span class="badge badge-wip">Blocker</span> | Blocked by open reduction of `substTerm` (`R13_SubstTermOpenEq.hs`, R13/R16) |
| [DeBruijn](/DeBruijn/) | `Type`, `Context`, `_∋_`, `_⊢_`, `ext`, `rename`, `exts`, `subst` | `PLFH.Part2.DeBruijn.*` | <span class="badge badge-pass">Direct port</span> | Intrinsically typed terms & type-preserving substitution checked directly |
| [DeBruijn](/DeBruijn/) | Promoted `Value`, `_—→_`, `Progress` over `Γ ⊢ A` | `PLFH.Part2.DeBruijn.{Value,Step,Progress}` | <span class="badge badge-pass">Direct port</span> | **GADT promotion of `Term g a` + `substSingle` compiles!** |
| [DeBruijn](/DeBruijn/) | Intrinsically-typed `progress :: foreach (m :: Term 'CEmpty a) -> Progress m` | — | <span class="badge badge-wip">Blocker</span> | `foreach` over indexed GADT domain blocked (`R03_ForEachGadt*.hs`, R03) |

## Negative Controls (Verified Rejections)

| Control File | Claimed Falsehood | Expected Diagnostic |
| --- | --- | --- |
| `hs/negative/NegZeroSucc.hs` | `'Zero :~: 'Succ 'Zero` | `GHC-83865` |
| `hs/negative/NegOneLeZero.hs` | `LE ('Succ 'Zero) 'Zero` | `GHC-83865` |
| `hs/negative/NegIllTypedApp.hs` | `HasType 'CEmpty ('App 'TZero 'TZero) 'TNat` | `GHC-83865` |

## Minimal Compiler-Gap Reproducers

Every reproducer lives under [`reproducers/`](https://github.com/Tritlo/PLFH/tree/main/reproducers) and is mirrored to `docs/dependent-haskell/plfh/reproducers/` in `Tritlo/ghc`:

| Reproducer | Serokell Card | Diagnostic (`db2586fdc2`) | Summary |
| --- | --- | --- | --- |
| `R13_WildcardBreaksOpenEq.hs` | R13 / R16 | `GHC-70565` | `timesWild Zero _ = Zero` fails open evaluation while `timesNamed Zero n = Zero` succeeds |
| `R13_MonusOpenEq.hs` | R13 / R16 | `GHC-70565` | `monus` fails open evaluation (even if first-arg-first) |
| `R13_PowOpenEq.hs` | R13 / R16 | `GHC-70565` | `pow` (recursion on 2nd arg) fails open evaluation |
| `R13_EqSizeOpenEq.hs` | R13 / R16 | `GHC-70565` | `eqSize` (unguarded tail recursion returning `Bool`) fails open evaluation |
| `R13_RevOpenEq.hs` | R13 / R16 | `GHC-70565` | Naive quadratic `rev (x:xs) = app (rev xs) [x]` fails open evaluation |
| `R13_SubstTermOpenEq.hs` | R13 / R16 | `GHC-70565` | `substTerm` (branching on `case eqSize x y of`) fails open evaluation — blocks Preservation |
| `R03_SecondColumnPattern.hs` | R03 | `GHC-83605` | Constructor equations cannot split a non-leading retained argument |
| `R03_FunctionColumnSplit.hs` | R03 | `GHC-83605` | Multi-equation constructor split after a retained function binder rejected |
| `R03_CongPartialApp.hs` | R03 / R17 / R23 | Untouchable meta | `cong @(plus m)` fails with untouchable meta-variable bound by retained application |
| `R03_WithEqualityUnderTrans.hs` | R03 | Untouchable meta | `withEquality (plusComm m n) Refl` inside `trans` fails with untouchable meta |
| `R03_FoldrRetainedIndex.hs` | R03 | `GHC-83605` | `foldrL plus Zero xs` rejected as a retained runtime argument |
| `R03_ForEachGadtEquations.hs` | R03 | `GHC-83605` | `foreach (m :: Term 'CEmpty a)` equations rejected on indexed GADT domain |
| `R03_ForEachGadtCase.hs` | R03 | `GHC-25897` / mismatch | `case m of` on `foreach (m :: Term 'CEmpty a)` does not refine `m` |
| `R03_TcInstFunPanic.hs` | R03 / Compiler bug | **GHC panic!** | `substP @Even (toEqP (plusComm m n)) ev` panics in `GHC.Tc.Gen.App.tcInstFun` (line 3947) |
| `R05_SubstTyEtaAliasPanic.hs` | R05 / Compiler bug | **GHC panic!** | Eta-reduced alias `lengthReverseLaw = lengthReverse` panics in `GHC.Core.TyCo.Subst.substTy` (line 900) |
| `R04_SigmaUnderForEach.hs` | R04 | Rejected sum position | Returning inline `some (k :: Size) \| k :~: plus m n` under `foreach` rejected |
| `R23_MatchabilityInLeibniz.hs` | R23 | `GHC-83865` | Matchable `EqP x :: a -> Type` cannot instantiate `a %U -> Type` directly |
