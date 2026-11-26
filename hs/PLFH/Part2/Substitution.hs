-- Generated from content/part2/Substitution.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE AllowAmbiguousTypes, DependentTypes #-}
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
{-# LINE 43 "content/part2/Substitution.md" #-}
module PLFH.Part2.Substitution
  ( Rename
  , Subst
  , ids
  , shift
  , ren
  , consSubst
  , seqSubst
  , HasTerm (..)
  , HasFin (..)
  , finWToHas
  , termWToHas
  , hasToTermW
  , RenW
  , shiftW
  , extRenW
  , evalRename
  , SubW
  , idsW
  , singleW
  , singleHasW
  , consW
  , extsW
  , evalSubst
  , RenEq
  , SubEq
  , symSubEq
  , congExt
  , congRename
  , congExts
  , congSubst
  , subHead
  , subTail
  , subIdLVar
  , subApp
  , subLam
  , extsIds
  , subId
  , extsRen
  , renSubst
  , renameCompEq
  , substRename
  , renameSubst
  , extsSeq
  , subSub
  , zShiftAt
  , subEtaAt
  , subIdLAt
  , subIdRAt
  , subDistAt
  , subAssocAt
  , extsAsSigmaAt
  , substSingleAsCons
  , renCommute
  , extsSingleBeta
  , substCommute
  , substitution
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl), sym)
import Data.Nat.Dependent (Nat (..))
import PLFH.Part1.Induction (cong)
import PLFH.Part2.Untyped
  ( Fin (..)
  , FinW (..)
  , TermW (..)
  , UTerm (..)
  , extU
  , extsU
  , mkTermW
  , renameU
  , shiftFin
  , singleSubstU
  , substSingleU
  , substU
  )

{-# LINE 143 "content/part2/Substitution.md" #-}
-- | A simultaneous renaming from scope depth `m` to scope depth `n`.
type Rename (m :: Nat) (n :: Nat) = Fin m -> Fin n

-- | A simultaneous substitution mapping variables in depth `m` to terms in depth `n`.
type Subst (m :: Nat) (n :: Nat) = Fin m -> UTerm n

-- | Identity substitution: maps each variable to itself.
ids :: Fin m -> UTerm m
ids = UVar

-- | Shift renaming: increments every de Bruijn variable by one (`↑` / `S_`).
shift :: Fin m -> Fin (Succ m)
shift = FS

-- | Lift a renaming to a substitution.
ren :: (Fin m -> Fin n) -> Fin m -> UTerm n
ren rho x = UVar (rho x)

-- | Extend a substitution with a new term for variable 0 (`M • σ`).
consSubst :: UTerm n -> (Fin m -> UTerm n) -> Fin (Succ m) -> UTerm n
consSubst t _     FZ     = t
consSubst _ sigma (FS x) = sigma x

-- | Sequential composition of substitutions (`σ ⨟ τ`).
seqSubst :: (Fin m -> UTerm n) -> (Fin n -> UTerm p) -> Fin m -> UTerm p
seqSubst sigma tau x = substU tau (sigma x)

{-# LINE 183 "content/part2/Substitution.md" #-}
-- | Retained runtime witness for a term `t :: UTerm n`.
type HasTerm :: forall (n :: Nat). UTerm n -> Type
data HasTerm t where
  MkHasTerm :: foreach (t :: UTerm n) -> HasTerm t

-- | Runtime witness producing the retained term `s x` for each variable `x :: Fin m`.
type SubW :: forall (m :: Nat) (n :: Nat). Subst m n -> Type
type SubW @m @n s = foreach (x :: Fin m) -> HasTerm (s x)

-- | Runtime witness for the identity substitution `ids`.
idsW :: forall m. SubW @m @m (ids @m)
idsW x = MkHasTerm (UVar x)

-- | Runtime witness for single-variable substitution `singleSubstU w`.
singleW :: forall n. foreach (w :: UTerm n) -> SubW @(Succ n) @n (singleSubstU w)
singleW w FZ     = MkHasTerm w
singleW _ (FS x) = MkHasTerm (UVar x)

-- | Runtime witness for `consSubst t s`.
consW :: forall m n (s :: Subst m n).
         foreach (t :: UTerm n) -> SubW @m @n s -> SubW @(Succ m) @n (consSubst t s)
consW t _  FZ     = MkHasTerm t
consW _ sw (FS x) = sw x

-- | Retained runtime witness for a variable `x :: Fin n`.
type HasFin :: forall (n :: Nat). Fin n -> Type
data HasFin x where
  MkHasFin :: foreach (x :: Fin n) -> HasFin x

finWToHas :: forall (n :: Nat) (x :: Fin n). FinW x -> HasFin x
finWToHas (WFZ @m) = MkHasFin (FZ :: Fin (Succ m))
finWToHas (WFS fx) = case finWToHas fx of MkHasFin y -> MkHasFin (FS y)

termWToHas :: forall (n :: Nat) (t :: UTerm n). TermW t -> HasTerm t
termWToHas (WVar fx)    = case finWToHas fx of MkHasFin x -> MkHasTerm (UVar x)
termWToHas (WLam wb)    = case termWToHas wb of MkHasTerm b -> MkHasTerm (ULam b)
termWToHas (WApp wl wm) = case (termWToHas wl, termWToHas wm) of
  (MkHasTerm l, MkHasTerm m) -> MkHasTerm (UApp l m)

hasToTermW :: forall (n :: Nat) (t :: UTerm n). HasTerm t -> TermW t
hasToTermW (MkHasTerm u) = mkTermW u

-- | Runtime witness producing the retained index `r x` for each variable `x :: Fin m`.
type RenW :: forall (m :: Nat) (n :: Nat). Rename m n -> Type
type RenW @m @n r = foreach (x :: Fin m) -> HasFin (r x)

shiftW :: forall m. RenW @m @(Succ m) shiftFin
shiftW x = MkHasFin (FS x)

extRenW :: forall m n (r :: Rename m n).
           RenW @m @n r -> RenW @(Succ m) @(Succ n) (extU r)
extRenW _  FZ     = MkHasFin (FZ :: Fin (Succ n))
extRenW rw (FS x) = case rw x of
  MkHasFin y' -> MkHasFin (FS y')

evalRename :: forall m n (r :: Rename m n).
              RenW @m @n r -> foreach (t :: UTerm m) -> HasTerm (renameU r t)
evalRename rw (UVar x)    = case rw x of
  MkHasFin y -> MkHasTerm (UVar y)
evalRename rw (ULam b)    = case evalRename @(Succ m) @(Succ n) @(extU r) (extRenW @m @n @r rw) b of
  MkHasTerm b' -> MkHasTerm (ULam b')
evalRename rw (UApp l r') = case (evalRename @m @n @r rw l, evalRename @m @n @r rw r') of
  (MkHasTerm l', MkHasTerm r'') -> MkHasTerm (UApp l' r'')

shiftHasTerm :: forall n (t :: UTerm n). HasTerm t -> HasTerm (renameU shiftFin t)
shiftHasTerm (MkHasTerm u) = evalRename @n @(Succ n) @shiftFin (shiftW @n) u

singleHasW :: forall n (v :: UTerm n). HasTerm v -> SubW @(Succ n) @n (singleSubstU v)
singleHasW (MkHasTerm w') = singleW @n w'

-- | Lifting a runtime substitution witness under a binder (`extsU s`).
extsW :: forall m n (s :: Subst m n).
         SubW @m @n s -> SubW @(Succ m) @(Succ n) (extsU s)
extsW _  FZ     = MkHasTerm (UVar (FZ :: Fin (Succ n)))
extsW sw (FS x) = shiftHasTerm @n @(s x) (sw x)

-- | Evaluate a witnessed substitution on a retained term `t`, yielding `HasTerm (substU s t)`.
evalSubst :: forall m n (s :: Subst m n).
             SubW @m @n s -> foreach (t :: UTerm m) -> HasTerm (substU s t)
evalSubst sw (UVar x)   = sw x
evalSubst sw (ULam b)   = case evalSubst @(Succ m) @(Succ n) @(extsU s) (extsW @m @n @s sw) b of
  MkHasTerm b' -> MkHasTerm (ULam b')
evalSubst sw (UApp l r) = case (evalSubst @m @n @s sw l, evalSubst @m @n @s sw r) of
  (MkHasTerm l', MkHasTerm r') -> MkHasTerm (UApp l' r')

{-# LINE 282 "content/part2/Substitution.md" #-}
-- | Pointwise equality between two renamings.
type RenEq :: forall (m :: Nat) (n :: Nat). Rename m n -> Rename m n -> Type
type RenEq @m @n r1 r2 = foreach (x :: Fin m) -> r1 x :~: r2 x

-- | Pointwise equality between two substitutions.
type SubEq :: forall (m :: Nat) (n :: Nat). Subst m n -> Subst m n -> Type
type SubEq @m @n s1 s2 = foreach (x :: Fin m) -> s1 x :~: s2 x

-- | Symmetry of pointwise substitution equality.
symSubEq :: forall m n (s1 :: Subst m n) (s2 :: Subst m n).
            SubEq @m @n s1 s2 -> SubEq @m @n s2 s1
symSubEq eq x = sym (eq x)

-- | Pointwise-equal renamings lift to pointwise-equal extended renamings (`cong-ext`).
congExt :: forall m n (r1 :: Rename m n) (r2 :: Rename m n).
           RenEq @m @n r1 r2 -> RenEq @(Succ m) @(Succ n) (extU r1) (extU r2)
congExt _  FZ     = Refl
congExt eq (FS x) = case eq x of Refl -> Refl

-- | Pointwise-equal renamings produce equal renamed terms (`cong-rename`).
congRename :: forall m n (r1 :: Rename m n) (r2 :: Rename m n).
              RenEq @m @n r1 r2
           -> foreach (t :: UTerm m) -> renameU r1 t :~: renameU r2 t
congRename eq (UVar x)   = case eq x of Refl -> Refl
congRename eq (ULam b)   =
  case congRename @(Succ m) @(Succ n) @(extU r1) @(extU r2) (congExt @m @n @r1 @r2 eq) b of
    Refl -> Refl
congRename eq (UApp l r) = case (congRename @m @n @r1 @r2 eq l, congRename @m @n @r1 @r2 eq r) of
  (Refl, Refl) -> Refl

stepExtsFS :: forall m n (s1 :: Subst m n) (s2 :: Subst m n) (x :: Fin m).
              (s1 x :~: s2 x) -> extsU s1 (FS x) :~: extsU s2 (FS x)
stepExtsFS eq = cong (renameU shiftFin) eq

-- | Pointwise-equal substitutions lift to pointwise-equal extended substitutions (`cong-exts`).
congExts :: forall m n (s1 :: Subst m n) (s2 :: Subst m n).
            SubEq @m @n s1 s2 -> SubEq @(Succ m) @(Succ n) (extsU s1) (extsU s2)
congExts _  FZ     = Refl
congExts eq (FS x) = stepExtsFS @m @n @s1 @s2 @x (eq x)

-- | Pointwise-equal substitutions produce equal substituted terms (`cong-sub`).
congSubst :: forall m n (s1 :: Subst m n) (s2 :: Subst m n).
             SubEq @m @n s1 s2
          -> foreach (t :: UTerm m) -> substU s1 t :~: substU s2 t
congSubst eq (UVar x)   = eq x
congSubst eq (ULam b)   =
  case congSubst @(Succ m) @(Succ n) @(extsU s1) @(extsU s2) (congExts @m @n @s1 @s2 eq) b of
    Refl -> Refl
congSubst eq (UApp l r) = case (congSubst @m @n @s1 @s2 eq l, congSubst @m @n @s1 @s2 eq r) of
  (Refl, Refl) -> Refl

{-# LINE 341 "content/part2/Substitution.md" #-}
-- | Head lookup: `(t • σ) 0 ≡ t`.
subHead :: forall m n (t :: UTerm n) (s :: Subst m n).
           consSubst t s FZ :~: t
subHead = Refl

-- | Tail lookup: `(t • σ) (FS x) ≡ σ x`.
subTail :: forall m n (t :: UTerm n) (s :: Subst m n) (x :: Fin m).
           consSubst t s (FS x) :~: s x
subTail = Refl

-- | Variable evaluation: `substU σ (UVar x) ≡ σ x`.
subIdLVar :: forall m n (s :: Subst m n) (x :: Fin m).
             substU s (UVar x) :~: s x
subIdLVar = Refl

-- | Application distribution: `(L · R) [ σ ] ≡ (L [ σ ]) · (R [ σ ])`.
subApp :: forall m n (s :: Subst m n) (l :: UTerm m) (r :: UTerm m).
          substU s (UApp l r) :~: UApp (substU s l) (substU s r)
subApp = Refl

-- | Lambda distribution: `(λ B) [ σ ] ≡ λ (B [ exts σ ])`.
subLam :: forall m n (s :: Subst m n) (b :: UTerm (Succ m)).
          substU s (ULam b) :~: ULam (substU (extsU s) b)
subLam = Refl

{-# LINE 381 "content/part2/Substitution.md" #-}
-- | Lifting the identity substitution under a binder yields `ids` pointwise (`exts-ids`).
extsIds :: forall m. SubEq @(Succ m) @(Succ m) (extsU (ids @m)) (ids @(Succ m))
extsIds FZ     = Refl
extsIds (FS _) = Refl

-- | Identity substitution law (`sub-id`): `M [ ids ] ≡ M`!
subId :: forall m. foreach (t :: UTerm m) -> substU (ids @m) t :~: t
subId (UVar _)   = Refl
subId (ULam b)   =
  case congSubst @(Succ m) @(Succ m) @(extsU (ids @m)) @(ids @(Succ m)) (extsIds @m) b of
    Refl -> case subId @(Succ m) b of
      Refl -> Refl
subId (UApp l r) = case (subId @m l, subId @m r) of
  (Refl, Refl) -> Refl

-- | Lifting a promoted renaming commutes with `extU` pointwise (`exts-ren`).
extsRen :: forall m n (r :: Rename m n).
           SubEq @(Succ m) @(Succ n) (extsU (ren r)) (ren (extU r))
extsRen FZ     = Refl
extsRen (FS _) = Refl

-- | Renaming agrees with substituting the promoted renaming (`rename-sub`).
renSubst :: forall m n (r :: Rename m n).
            foreach (t :: UTerm m) -> renameU r t :~: substU (ren r) t
renSubst (UVar _)    = Refl
renSubst (ULam b)    =
  case renSubst @(Succ m) @(Succ n) @(extU r) b of
    Refl -> case congSubst @(Succ m) @(Succ n) @(ren (extU r)) @(extsU (ren r))
                   (symSubEq @(Succ m) @(Succ n) @(extsU (ren r)) @(ren (extU r)) (extsRen @m @n @r)) b of
      Refl -> Refl
renSubst (UApp l r') = case (renSubst @m @n @r l, renSubst @m @n @r r') of
  (Refl, Refl) -> Refl

extCompEq :: forall m n p q (r1 :: Rename m n) (r2 :: Rename n p)
                            (s1 :: Rename m q) (s2 :: Rename q p).
             (foreach (x :: Fin m) -> r2 (r1 x) :~: s2 (s1 x))
          -> foreach (y :: Fin (Succ m)) -> extU r2 (extU r1 y) :~: extU s2 (extU s1 y)
extCompEq _  FZ     = Refl
extCompEq eq (FS x) = case eq x of Refl -> Refl

-- | General commuting square for double renaming (`rename-rename`).
renameCompEq :: forall m n p q (r1 :: Rename m n) (r2 :: Rename n p)
                               (s1 :: Rename m q) (s2 :: Rename q p).
                (foreach (x :: Fin m) -> r2 (r1 x) :~: s2 (s1 x))
             -> foreach (t :: UTerm m)
             -> renameU r2 (renameU r1 t) :~: renameU s2 (renameU s1 t)
renameCompEq eq (UVar x)   = case eq x of Refl -> Refl
renameCompEq eq (ULam b)   =
  case renameCompEq @(Succ m) @(Succ n) @(Succ p) @(Succ q)
         @(extU r1) @(extU r2) @(extU s1) @(extU s2)
         (extCompEq @m @n @p @q @r1 @r2 @s1 @s2 eq) b of
    Refl -> Refl
renameCompEq eq (UApp l r) =
  case ( renameCompEq @m @n @p @q @r1 @r2 @s1 @s2 eq l
       , renameCompEq @m @n @p @q @r1 @r2 @s1 @s2 eq r ) of
    (Refl, Refl) -> Refl

extsSeqRen :: forall m n p (r :: Rename m n) (s :: Subst n p).
              SubEq @(Succ m) @(Succ p)
                    (seqSubst (ren (extU r)) (extsU s))
                    (extsU (seqSubst (ren r) s))
extsSeqRen FZ     = Refl
extsSeqRen (FS _) = Refl

-- | Substitution after renaming (`sub-rename`): `(M [ ren r ]) [ s ] ≡ M [ ren r ⨟ s ]`.
substRename :: forall m n p (r :: Rename m n) (s :: Subst n p).
               foreach (t :: UTerm m)
            -> substU s (renameU r t) :~: substU (seqSubst (ren r) s) t
substRename (UVar _)    = Refl
substRename (ULam b)    =
  case substRename @(Succ m) @(Succ n) @(Succ p) @(extU r) @(extsU s) b of
    Refl -> case congSubst @(Succ m) @(Succ p)
                   @(seqSubst (ren (extU r)) (extsU s)) @(extsU (seqSubst (ren r) s))
                   (extsSeqRen @m @n @p @r @s) b of
      Refl -> Refl
substRename (UApp l r') = case (substRename @m @n @p @r @s l, substRename @m @n @p @r @s r') of
  (Refl, Refl) -> Refl

subIdW :: forall n (t :: UTerm n). HasTerm t -> substU (ids @n) t :~: t
subIdW (MkHasTerm u) = subId @n u

renSubstW :: forall m n (r :: Rename m n) (t :: UTerm m).
             HasTerm t -> renameU r t :~: substU (ren r) t
renSubstW (MkHasTerm u) = renSubst @m @n @r u

shiftExtComm :: forall n p (r :: Rename n p).
                foreach (x :: Fin n) -> extU r (shiftFin x) :~: shiftFin (r x)
shiftExtComm _ = Refl

congShiftRename :: forall n p (t1 :: UTerm p) (t2 :: UTerm p).
                   t1 :~: t2 -> renameU shiftFin t1 :~: renameU shiftFin t2
congShiftRename eq = cong (renameU shiftFin) eq

extsRenSeqAt :: forall n p (r :: Rename n p) (t :: UTerm n).
                HasTerm t
             -> substU (ren (extU r)) (renameU shiftFin t) :~: renameU shiftFin (substU (ren r) t)
extsRenSeqAt (MkHasTerm u) =
  case sym (renSubstW @(Succ n) @(Succ p) @(extU r) @(renameU shiftFin u)
             (evalRename @n @(Succ n) @shiftFin (shiftW @n) u)) of
    Refl -> case renameCompEq @n @(Succ n) @(Succ p) @p @shiftFin @(extU r) @r @shiftFin
                   (shiftExtComm @n @p @r) u of
      Refl -> congShiftRename @n @p (renSubst @n @p @r u)

extsRenSeq :: forall m n p (s :: Subst m n) (r :: Rename n p).
              SubW @m @n s
           -> SubEq @(Succ m) @(Succ p)
                    (seqSubst (extsU s) (ren (extU r)))
                    (extsU (seqSubst s (ren r)))
extsRenSeq _  FZ     = Refl
extsRenSeq sw (FS x) = extsRenSeqAt @n @p @r @(s x) (sw x)

-- | Renaming after substitution (`rename-sub`): `rename r (M [ s ]) ≡ M [ s ⨟ ren r ]`.
renameSubst :: forall m n p (s :: Subst m n) (r :: Rename n p).
               SubW @m @n s
            -> foreach (t :: UTerm m)
            -> renameU r (substU s t) :~: substU (seqSubst s (ren r)) t
renameSubst sw (UVar x)    = renSubstW @n @p @r @(s x) (sw x)
renameSubst sw (ULam b)    =
  case renameSubst @(Succ m) @(Succ n) @(Succ p) @(extsU s) @(extU r) (extsW @m @n @s sw) b of
    Refl -> case congSubst @(Succ m) @(Succ p)
                   @(seqSubst (extsU s) (ren (extU r))) @(extsU (seqSubst s (ren r)))
                   (extsRenSeq @m @n @p @s @r sw) b of
      Refl -> Refl
renameSubst sw (UApp l r') = case (renameSubst @m @n @p @s @r sw l, renameSubst @m @n @p @s @r sw r') of
  (Refl, Refl) -> Refl

shiftExtsAgree :: forall n p (tau :: Subst n p).
                  SubW @n @p tau
               -> SubEq @n @(Succ p)
                        (seqSubst (ren shiftFin) (extsU tau))
                        (seqSubst tau (ren shiftFin))
shiftExtsAgree tw z = renSubstW @p @(Succ p) @shiftFin @(tau z) (tw z)

extsSeqAt :: forall n p (tau :: Subst n p) (t :: UTerm n).
             SubW @n @p tau -> HasTerm t
          -> substU (extsU tau) (renameU shiftFin t) :~: renameU shiftFin (substU tau t)
extsSeqAt tw (MkHasTerm u) =
  case substRename @n @(Succ n) @(Succ p) @shiftFin @(extsU tau) u of
    Refl -> case congSubst @n @(Succ p)
                   @(seqSubst (ren shiftFin) (extsU tau)) @(seqSubst tau (ren shiftFin))
                   (shiftExtsAgree @n @p @tau tw) u of
      Refl -> sym (renameSubst @n @p @(Succ p) @tau @shiftFin tw u)

-- | Lifting distributes over sequential composition pointwise (`exts-seq`).
extsSeq :: forall m n p (sigma :: Subst m n) (tau :: Subst n p).
           SubW @m @n sigma -> SubW @n @p tau
        -> SubEq @(Succ m) @(Succ p)
                 (seqSubst (extsU sigma) (extsU tau))
                 (extsU (seqSubst sigma tau))
extsSeq _  _  FZ     = Refl
extsSeq sw tw (FS x) = extsSeqAt @n @p @tau @(sigma x) tw (sw x)

-- | Substitution composition theorem (`sub-sub`): `(M [ σ ]) [ τ ] ≡ M [ σ ⨟ τ ]`!
subSub :: forall m n p (sigma :: Subst m n) (tau :: Subst n p).
          SubW @m @n sigma -> SubW @n @p tau
       -> foreach (t :: UTerm m)
       -> substU tau (substU sigma t) :~: substU (seqSubst sigma tau) t
subSub _  _  (UVar _)   = Refl
subSub sw tw (ULam b)   =
  case subSub @(Succ m) @(Succ n) @(Succ p) @(extsU sigma) @(extsU tau)
         (extsW @m @n @sigma sw) (extsW @n @p @tau tw) b of
    Refl -> case congSubst @(Succ m) @(Succ p)
                   @(seqSubst (extsU sigma) (extsU tau)) @(extsU (seqSubst sigma tau))
                   (extsSeq @m @n @p @sigma @tau sw tw) b of
      Refl -> Refl
subSub sw tw (UApp l r) = case (subSub @m @n @p @sigma @tau sw tw l, subSub @m @n @p @sigma @tau sw tw r) of
  (Refl, Refl) -> Refl

subSubW :: forall n p q (t :: Subst n p) (u :: Subst p q) (m :: UTerm n).
           SubW @n @p t -> SubW @p @q u -> HasTerm m
        -> substU u (substU t m) :~: substU (seqSubst t u) m
subSubW tw uw (MkHasTerm m) = subSub @n @p @q @t @u tw uw m

{-# LINE 563 "content/part2/Substitution.md" #-}
-- | Shift-cons cancellation (`Z-shift`, pointwise): `(ren ↑ ⨟ (t • σ)) x ≡ σ x`.
zShiftAt :: forall m n (t :: UTerm n) (s :: Subst m n).
            SubEq @m @n (seqSubst (ren (shift @m)) (consSubst t s)) s
zShiftAt _ = Refl

-- | Eta law (`sub-η`, pointwise): `(0 • ren ↑) y ≡ ids y`.
subEtaAt :: forall m.
            SubEq @(Succ m) @(Succ m) (consSubst (UVar FZ) (ren (shift @m))) (ids @(Succ m))
subEtaAt FZ     = Refl
subEtaAt (FS _) = Refl

-- | Left identity of `seqSubst` (`sub-idL`, pointwise): `(ids ⨟ σ) x ≡ σ x`.
subIdLAt :: forall m n (s :: Subst m n).
            SubEq @m @n (seqSubst (ids @m) s) s
subIdLAt _ = Refl

-- | Right identity of `seqSubst` (`sub-idR`, pointwise): `(σ ⨟ ids) x ≡ σ x`.
subIdRAt :: forall m n (s :: Subst m n).
            SubW @m @n s -> SubEq @m @n (seqSubst s (ids @n)) s
subIdRAt sw x = subIdW @n @(s x) (sw x)

-- | Distributivity (`sub-dist`, pointwise): `((t • σ) ⨟ τ) y ≡ (t [ τ ] • (σ ⨟ τ)) y`.
subDistAt :: forall m n p (t :: UTerm n) (s :: Subst m n) (tau :: Subst n p).
             SubEq @(Succ m) @p (seqSubst (consSubst t s) tau) (consSubst (substU tau t) (seqSubst s tau))
subDistAt FZ     = Refl
subDistAt (FS _) = Refl

-- | Associativity of `seqSubst` (`sub-assoc`, pointwise): `((σ ⨟ τ) ⨟ υ) x ≡ (σ ⨟ (τ ⨟ υ)) x`.
subAssocAt :: forall m n p q (s :: Subst m n) (t :: Subst n p) (u :: Subst p q).
              SubW @m @n s -> SubW @n @p t -> SubW @p @q u
           -> SubEq @m @q (seqSubst (seqSubst s t) u) (seqSubst s (seqSubst t u))
subAssocAt sw tw uw x = subSubW @n @p @q @t @u @(s x) tw uw (sw x)

-- | `extsU σ` equals `0 • (σ ⨟ ren ↑)` pointwise (`exts-as-sigma`)!
extsAsSigmaAt :: forall m n (s :: Subst m n).
                 SubW @m @n s
              -> SubEq @(Succ m) @(Succ n) (extsU s) (consSubst (UVar FZ) (seqSubst s (ren shiftFin)))
extsAsSigmaAt _  FZ     = Refl
extsAsSigmaAt sw (FS x) = renSubstW @n @(Succ n) @shiftFin @(s x) (sw x)

singleAsConsAt :: forall n (w :: UTerm n).
                  SubEq @(Succ n) @n (singleSubstU w) (consSubst w (ids @n))
singleAsConsAt FZ     = Refl
singleAsConsAt (FS _) = Refl

-- | Single-variable substitution `substSingleU b w` agrees with `substU (w • ids) b`!
substSingleAsCons :: forall n (w :: UTerm n).
                     foreach (b :: UTerm (Succ n))
                  -> substSingleU b w :~: substU (consSubst w (ids @n)) b
substSingleAsCons b =
  congSubst @(Succ n) @n @(singleSubstU w) @(consSubst w (ids @n)) (singleAsConsAt @n @w) b

{-# LINE 624 "content/part2/Substitution.md" #-}
shiftSingleCancel :: forall n (v :: UTerm n).
                     SubEq @n @n (seqSubst (ren shiftFin) (singleSubstU v)) (ids @n)
shiftSingleCancel _ = Refl

commuteAt :: forall n (v :: UTerm n) (t :: UTerm n).
             HasTerm t
          -> t :~: substU (singleSubstU v) (renameU shiftFin t)
commuteAt (MkHasTerm u) =
  case substRename @n @(Succ n) @n @shiftFin @(singleSubstU v) u of
    Refl -> case congSubst @n @n
                   @(seqSubst (ren shiftFin) (singleSubstU v)) @(ids @n)
                   (shiftSingleCancel @n @v) u of
      Refl -> sym (subId @n u)

commuteMap :: forall m n (s :: Subst m n) (w :: UTerm m).
              SubW @m @n s
           -> SubEq @(Succ m) @n
                    (seqSubst (singleSubstU w) s)
                    (seqSubst (extsU s) (singleSubstU (substU s w)))
commuteMap _  FZ     = Refl
commuteMap sw (FS x) = commuteAt @n @(substU s w) @(s x) (sw x)

-- | Substitution commutes with single-variable substitution (`subst-commute`):
-- `(M [ N ]) [ σ ] ≡ (M [ exts σ ]) [ N [ σ ] ]`!
substCommute :: forall m n (s :: Subst m n).
                SubW @m @n s
             -> foreach (w :: UTerm m)
             -> foreach (t :: UTerm (Succ m))
             -> substU s (substSingleU t w)
            :~: substSingleU (substU (extsU s) t) (substU s w)
substCommute sw w t =
  case subSub @(Succ m) @m @n @(singleSubstU w) @s (singleW @m w) sw t of
    Refl -> case congSubst @(Succ m) @n
                   @(seqSubst (singleSubstU w) s) @(seqSubst (extsU s) (singleSubstU (substU s w)))
                   (commuteMap @m @n @s @w sw) t of
      Refl -> sym (subSub @(Succ m) @(Succ n) @n @(extsU s) @(singleSubstU (substU s w))
                     (extsW @m @n @s sw) (singleHasW @n @(substU s w) (evalSubst @m @n @s sw w)) t)

-- | Renaming commutes with single-variable substitution (`rename-subst-single`):
-- `renameU r (substSingleU t w) ≡ substSingleU (renameU (extU r) t) (renameU r w)`.
renCommute :: forall m n (r :: Rename m n).
              RenW @m @n r
           -> foreach (w :: UTerm m)
           -> foreach (t :: UTerm (Succ m))
           -> renameU r (substSingleU t w)
          :~: substSingleU (renameU (extU r) t) (renameU r w)
renCommute rw w t =
  let sw :: SubW @m @n (ren r)
      sw x = case rw x of MkHasFin y -> MkHasTerm (UVar y)
  in case evalSubst @(Succ m) @m @(singleSubstU w) (singleW @m w) t of
    MkHasTerm tw ->
      case renSubst @m @n @r tw of
        Refl -> case substCommute @m @n @(ren r) sw w t of
          Refl -> case renSubst @m @n @r w of
            Refl -> case congSubst @(Succ m) @(Succ n) @(extsU (ren r)) @(ren (extU r))
                           (extsRen @m @n @r) t of
              Refl -> case renSubst @(Succ m) @(Succ n) @(extU r) t of
                Refl -> Refl

-- | Beta-commutation for extended substitutions:
-- `substSingleU (substU (extsU s) b) w ≡ substU (consSubst w s) b`.
extsSingleBeta :: forall m n (s :: Subst m n).
                  SubW @m @n s
               -> foreach (w :: UTerm n)
               -> foreach (b :: UTerm (Succ m))
               -> substSingleU (substU (extsU s) b) w :~: substU (consSubst w s) b
extsSingleBeta sw w b =
  case subSub @(Succ m) @(Succ n) @n @(extsU s) @(singleSubstU w)
         (extsW @m @n @s sw) (singleW @n w) b of
    Refl -> congSubst @(Succ m) @n
              @(seqSubst (extsU s) (singleSubstU w)) @(consSubst w s)
              go b
  where
    go :: SubEq @(Succ m) @n (seqSubst (extsU s) (singleSubstU w)) (consSubst w s)
    go FZ     = Refl
    go (FS x) = sym (commuteAt @n @w @(s x) (sw x))

-- | Barendregt's Substitution Lemma (`substitution`):
-- `M [ N ] [ L ] ≡ M [ exts (L • ids) ] [ N [ L ] ]`!
substitution :: forall m.
                foreach (n :: UTerm (Succ m))
             -> foreach (l :: UTerm m)
             -> foreach (t :: UTerm (Succ (Succ m)))
             -> substSingleU (substSingleU t n) l
            :~: substSingleU (substU (extsU (singleSubstU l)) t) (substSingleU n l)
substitution n l t = substCommute @(Succ m) @m @(singleSubstU l) (singleW @m l) n t
