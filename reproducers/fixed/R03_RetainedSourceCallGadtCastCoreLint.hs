{-# LANGUAGE DependentTypes #-}
-- | Minimal reproducer (Serokell R03 / R13; GHC Proposal #378):
-- Passing a GADT-refined argument (`m` cast by `SelCo` from matching
-- `Lam body :: Term CEmpty (TArr a b)`) into a certified source call
-- (`substSingle body m`) inside a retained `foreach` constructor field
-- (`PStep`) triggers two linked compiler failures:
--   1. Directly in `appBeta`: rejected at typecheck time with `GHC-83605`,
--      because `GHC.Core.exprToNativeIndex` rejects `Cast` inside certified
--      source-call operands.
--   2. Factored through a helper (`betaStep body m w = PStep (substSingle body m) ...`):
--      accepted by the typechecker, then inlined by `Desugar (after optimization)`
--      (`simpleOptPgm`), crashing Core Lint with:
--      `Unsupported retained runtime argument: substSingle ... (m \`cast\` ...)`.
--
-- Hit when writing PLFA's 6-line intrinsically-typed evaluator `eval` over
-- `Progress` with retained `PStep :: foreach n -> Step m n -> Progress m` in
-- `PLFH.Part2.DeBruijn`.
-- Note: `betaStep` and `appBeta` are intentionally unexported (matching
-- `PLFH.Part2.DeBruijn`'s explicit export list), which allows `simpleOptPgm`
-- to inline them into `progress` and trigger the Core Lint failure.
module R03_RetainedSourceCallGadtCastCoreLint
  ( Ty (..)
  , Ctx (..)
  , Lookup (..)
  , Term (..)
  , ext
  , rename
  , exts
  , subst
  , substSingle
  , Value (..)
  , Step (..)
  , Progress (..)
  , progress
  ) where

import Data.Kind (Type)

data Ty = TNat | TArr Ty Ty
data Ctx = CEmpty | CExt Ctx Ty

data Lookup (g :: Ctx) (a :: Ty) where
  Z :: Lookup (CExt g a) a
  S :: Lookup g a -> Lookup (CExt g b) a

data Term (g :: Ctx) (a :: Ty) where
  Var :: Lookup g a -> Term g a
  Lam :: Term (CExt g a) b -> Term g (TArr a b)
  App :: Term g (TArr a b) -> Term g a -> Term g b

ext :: (forall a. Lookup g a -> Lookup d a) -> Lookup (CExt g b) a -> Lookup (CExt d b) a
ext _ Z     = Z
ext r (S x) = S (r x)

rename :: (forall a. Lookup g a -> Lookup d a) -> Term g a -> Term d a
rename r (Var x)   = Var (r x)
rename r (Lam n)   = Lam (rename (ext r) n)
rename r (App l m) = App (rename r l) (rename r m)

exts :: (forall a. Lookup g a -> Term d a) -> Lookup (CExt g b) a -> Term (CExt d b) a
exts _ Z     = Var Z
exts s (S x) = rename S (s x)

subst :: (forall a. Lookup g a -> Term d a) -> Term g a -> Term d a
subst s (Var x)   = s x
subst s (Lam n)   = Lam (subst (exts s) n)
subst s (App l m) = App (subst s l) (subst s m)

substSingle :: forall g b a. Term (CExt g b) a -> Term g b -> Term g a
substSingle m v = subst go m
  where
    go :: Lookup (CExt g b) x -> Term g x
    go Z     = v
    go (S x) = Var x

type Value :: forall (g :: Ctx) (a :: Ty). Term g a -> Type
data Value m where
  VLam :: Value (Lam n)

type Step :: forall (g :: Ctx) (a :: Ty). Term g a -> Term g a -> Type
data Step m n where
  XiApp1  :: Step l l' -> Step (App l m) (App l' m)
  XiApp2  :: Value l -> Step m m' -> Step (App l m) (App l m')
  BetaLam :: forall g a b (n :: Term (CExt g a) b) (w :: Term g a).
             Value w -> Step (App (Lam n) w) (substSingle n w)

type Progress :: forall (a :: Ty). Term CEmpty a -> Type
data Progress m where
  PStep :: foreach (n :: Term CEmpty a) -> Step m n -> Progress m
  PDone :: Value m -> Progress m

betaStep :: forall a b.
            foreach (body :: Term (CExt CEmpty a) b) -> foreach (m :: Term CEmpty a)
         -> Value m -> Progress (App (Lam body) m)
betaStep body m w = PStep (substSingle body m) (BetaLam w)

appBeta :: forall a b.
           foreach (l :: Term CEmpty (TArr a b)) -> foreach (m :: Term CEmpty a)
        -> Value l -> Value m -> Progress (App l m)
appBeta l = case l of
  Lam body -> \m _ w -> betaStep body m w
  Var x    -> \_ _ _ -> case x of {}
  App _ _  -> \_ v _ -> case v of {}

progress :: forall (a :: Ty). foreach (m :: Term CEmpty a) -> Progress m
progress t = case t of
  Var x   -> case x of {}
  Lam _   -> PDone VLam
  App l m -> case progress l of
    PStep l' s -> PStep (App l' m) (XiApp1 s)
    PDone v    -> case progress m of
      PStep m' s -> PStep (App l m') (XiApp2 v s)
      PDone w    -> appBeta l m v w
