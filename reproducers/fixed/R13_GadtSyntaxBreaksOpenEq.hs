{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
-- | Minimal reproducer (R13/R16): declaring a plain non-indexed ADT with GADT
-- syntax (`data ValG where`) disables checked open source equations with
-- `GHC-68947`, while the identical ADT declared with H98 syntax (`data ValH =`)
-- compiles and computes cleanly in types!
--
-- Triggered by `dom` and `cod` on `Value` in PLFH.Part3.Denotational.
module R13_GadtSyntaxBreaksOpenEq (ValH (..), domH, okH, ValG (..), domG, badG) where

import Data.Type.Equality ((:~:) (Refl))

-- Control: H98 syntax succeeds!
data ValH = BotH | ArrH ValH ValH | JoinH ValH ValH

domH :: ValH -> ValH
domH BotH        = BotH
domH (ArrH v w)  = v
domH (JoinH a b) = JoinH (domH a) (domH b)

okH :: domH ('JoinH ('ArrH 'BotH 'BotH) 'BotH) :~: 'JoinH 'BotH 'BotH
okH = Refl

-- Trigger: identical non-indexed ADT using GADT syntax fails GHC-68947!
data ValG where
  BotG  :: ValG
  ArrG  :: ValG -> ValG -> ValG
  JoinG :: ValG -> ValG -> ValG

domG :: ValG -> ValG
domG BotG        = BotG
domG (ArrG v w)  = v
domG (JoinG a b) = JoinG (domG a) (domG b)

badG :: domG ('JoinG ('ArrG 'BotG 'BotG) 'BotG) :~: 'JoinG 'BotG 'BotG
badG = Refl
