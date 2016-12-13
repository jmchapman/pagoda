{-# LANGUAGE GADTs,
             DataKinds,
             KindSignatures,
             StandaloneDeriving #-}
--------------------------------------------------------------------------------
module DeBruijnify where

import Utils
import Syntax

-- Raw terms

data Raw = RLam String Raw
         | RN
         | RZ
         | RB Bit
         | RPi String Raw Raw
         | RType
         | RPt
         | RPath Raw Raw
         | REn RawEn
         deriving Show

data RawEn = RApp RawEn  Raw
           | RVar String Nat
           | RAnn Raw Raw
           deriving Show

type RawSplice = Raw

type SC = Maybe

deBruijnify :: Vec String n -> Raw -> SC (Tm (Syn n))
deBruijnify g RType          = pure Type
deBruijnify g (RPi x _S _T)  =
  Pi <$> deBruijnify g _S <*> (SynBody <$> deBruijnify (VCons x g) _T)
deBruijnify g (RLam x t)     = Lam . SynBody <$> deBruijnify (VCons x g) t
deBruijnify g RN             = pure N
deBruijnify g RZ             = pure Z
deBruijnify g RPt            = pure Pt
deBruijnify g (RPath _S _T)  =
  Path <$> deBruijnify g _S <*> deBruijnify g _T 
deBruijnify g (REn e)    = En <$> deBruijnifyE g e

deBruijnifyE :: Vec String n -> RawEn -> SC (En (Syn n))
deBruijnifyE g (RApp t u)  = (:/) <$> deBruijnifyE g t <*> deBruijnify g u
deBruijnifyE g (RVar x n)  = V <$> velemIndex' x n g
deBruijnifyE g (RAnn t ty) = (:::) <$> deBruijnify g t <*> deBruijnify g ty



