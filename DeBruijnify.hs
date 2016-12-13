{-# LANGUAGE GADTs,
             DataKinds,
             KindSignatures,
             StandaloneDeriving #-}
--------------------------------------------------------------------------------
module DeBruijnify where

import Data.List
import Data.Maybe
import Control.Applicative

import Utils
import Syntax
import Layout

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

-- parsing
bigTm :: ParseTokens Raw
bigTm = smallTm <|> pathTm <|> lamTm <|> piTm <|> REn <$> bigEn

smallTm :: ParseTokens Raw
smallTm = typeTm
    <|> pointTm
    <|> nTm
    <|> zTm
    <|> grp "(" (gap *> bigTm <* gap) ")"



bigEn :: ParseTokens RawEn
bigEn = smallEn <|> appTm

smallEn :: ParseTokens RawEn
smallEn = varTm <|>
  grp "(" (gap *> bigEn <* gap) ")" <|>
  grp "(" (gap *> annTm <* gap) ")" -- are the brackets really needed?

piTm :: ParseTokens Raw
piTm = RPi <$ eat "pi" <* gap <*> var <* gap <* eat ":"
  <* gap <*> bigTm <* gap <* eat "."
  <* gap <*> bigTm

lamTm :: ParseTokens Raw
lamTm = RLam <$ eat "\\" <* gap <*> var <* gap <* eat "."
  <* gap <*> bigTm

annTm :: ParseTokens RawEn
annTm = RAnn <$> bigTm <* gap <* eat ":" <* gap <*> bigTm

varTm :: ParseTokens RawEn
varTm = (\ x -> RVar x Zero) <$ gap <*> var

appTm :: ParseTokens RawEn
appTm = RApp <$> smallEn <* gap <*> bigTm

-- type
typeTm :: ParseTokens Raw
typeTm = RType <$ eat "*"

-- natural numbers
nTm :: ParseTokens Raw
nTm = RN <$ eat "N"  

zTm :: ParseTokens Raw
zTm = RZ <$ eat "Z"  

-- points and paths

pointTm :: ParseTokens Raw
pointTm = RB <$> (B0 <$ eat "0" <|> B1 <$ eat "1")

pathTm :: ParseTokens Raw
pathTm = RPath <$> smallTm <* gap <* eat "-" <* gap <*> bigTm

-- variables are anything that isn't something else

var :: ParseTokens String
var = sym >>= \ x -> case x of
  c : s | elem c "'\\-" -> empty
  _     | elem ':' x -> empty
  "*" -> empty
  "N" -> empty
  "Z" -> empty
  "pi" -> empty
  "0" -> empty
  "1" -> empty
  _ -> return x


