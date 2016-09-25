{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}
module DeBrujnify where

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
         | RPi String Raw Raw
         | REn RawEn
         deriving Show

data RawEn = RApp RawEn  Raw
           | RVar String Nat
           | RAnn Raw Raw
           deriving Show
type RawSplice = Raw

type SC = Maybe

deBruijnify :: Vec String n -> Raw -> SC (Tm (Syn n))
deBruijnify g (RLam x t) = Lam . SynBody <$> deBruijnify (VCons x g) t
deBruijnify g (RPi x _S _T)  = Pi <$> deBruijnify g _S <*> (SynBody <$> deBruijnify (VCons x g) _T)
deBruijnify g RN         = pure N
deBruijnify g RZ         = pure Z
deBruijnify g (REn e)    = En <$> deBruijnifyE g e

deBruijnifyE :: Vec String n -> RawEn -> SC (En (Syn n))
deBruijnifyE g (RApp t u)  = (:/) <$> deBruijnifyE g t <*> deBruijnify g u
deBruijnifyE g (RVar x n)  = V <$> velemIndex' x n g
deBruijnifyE g (RAnn t ty) = (:::) <$> deBruijnify g t <*> deBruijnify g ty

-- raw tests
rex1 = RLam "x" RZ `RAnn` RPi "x" RN RN

-- parsing
bigTm :: ParseTokens Raw
bigTm = zTm <|> nTm <|> lamTm <|> piTm <|> REn <$> bigEn <|>
        grp "(" (gap *> bigTm <* gap) ")"

bigEn :: ParseTokens RawEn
bigEn = smallEn <|> appTm

smallEn :: ParseTokens RawEn
smallEn = grp "(" (gap *> annTm <* gap) ")" <|>
          grp "(" (gap *> bigEn <* gap) ")" <|> varTm
       
lamTm :: ParseTokens Raw
lamTm = RLam <$ eat "\\" <* gap <*> var <* gap <* eat "." <* gap <*> bigTm

piTm :: ParseTokens Raw
piTm = RPi <$ eat "pi" <* gap <*> var <* gap <* eat ":" <* gap <*> bigTm <* gap <* eat "." <* gap <*> bigTm

annTm :: ParseTokens RawEn
annTm = RAnn <$ gap <*> bigTm <* gap <* eat ":" <* gap <*> bigTm <* gap

varTm :: ParseTokens RawEn
varTm = (\ x -> RVar x Zero) <$ gap <*> var

appTm :: ParseTokens RawEn
appTm = RApp <$ gap <*> smallEn <* gap <*> bigTm

zTm :: ParseTokens Raw
zTm = RZ <$ eat "Z"  

nTm :: ParseTokens Raw
nTm = RN <$ eat "N"  

var :: ParseTokens String
var = sym >>= \ x -> case x of
  c : s | elem c "'\\-" -> empty
  _     | elem ':' x -> empty
  "N" -> empty
  "Z" -> empty
  "pi" -> empty
  _ -> return x

-- tests
pex1 = map (\ (_,y,z) -> (y,z)) $ parseTokens bigTm (groupify $ tokens "(x y) z")
pex2 = map (\ (_,y,z) -> (y,z)) $ parseTokens bigTm (groupify $ tokens "x y z")
pex3 = map (\ (_,y,z) -> (y,z)) $ parseTokens bigTm (groupify $ tokens "(\\ x . x) z")
pex4 = map (\ (_,y,z) -> (y,z)) $ parseTokens bigTm (groupify $
  tokens "\\ x . x z")
pex5 = map (\ (_,y,z) -> (y,z)) $ parseTokens bigTm (groupify $
  tokens "\\ x . x")
pex6 = map (\ (_,y,z) -> (y,z)) $ parseTokens bigTm (groupify $ tokens "(Z : N)")

pex7 =  "((\\ x . x) : pi x : N . N) Z" -- use with below

-- these should move
{-
parseEval s = fmap val $ deBruijnify VNil $ head $ map (\ (_,y,_) -> y) $ filter (\ (_,_,z) -> null z)  $ parseTokens bigTm (groupify $ tokens s)

parseCheck s = runTC .infer =<< (deBruijnifyE VNil $ head $ map (\ (_,y,_) -> y) $ filter (\ (_,_,z) -> null z)  $ parseTokens bigEn (groupify $ tokens s))

parseQuote s = fmap (runFresh . quote) $  parseCheck s
-}
