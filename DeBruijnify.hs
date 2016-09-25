{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}
module DeBrujnify where

import Utils
import Data.List
import Data.Maybe
import Syntax
import Layout
import Control.Applicative

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

data Vec x (n :: Nat) where
  VNil  :: Vec x Zero
  VCons :: x -> Vec x n -> Vec x (Suc n)

vlookup :: Fin n -> Vec x n -> x
vlookup FZero    (VCons x _ ) = x
vlookup (FSuc i) (VCons _ xs) = vlookup i xs

-- find the first x in the vector and return its index
velemIndex :: Eq x => x -> Vec x n -> Maybe (Fin n)
velemIndex x VNil          = Nothing
velemIndex x (VCons x' xs) =
  if x == x' then
    Just FZero              
  else
    fmap FSuc (velemIndex x xs)

-- find the nth x in the vector and return its index
velemIndex' :: Eq x => x -> Nat ->  Vec x n -> Maybe (Fin n)
velemIndex' x n VNil          = Nothing
velemIndex' x n (VCons x' xs) =
  if x == x' then
    case n of
      Zero  -> Just FZero
      Suc n -> fmap FSuc (velemIndex' x n xs)
  else
    fmap FSuc (velemIndex' x n xs)


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

parseEval s = fmap val $ deBruijnify VNil $ head $ map (\ (_,y,_) -> y) $ filter (\ (_,_,z) -> null z)  $ parseTokens bigTm (groupify $ tokens s)

parseCheck s = runTC .infer =<< (deBruijnifyE VNil $ head $ map (\ (_,y,_) -> y) $ filter (\ (_,_,z) -> null z)  $ parseTokens bigEn (groupify $ tokens s))

