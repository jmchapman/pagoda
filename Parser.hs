module Parser where

import Control.Applicative

import Utils
import Layout
import DeBruijnify
import Syntax

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
bigEn = smallEn <|> appTm <|> annTm

smallEn :: ParseTokens RawEn
smallEn = varTm <|>
  grp "(" (gap *> bigEn <* gap) ")" -- <|>
--  grp "(" (gap *> annTm <* gap) ")" -- are the brackets really needed?

piTm :: ParseTokens Raw
piTm = RPi <$ eat "pi" <* gap <*> var <* gap <* eat ":"
  <* gap <*> bigTm <* gap <* eat "."
  <* gap <*> bigTm

lamTm :: ParseTokens Raw
lamTm = RLam <$ eat "\\" <* gap <*> var <* gap <* eat "."
  <* gap <*> bigTm

annTm :: ParseTokens RawEn
annTm = RAnn <$> smallTm <* gap <* eat ":" <* gap <*> bigTm

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
