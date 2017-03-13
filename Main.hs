--------------------------------------------------------------------------------
{-# OPTIONS_GHC -Wall #-}
module Main where

import Utils
import Layout
import Parser
import Raw
import Syntax
import Semantics
import TypeChecker

-- parsing tests
pex1, pex2 , pex3, pex4, pex5, pex6, pex7, pex8, pex9, pex10 :: String
pex11, pex12, pex13, pex14, pex15, pex16, pex17 :: String
pex1 = "(x y) z"
pex2 = "x y z"
pex3 = "(\\ x . x) z"
pex4 = "\\ x . x z"
pex5 = "\\ x . x"
pex6 =  "(Z : N)"
pex7 =  "((\\ x . x) : pi x : N . N) Z"
pex8 = "*"
pex9 = "1"
pex10 = "0"
pex11 = "* - *"
pex12 = "(* - *)"
pex13 = "(* : *) - *"
pex14 = "* : * - *"
pex15 =  "((\\ x . x) : pi x : * . *) * - *"
pex16 = "N : *"
pex17 = "(\\ i . N) : N - N" 

parse :: String -> Raw
parse s = fst $ head $ filter (\ (_,z) -> z == []) $
  map (\ (_,y,z) -> (y,z)) $ parseTokens bigTm (groupify $ tokens s)

parseEval :: String -> Maybe Val
parseEval s = fmap val $ deBruijnify VNil $ head $ map (\ (_,y,_) -> y) $ filter (\ (_,_,z) -> null z)  $ parseTokens bigTm (groupify $ tokens s)

parseCheck :: String -> Maybe Thing
parseCheck s = runTC .infer =<< (deBruijnifyE VNil $ head $ map (\ (_,y,_) -> y) $ filter (\ (_,_,z) -> null z)  $ parseTokens bigEn (groupify $ tokens s))

parseQuote :: String -> Maybe TERM
parseQuote s = fmap (runFresh . quote) $  parseCheck s

-- raw tests
rex1 :: RawEn
rex1 = RLam "x" RZ `RAnn` RPi "x" RN RN

-- typechecking tests

-- successful tests
ex1 , ex2 , ex3 , ex4 :: TC Val
ex1 = N >:> Z
ex2 = Pi N (SemBody BNil N) >:> Lam (SynBody Z)
ex3 = N >:> En ((Lam (SynBody Z) ::: Pi N (SynBody N)) :/ Z)
ex4 = (val $ Pi Type (SynBody (Pi (En (V FZero)) (SynBody (En (V (FSuc FZero))))))) >:> Lam (SynBody (Lam (SynBody (En (V FZero)))))

ex5' , ex5'' :: Thing
ex5' = eval BNil (P (Ref (-1) (Pi N (SemBody BNil N))))
ex5'' = eval BNil (Lam (SynBody (En (P (Ref (-1) (Pi N (SemBody BNil N))) :/ En (V FZero)))) ::: Pi N (SynBody N))
ex5 :: Bool
ex5 = ex5' == ex5'' -- calls quote

-- Failing tests
fex1 , fex2, fex3 :: TC Val
fex1 = Pi N (SemBody BNil N) >:> Z
fex2 = N >:> En ((Lam (SynBody Z) ::: Pi N (SynBody N)) :/ N)
fex3 = N >:> En ((Z ::: N) :/ Z)

main :: IO a
main = loop where
  loop = do
    str <- getLine
    print $ parse str
    loop
