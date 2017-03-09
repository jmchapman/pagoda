{-# LANGUAGE DataKinds,
             TypeSynonymInstances,
             FlexibleInstances,
             DeriveFunctor,
             GADTs #-}
{-# OPTIONS_GHC -Wall -fno-warn-orphans #-} -- we define Eq for values here


module Semantics where

import Prelude hiding ((/))

import Utils
import Syntax

-- semantics
tval :: Env n -> Tm ('Syn n) -> Val
tval g (En e)              = valOf (eval g e)
tval _ (I b)               = I b
tval g (Lam (SynBody t))   = Lam (SemBody g t)
tval _ Z                   = Z
tval _ N                   = N
tval g (Pi s (SynBody t))  = Pi (tval g s) (SemBody g t)
tval g (Path _S _T)        = Path (tval g _S) (tval g _T)
tval _ Type                = Type
tval _ Pt                  = Pt

eval :: Env n -> En ('Syn n) -> Thing
eval g (V i     ) = blookup i g
eval _ (P r     ) = En (P r) :::: refType r
eval g (e :/ t  ) = eval g e / tval g t
eval g (t ::: ty) = tval g t :::: tval g ty

(/) :: Thing -> Val -> Thing
(_Q                :::: Path _S _T) / I B0 = _S :::: Type
(_Q                :::: Path _S _T) / I B1 = _T :::: Type
(Lam (SemBody g t) :::: Path _S _T) / p =
  tval (BCons g (p :::: Pt)) t :::: Type
(En _Q             :::: Path _S _T) / p =
  En (_Q :/ p) :::: Type
(Lam (SemBody g t) :::: Pi _S (SemBody g' _T)) / s =
  tval (BCons g (s :::: _S)) t :::: tval (BCons g' (s :::: _S)) _T
(En e              :::: Pi _S (SemBody g _T)) / s =
  En (e :/ s) :::: tval (BCons g (s :::: _S)) _T
_ / _ = error "unexpected application"

val :: Tm ('Syn 'Zero) -> Val
val t = tval BNil t

newtype Fresh x = Fresh (Name -> (x,Name)) deriving Functor

runFresh :: Fresh a -> a
runFresh (Fresh f) = fst (f 0)

-- this thing is highly suspicious
instance Applicative Fresh where
  pure x = Fresh (\ name -> (x, name))
  Fresh f <*> Fresh a = Fresh $ \name ->
    let (f',_)          = f name
        (a',newestname) = a name
    in
        (f' a', newestname)

instance Monad Fresh where
  Fresh x >>= f = Fresh $ \ name ->
    let (x' , newname) = x name
        Fresh fx = f x'
    in
        fx newname

fresh :: Val -> Fresh Ref
fresh ty = Fresh $ \ i -> (Ref (next i) ty, next i)

quote :: Thing -> Fresh TERM
quote (I b :::: Pt) = return $ I b
quote (N :::: Type) = return N
quote (Z :::: N)    = return Z
quote (Path _S _T           :::: Type) = do
  Path <$> quote (_S :::: Type) <*> quote (_T :::: Type)
quote (Pi _S (SemBody g _T) :::: Type) = do
  x <- fresh _S
  dom <- quote (_S :::: Type)
  cod <- quote (tval (BCons g (En (P x) :::: _S)) _T :::: Type)
  return $ Pi dom (SynBody (abstract x SZero cod))
quote f@(_    :::: Pi _S _) = do
  x <- fresh _S
  body <- quote (f  / En (P x))
  return $ Lam (SynBody (abstract x SZero body))
quote (En e :::: _) = fmap (En . fst) $ nquote e
quote (_    :::: _) = error "tried to quote a canonical thing with a wrong type"

nquote :: Ne -> Fresh (ELIM,Val)
nquote (P x) = pure (P x , refType x) 
nquote (e :/ s) = do
  (e',Pi _S (SemBody g _T)) <- nquote e
  s' <- quote (s :::: _S)
  return (e' :/ s', tval (BCons g (s :::: _S)) _T)
  
instance Eq Thing where
  thing1 == thing2 = runFresh (quote thing1) == runFresh (quote thing2)

instance Eq Ne where
  ne1 == ne2 = fst (runFresh (nquote ne1)) == fst (runFresh (nquote ne2))

