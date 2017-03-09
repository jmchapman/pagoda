{-# LANGUAGE DeriveFunctor, GADTs #-}
{-# OPTIONS_GHC -Wall #-}

module TypeChecker where

import Prelude hiding ((/))

import Utils
import Syntax
import Semantics

-- typechecker

newtype TC x = TC (Name -> Maybe (x,Name)) deriving Functor

runTC :: TC x -> Maybe x
runTC (TC f) = fmap fst (f 0)

instance Applicative TC where
  pure x = TC $ \ n -> Just (x, n)
  TC f <*> TC x = TC $ \ name -> do
    (f' , newname) <- f name
    (x' , newestname) <- x newname
    return (f' x' , newestname)

instance Monad TC where
  TC x >>= f = TC $ \ name -> do
    (x' , newname) <- x name
    let TC fx = f x'
    fx newname

-- is the action ok?
(/:>) :: Val -> TERM -> TC ()
Pi _S _T /:> s = _S >:> s >> return ()
ty       /:> s =
  fail $ show s ++ " can't act on something of type " ++ show ty

tcfresh :: Val -> TC Ref
tcfresh ty = TC $ \ i -> Just (Ref (next i) ty, next i)

-- check a term in a trusted type
(>:>) :: Val -> TERM -> TC Val
Type                 >:> Type               = return Type

Type                 >:> N                  = return N
N                    >:> Z                  = return Z

Type                 >:> Path _S _T         = do
  Path <$> (Type >:> _S) <*> (Type >:> _T)
Path _S _T           >:> Lam (SynBody t)    = do
  x <- tcfresh Pt
  _ <- Type >:> instantiate t x
  subType _S (tval (BCons BNil (I B0 :::: Pt)) t)
  subType _T (tval (BCons BNil (I B1 :::: Pt)) t)
  return $ Lam (SemBody BNil t)
  
Type                 >:> Pi _S (SynBody _T) = do
  _S <- Type >:> _S
  x <- tcfresh _S
  _ <- Type >:> instantiate _T x
  return $ Pi _S (SemBody BNil _T)
Pi _S (SemBody g _T) >:> Lam (SynBody t)    = do
  x <- tcfresh _S
  _ <- tval (BCons g (En (P x) :::: _S)) _T >:> instantiate t x
  return $ Lam (SemBody BNil t)
want                 >:> En e               = do
  th <- infer e
  typeOf th `subType` want
  return (valOf th)
-- failure cases
Type                 >:> v                  =
  fail $ show v ++ " ain't no type"
N                    >:> v                  =
  fail $ show v ++ " ain't no number"
Pi _ _               >:> v                  =
  fail $ show v ++ " ain't no function"
_                    >:> _                  =
  fail "it don't type check"
  
infer :: ELIM -> TC Thing
infer (P x)       = return (En (P x) :::: refType x)
infer (e :/ t)    = do
  e' <- infer e
  typeOf e' /:> t
  return (e' / val t)
infer (t ::: ty) = do
  ty' <- Type >:> ty
  t'  <- ty' >:> t
  return (t' :::: ty')
infer (V _)       = error "inferred a V which shouldn't be in an elim"

subType :: Val -> Val -> TC ()
subType Type   Type    = return ()
subType N      N       = return ()
subType (En e) (En e') =
  if e == e' then return () else
    fail $ show e ++ " ain't the same neutral type as " ++ show e'
subType (Pi _S (SemBody g _T)) (Pi _S' (SemBody g' _T')) = do
  subType _S' _S 
  x <- tcfresh _S
  -- might need to pay attention to which domain type is used later
  subType (tval (BCons g (En (P x) :::: _S)) _T)
          (tval (BCons g' (En (P x) :::: _S')) _T')
subType x y = fail $ show x ++ " ain't the same as " ++ show y

-- -}

