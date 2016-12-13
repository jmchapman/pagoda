{-# LANGUAGE DeriveFunctor, GADTs #-}

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
    (f , newname) <- f name
    (x , newestname) <- x newname
    return (f x , newestname)

instance Monad TC where
  TC x >>= f = TC $ \ name -> do
    (x , newname) <- x name
    let TC fx = f x
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
Type                 >:> Path _S _T         = do
  Path <$> (Type >:> _S) <*> (Type >:> _T)
Type                 >:> N                  = return N
Type                 >:> Pi _S (SynBody _T) = do
  _S <- Type >:> _S
  x <- tcfresh _S
  Type >:> instantiate _T x
  return $ Pi _S (SemBody E0 _T)
N                    >:> Z                  = return Z
Pi _S (SemBody g _T) >:> Lam (SynBody t)    = do
  x <- tcfresh _S
  tval (ES g (En (P x) :::: _S)) _T >:> instantiate t x
  return $ Lam (SemBody E0 t)
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
  e <- infer e
  typeOf e /:> t
  return (e / val t)
infer (t ::: ty) = do
  ty <- Type >:> ty
  t  <- ty >:> t
  return (t :::: ty)

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
  subType (tval (ES g (En (P x) :::: _S)) _T)
          (tval (ES g' (En (P x) :::: _S')) _T')
subType x y = fail $ show x ++ " ain't the same as " ++ show y

-- -}

