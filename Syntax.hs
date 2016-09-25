{-# LANGUAGE KindSignatures, DataKinds, GADTs,
             StandaloneDeriving,
             TypeSynonymInstances,
             FlexibleInstances,
             DeriveFunctor #-}
module Syntax where

import Prelude hiding ((/))
import Utils
import Control.Monad

type Name = Int
data Phase = Syn Nat | Sem

data Env (n :: Nat) where
  E0 :: Env Zero
  ES :: Env n -> Thing -> Env (Suc n)

deriving instance Show (Env n)

elookup :: Env n -> Fin n -> Thing
elookup (ES _ th) FZero    = th
elookup (ES g _ ) (FSuc i) = elookup g i

type Val = Tm Sem
type Ne  = En Sem
data Thing = (::::) {valOf :: Val, typeOf :: Val} deriving Show

data Body p where
  SynBody :: Tm (Syn (Suc n)) -> Body (Syn n)
  SemBody :: Env n -> Tm (Syn (Suc n)) -> Body Sem

deriving instance Show (Body p)
instance Eq   (Body (Syn p)) where
  SynBody t == SynBody t' = t == t'

data Ref = Ref {refName :: Name, refType :: Val} deriving Show

data En (p :: Phase) where
  V     :: Fin n                    -> En (Syn n)
  P     :: Ref                      -> En p
  (:/)  :: En p       -> Tm p       -> En p
  (:::) :: Tm (Syn n) -> Tm (Syn n) -> En (Syn n)

deriving instance Show (En p)
deriving instance Eq (En (Syn n))

data Tm (p :: Phase) where
  En   :: En p           -> Tm p
  Lam  :: Body p         -> Tm p
  Z    ::                   Tm p
  N    ::                   Tm p
  Pi   :: Tm p -> Body p -> Tm p
  Type ::                   Tm p

deriving instance Show (Tm p)
deriving instance Eq (Tm (Syn n))

instantiate :: Tm (Syn (Suc Zero)) -> Ref -> Tm (Syn Zero)
instantiate t x = subTm SZero (SS S0 (P x)) t

data Ren (m :: Nat)(n :: Nat) where
   R0 :: Ren m Zero
   RS :: Ren m n -> Fin m -> Ren m (Suc n)

rlookup :: Ren m n -> Fin n -> Fin m
rlookup (RS is i) FZero    = i
rlookup (RS is i) (FSuc j) = rlookup is j

rwk :: SNat m -> Ren m n -> Ren (Suc m) n
rwk m    R0        = R0
rwk m (RS is i) = RS (rwk m is) (FSuc i)

rlift :: SNat m -> Ren m n -> Ren (Suc m) (Suc n)
rlift n is = RS (rwk n is) FZero

ren :: SNat m -> Ren m n -> Tm (Syn n) -> Tm (Syn m)
ren n is (En e)               = En $ renEn n is e
ren n is (Lam (SynBody t))    = Lam (SynBody (ren (SSuc n) (rlift n is) t))
ren n is Z                    = Z
ren n is N                    = N
ren n is (Pi _S (SynBody _T)) =
  Pi (ren n is _S) (SynBody (ren (SSuc n) (rlift n is) _T))
ren n is Type                 = Type

renEn :: SNat m -> Ren m n -> En (Syn n) -> En (Syn m)
renEn n is (V i)      = V $ rlookup is i
renEn n _  (P x)      = P x
renEn n is (e :/ s)   = renEn n is e :/ ren n is s
renEn n is (t ::: ty) = ren n is t ::: ren n is ty

renId :: SNat n -> Ren n n
renId SZero    = R0
renId (SSuc n) = RS (rwk n (renId n)) FZero

data Subst (m :: Nat)(n :: Nat) where
   S0 :: Subst m Zero
   SS :: Subst m n -> En (Syn m) -> Subst m (Suc n)

slookup :: Subst m n -> Fin n -> En (Syn m)
slookup (SS es e) FZero    = e
slookup (SS es e) (FSuc i) = slookup es i

swk :: SNat m -> Subst m n -> Subst (Suc m) n
swk m S0 = S0
swk m (SS es e) = SS (swk m es) (renEn (SSuc m) (rwk m (renId m)) e)

slift :: SNat m -> Subst m n -> Subst (Suc m) (Suc n)
slift n es = SS (swk n es) (V FZero)

subTm :: SNat m -> Subst m n -> Tm (Syn n) -> Tm (Syn m)
subTm n es (En e)               = En $ subEn n es e
subTm n es (Lam (SynBody t))    = Lam (SynBody (subTm (SSuc n) (slift n es) t))
subTm n es Z                    = Z
subTm n es N                    = N
subTm n es (Pi _S (SynBody _T)) =
  Pi (subTm n es _S) (SynBody (subTm (SSuc n) (slift n es) _T))
subTm n es Type                 = Type

subEn :: SNat m -> Subst m n -> En (Syn n) -> En (Syn m)
subEn n es (V i)      = slookup es i
subEn n _  (P x)      = P x
subEn n es (e :/ s)   = subEn n es e :/ subTm n es s
subEn n es (t ::: ty) = subTm n es t ::: subTm n es ty

-- intepreter/evaluator

tval :: Env n -> Tm (Syn n) -> Val
tval g (En e)  = valOf (eval g e)
tval g (Lam (SynBody t)) = Lam (SemBody g t)
tval g Z          = Z
tval g N          = N
tval g (Pi s (SynBody t))  = Pi (tval g s) (SemBody g t)
tval g Type       = Type

eval :: Env n -> En (Syn n) -> Thing
eval g (V i     ) = elookup g i
eval g (P r     ) = En (P r) :::: refType r
eval g (e :/ t  ) = eval g e / tval g t
eval g (t ::: ty) = tval g t :::: tval g ty

(/) :: Thing -> Val -> Thing
(Lam (SemBody g t) :::: Pi _S (SemBody g' _T)) / s =
  tval (ES g (s :::: _S)) t :::: tval (ES g' (s :::: _S)) _T
(En e :::: Pi _S (SemBody g _T)) / s =
  En (e :/ s) :::: tval (ES g (s :::: _S)) _T

val :: Tm (Syn Zero) -> Val
val t = tval E0 t

-- quote, needed for equality checking, needs a name supply but doesn't fail
newtype Fresh x = Fresh (Name -> (x,Name)) deriving Functor

runFresh (Fresh f) = fst (f 0)

instance Applicative Fresh where
  pure x = Fresh (\ name -> (x, name))
  Fresh f <*> Fresh a = Fresh $ \name ->
    let (f',newname)    = f name
        (a',newestname) = a name
    in
        (f' a', newestname)

instance Monad Fresh where
  Fresh x >>= f = Fresh $ \ name ->
    let (x' , newname) = x name
        Fresh fx = f x'
    in
        fx newname

-- abstract the free var by weakening then replacing
abstract :: Ref -> SNat n -> Tm (Syn n) -> Tm (Syn (Suc n))
abstract x n t =  replace x FZero (ren (SSuc n) (rwk n (renId n)) t)

-- replaces a given free var with a given bound var, adjusts for binders
replace :: Ref -> Fin n -> Tm (Syn n) -> Tm (Syn n)
replace x i (En e)               = En (ereplace x i e)
replace x i (Lam (SynBody t))    = Lam (SynBody (replace x (FSuc i) t))
replace x i Z                    = Z
replace x i N                    = N
replace x i (Pi _S (SynBody _T)) =
  Pi (replace x i _S) (SynBody (replace x (FSuc i) _T))
replace x i Type                 = Type

ereplace :: Ref -> Fin n -> En (Syn n) -> En (Syn n)
ereplace x i (V j) = V j -- i better not equal j
ereplace x i (P y) | x == y = V i
ereplace x i (P y)          = P y
ereplace x i (e :/ s) = ereplace x i e :/ replace x i s
ereplace x i (t ::: ty) = replace x i t ::: replace x i ty

fresh :: Val -> Fresh Ref
fresh ty = Fresh $ \ i -> (Ref (next i) ty, next i)

quote :: Thing -> Fresh TERM
quote (N :::: Type) = return N
quote (Z :::: N)    = return Z
quote (Pi _S (SemBody g _T) :::: Type) = do
  x <- fresh _S
  dom <- quote (_S :::: Type)
  cod <- quote (tval (ES g (En (P x) :::: _S)) _T :::: Type)
  return $ Pi dom (SynBody (abstract x SZero cod))
quote f@(_    :::: Pi _S _) = do
  x <- fresh _S
  body <- quote (f  / En (P x))
  return $ Lam (SynBody (abstract x SZero body))
quote (En e :::: ty) = fmap (En . fst) $ nquote e

nquote :: Ne -> Fresh (ELIM,Val)
nquote (P x) = pure (P x , refType x) 
nquote (e :/ s) = do
  (e',Pi _S (SemBody g _T)) <- nquote e
  s' <- quote (s :::: _S)
  return (e' :/ s', tval (ES g (s :::: _S)) _T)
  
instance Eq Thing where
  thing1 == thing2 = runFresh (quote thing1) == runFresh (quote thing2)

instance Eq Ne where
  ne1 == ne2 = fst (runFresh (nquote ne1)) == fst (runFresh (nquote ne2))

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

type TERM = Tm (Syn Zero)
type ELIM = En (Syn Zero)

next :: Name -> Name
next = (+1)

-- is the action ok?
(/:>) :: Val -> TERM -> TC ()
Pi _S _T /:> s = _S >:> s >> return ()
ty        /:> s =
  fail $ show s ++ " can't act on something of type " ++ show ty

tcfresh :: Val -> TC Ref
tcfresh ty = TC $ \ i -> Just (Ref (next i) ty, next i)

-- check a term in a trusted type
(>:>) :: Val -> TERM -> TC Val
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
    fail $ show e ++ " ain't the same as " ++ show e'
subType (Pi _S (SemBody g _T)) (Pi _S' (SemBody g' _T')) = do
  subType _S' _S 
  x <- tcfresh _S
  -- might need to pay attention to which domain type is used later
  subType (tval (ES g (En (P x) :::: _S)) _T)
          (tval (ES g' (En (P x) :::: _S')) _T')
subType x y = fail $ show x ++ " ain't the same as " ++ show y

instance Eq Ref where
  Ref i _ == Ref j _ = i == j

-- successful tests
ex1 = N >:> Z
ex2 = Pi N (SemBody E0 N) >:> Lam (SynBody Z)
ex3 = N >:> En ((Lam (SynBody Z) ::: Pi N (SynBody N)) :/ Z)
ex4 = (val $ Pi Type (SynBody (Pi (En (V FZero)) (SynBody (En (V (FSuc FZero))))))) >:> Lam (SynBody (Lam (SynBody (En (V FZero)))))

ex5' = eval E0 (P (Ref (-1) (Pi N (SemBody E0 N))))
ex5'' = eval E0 (Lam (SynBody (En (P (Ref (-1) (Pi N (SemBody E0 N))) :/ En (V FZero)))) ::: Pi N (SynBody N))
ex5 = ex5' == ex5'' -- calls quote

-- Failing tests
fex1 = Pi N (SemBody E0 N) >:> Z
fex2 = N >:> En ((Lam (SynBody Z) ::: Pi N (SynBody N)) :/ N)
fex3 = N >:> En ((Z ::: N) :/ Z)

-- -}
