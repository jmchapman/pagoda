{-# LANGUAGE KindSignatures, 
             DataKinds, 
             GADTs,
             StandaloneDeriving,
             TypeSynonymInstances,
             FlexibleInstances,
             DeriveFunctor #-}
{-# OPTIONS_GHC -Wall #-}
module Syntax where

import Utils
import Control.Monad()

-- Syntax

-- names are currently just integers, doesn't allow branching
type Name = Int

-- fresh name creation
next :: Name -> Name
next = (+1)

-- terms are parameterised by their phases, syntactic terms are open,
-- semantic terms are closed
data Phase = Syn Nat | Sem

type Val = Tm 'Sem
type Ne  = En 'Sem
data Thing = (::::) {valOf :: Val, typeOf :: Val} deriving Show

type TERM = Tm ('Syn 'Zero)
type ELIM = En ('Syn 'Zero)

type Env = BVec Thing

-- bodies of lambdas and pis
-- in the syntax they are terms, in the semantics they are closures
data Body p where
  SynBody :: Tm ('Syn ('Suc n)) -> Body ('Syn n)
  SemBody :: Env n -> Tm ('Syn ('Suc n)) -> Body 'Sem

deriving instance Show (Body p)
instance Eq   (Body ('Syn p)) where
  SynBody t == SynBody t' = t == t'

-- free variables
data Ref = Ref {refName :: Name, refType :: Val} deriving Show

instance Eq Ref where
  Ref i _ == Ref j _ = i == j

-- bits for the ends of the interval
data Bit = B0 | B1 deriving (Show, Eq)

data En (p :: Phase) where
  V     :: Fin n                    -> En ('Syn n)
  P     :: Ref                      -> En p
  (:/)  :: En p       -> Tm p       -> En p
  (:::) :: Tm ('Syn n) -> Tm ('Syn n) -> En ('Syn n)

deriving instance Show (En p)
deriving instance Eq (En ('Syn n))

data Tm (p :: Phase) where
  En   :: En p           -> Tm p
  I    :: Bit            -> Tm p
  Lam  :: Body p         -> Tm p
  Z    ::                   Tm p
  N    ::                   Tm p
  Pi   :: Tm p -> Body p -> Tm p
  Path :: Tm p -> Tm p   -> Tm p
  Type ::                   Tm p
  Pt   ::                   Tm p

deriving instance Show (Tm p)
deriving instance Eq (Tm ('Syn n))
-- we do not what a structural equality for Val

-- syntactic manipulations

instantiate :: Tm ('Syn ('Suc 'Zero)) -> Ref -> TERM
instantiate t x = subTm SZero (BCons BNil (P x)) t

-- renamings
type Ren m n = BVec (Fin m) n

rwk :: SNat m -> Ren m n -> Ren ('Suc m) n
rwk _ BNil        = BNil
rwk m (BCons is i) = BCons (rwk m is) (FSuc i)

rlift :: SNat m -> Ren m n -> Ren ('Suc m) ('Suc n)
rlift n is = BCons (rwk n is) FZero

ren :: SNat m -> Ren m n -> Tm ('Syn n) -> Tm ('Syn m)
ren n is (En e)               = En $ renEn n is e
ren _ _  (I b)                = I b
ren n is (Lam (SynBody t))    = Lam (SynBody (ren (SSuc n) (rlift n is) t))
ren _ _  Z                    = Z
ren _ _  N                    = N
ren n is (Pi _S (SynBody _T)) =
  Pi (ren n is _S) (SynBody (ren (SSuc n) (rlift n is) _T))
ren n is (Path _S _T)         = Path (ren n is _S) (ren n is _T)
ren _ _  Type                 = Type
ren _ _  Pt                   = Pt

renEn :: SNat m -> Ren m n -> En ('Syn n) -> En ('Syn m)
renEn _ is (V i)      = V $ blookup i is
renEn _ _  (P x)      = P x
renEn n is (e :/ s)   = renEn n is e :/ ren n is s
renEn n is (t ::: ty) = ren n is t ::: ren n is ty

renId :: SNat n -> Ren n n
renId SZero    = BNil
renId (SSuc n) = BCons (rwk n (renId n)) FZero


type Subst m n = BVec (En ('Syn m)) n
  -- why not Sub?

swk :: SNat m -> Subst m n -> Subst ('Suc m) n
swk _ BNil = BNil
swk m (BCons es e) = BCons (swk m es) (renEn (SSuc m) (rwk m (renId m)) e)

slift :: SNat m -> Subst m n -> Subst ('Suc m) ('Suc n)
slift n es = BCons (swk n es) (V FZero)

subTm :: SNat m -> Subst m n -> Tm ('Syn n) -> Tm ('Syn m)
subTm n es (En e)               = En $ subEn n es e
subTm _ _ (I b)                = I b
subTm n es (Lam (SynBody t))    = Lam (SynBody (subTm (SSuc n) (slift n es) t))
subTm _ _ Z                    = Z
subTm _ _ N                    = N
subTm n es (Pi _S (SynBody _T)) =
  Pi (subTm n es _S) (SynBody (subTm (SSuc n) (slift n es) _T))
subTm n es (Path _S _T)         = Path (subTm n es _S) (subTm n es _T)
subTm _ _ Type                 = Type
subTm _ _ Pt                   = Pt

subEn :: SNat m -> Subst m n -> En ('Syn n) -> En ('Syn m)
subEn _ es (V i)      = blookup i es
subEn _ _  (P x)      = P x
subEn n es (e :/ s)   = subEn n es e :/ subTm n es s
subEn n es (t ::: ty) = subTm n es t ::: subTm n es ty

-- abstract the free var by weakening then replacing
abstract :: Ref -> SNat n -> Tm ('Syn n) -> Tm ('Syn ('Suc n))
abstract x n t =  replace x FZero (ren (SSuc n) (rwk n (renId n)) t)

-- replaces a given free var with a given bound var, adjusts for binders
replace :: Ref -> Fin n -> Tm ('Syn n) -> Tm ('Syn n)
replace x i (En e)               = En (ereplace x i e)
replace _ _ (I b)                = I b
replace x i (Lam (SynBody t))    = Lam (SynBody (replace x (FSuc i) t))
replace _ _ Z                    = Z
replace _ _ N                    = N
replace x i (Pi _S (SynBody _T)) =
  Pi (replace x i _S) (SynBody (replace x (FSuc i) _T))
replace x i (Path _S _T)         = Path (replace x i _S) (replace x i _T)
replace _ _ Type                 = Type
replace _ _ Pt                   = Pt

ereplace :: Ref -> Fin n -> En ('Syn n) -> En ('Syn n)
ereplace _ _ (V j) = V j -- i better not equal j
ereplace x i (P y) | x == y = V i
ereplace _ _ (P y)          = P y
ereplace x i (e :/ s) = ereplace x i e :/ replace x i s
ereplace x i (t ::: ty) = replace x i t ::: replace x i ty
