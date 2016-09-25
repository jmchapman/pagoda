{-# LANGUAGE KindSignatures, DataKinds, GADTs,
             StandaloneDeriving,
             TypeSynonymInstances,
             FlexibleInstances,
             DeriveFunctor #-}
module Syntax where

import Utils
import Control.Monad

-- syntax

type Name = Int

next :: Name -> Name
next = (+1)

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

instance Eq Ref where
  Ref i _ == Ref j _ = i == j

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

-- syntactic manipulations

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
