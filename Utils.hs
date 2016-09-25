{-# LANGUAGE DataKinds, KindSignatures, GADTs,
    StandaloneDeriving #-}
module Utils where

data Nat = Zero | Suc Nat deriving Show

data SNat n where
  SZero :: SNat Zero
  SSuc  :: SNat n -> SNat (Suc n)

deriving instance Show (SNat n)

data Fin (n :: Nat) where
  FZero :: Fin (Suc n)
  FSuc  :: Fin n -> Fin (Suc n)

deriving instance Show (Fin n)
deriving instance Eq   (Fin n)

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

