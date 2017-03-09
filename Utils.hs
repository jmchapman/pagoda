{-# LANGUAGE DataKinds, KindSignatures, GADTs,
    StandaloneDeriving #-}
{-# OPTIONS_GHC -Wall #-}
module Utils where

data Nat = Zero | Suc Nat deriving Show

data SNat n where
  SZero :: SNat 'Zero
  SSuc  :: SNat n -> SNat ('Suc n)

deriving instance Show (SNat n)

data Fin (n :: Nat) where
  FZero :: Fin ('Suc n)
  FSuc  :: Fin n -> Fin ('Suc n)

deriving instance Show (Fin n)
deriving instance Eq   (Fin n)

data Vec x (n :: Nat) where
  VNil  :: Vec x 'Zero
  VCons :: x -> Vec x n -> Vec x ('Suc n)

deriving instance Show x => Show (Vec x n)

vlookup :: Fin n -> Vec x n -> x
vlookup FZero    (VCons x _ ) = x
vlookup (FSuc i) (VCons _ xs) = vlookup i xs
vlookup _        _            = error "impossible vlookup in empty vector"
  -- would be nice to omit this case

data BVec x (n :: Nat) where
  BNil  :: BVec x 'Zero
  BCons :: BVec x n -> x -> BVec x ('Suc n)

deriving instance Show x => Show (BVec x n)

blookup :: Fin n -> BVec x n -> x
blookup FZero    (BCons _  x) = x
blookup (FSuc i) (BCons xs _) = blookup i xs
blookup _        _            = error "impossible vlookup in empty vector"


-- find the first x in the vector and return its index
velemIndex :: Eq x => x -> Vec x n -> Maybe (Fin n)
velemIndex _ VNil          = Nothing
velemIndex x (VCons x' xs) =
  if x == x' then
    Just FZero              
  else
    fmap FSuc (velemIndex x xs)

-- find the nth x in the vector and return its index
velemIndex' :: Eq x => x -> Nat ->  Vec x n -> Maybe (Fin n)
velemIndex' _ _ VNil          = Nothing
velemIndex' x n (VCons x' xs) =
  if x == x' then
    case n of
      Zero  -> Just FZero
      Suc _ -> fmap FSuc (velemIndex' x n xs)
  else
    fmap FSuc (velemIndex' x n xs)
