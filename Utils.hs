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
