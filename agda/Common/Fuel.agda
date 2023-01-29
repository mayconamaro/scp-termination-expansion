{-# OPTIONS --safe #-}

module Common.Fuel where

open import Data.Nat using (ℕ)

data Fuel : ℕ → Set where
  gas : (f : ℕ) → Fuel f
