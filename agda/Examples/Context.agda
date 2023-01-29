{-# OPTIONS --safe #-}

module Examples.Context where

open import Common.Type
open import Common.Context

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)

{- Pertinence Example -}
ex1 : ℕ´ ∈ ∅ , ℕ´ , ℕ´ , ℕ´ , ℕ´
ex1 = there here

{- it is position 1 on [a, b, c, d] and position 2 on [d, c, b, a] -}
_ : bind-index ex1 ≡ 1
_ = refl

_ : bind-level ex1 ≡ 2
_ = refl
