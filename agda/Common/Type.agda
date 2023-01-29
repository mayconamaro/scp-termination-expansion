{-# OPTIONS --safe #-}

module Common.Type where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

infixr 16 _⇒_
data Type : Set where
  ℕ´  : Type
  _⇒_ : Type → Type → Type

_≟_ : ∀ (τ₁ τ₂ : Type) → Dec (τ₁ ≡ τ₂)
ℕ´ ≟ ℕ´        = yes refl
ℕ´ ≟ (τ₂ ⇒ τ₃) = no λ ()
(τ₁ ⇒ τ₂) ≟ ℕ´ = no λ ()
(τ₁ ⇒ τ₂) ≟ (τ₃ ⇒ τ₄) with τ₁ ≟ τ₃ | τ₂ ≟ τ₄
... | yes refl  | yes refl  = yes refl
... | yes τ₁≡τ₃ | no  τ₂≢τ₄ = no λ {refl → τ₂≢τ₄ refl}
... | no  τ₁≢τ₃ | _         = no λ {refl → τ₁≢τ₃ refl}
