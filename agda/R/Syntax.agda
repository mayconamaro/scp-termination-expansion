{-# OPTIONS --safe #-}

module R.Syntax where

open import Common.Type using (Type; ℕ´; _⇒_)
open import Common.Context using (Context; _,_; _∈_)
open import R.Syntax.Base
open import R.Syntax.Properties

infix 9 _⊩_
data _⊩_ : Context → Type → Set where
  rec : ∀{Γ τ₁ τ₂}
      (t : Γ , τ₁ ⇒ τ₂ ⊢ τ₁ ⇒ τ₂)
    → (τ₁ ⇒ τ₂) called-in t
    ----------------
    → Γ ⊩ τ₁ ⇒ τ₂

  rec∙ : ∀{Γ τ₁ τ₂}
    → Γ ⊩ τ₁ ⇒ τ₂
    → Γ ⊢ τ₁
    --------------
    → Γ ⊩ τ₂
