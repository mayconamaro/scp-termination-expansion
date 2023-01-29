{-# OPTIONS --safe #-}

module R.Syntax.Base where

open import Common.Type using (Type; ℕ´; _⇒_)
open import Common.Context using (Context; _,_; _∈_)

infix 9 _⊢_
data _⊢_ : Context → Type → Set where
  zero´ : ∀{Γ}
    → Γ ⊢ ℕ´

  suc´ : ∀{Γ}
    → Γ ⊢ ℕ´
    ---------
    → Γ ⊢ ℕ´

  var : ∀{Γ τ}
    → τ ∈ Γ
    ---------
    → Γ ⊢ τ

  abs : ∀{Γ τ₁ τ₂}
    → Γ , τ₁ ⊢ τ₂
    ------------------
    → Γ ⊢ τ₁ ⇒ τ₂

  app : ∀{Γ τ₁ τ₂}
    → Γ ⊢ τ₁ ⇒ τ₂
    → Γ ⊢ τ₁
    -------------
    → Γ ⊢ τ₂

  match : ∀{Γ τ}
    → Γ ⊢ ℕ´
    → Γ ⊢ τ
    → Γ , ℕ´ ⊢ τ
    ----------------
    → Γ ⊢ τ
