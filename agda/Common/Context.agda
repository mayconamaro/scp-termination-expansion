{-# OPTIONS --safe #-}

module Common.Context where

open import Common.Type using (Type; ℕ´)
open import Data.Nat using (ℕ; zero; suc)

infixl 15 _,_
data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

infix 10 _∈_
data _∈_ : Type → Context → Set where
  here : ∀{Γ τ}→ τ ∈ Γ , τ
  there : ∀{Γ τ₁ τ₂} → τ₁ ∈ Γ → τ₁ ∈ Γ , τ₂

infix 9 _⊆_
data _⊆_ : Context → Context → Set where
  empty : ∅ ⊆ ∅
  keep  : ∀{Γ Δ τ} → Γ ⊆ Δ → Γ , τ ⊆ Δ , τ
  drop  : ∀{Γ Δ τ} → Γ ⊆ Δ → Γ ⊆ Δ , τ

∈-subs : ∀{Γ Δ τ} → Γ ⊆ Δ → τ ∈ Γ → τ ∈ Δ
∈-subs empty ()
∈-subs (keep Γ⊆Δ)  here       = here
∈-subs (keep Γ⊆Δ) (there τ∈Γ) = there (∈-subs Γ⊆Δ τ∈Γ)
∈-subs (drop Γ⊆Δ)  τ∈Γ        = there (∈-subs Γ⊆Δ τ∈Γ)

⊆-refl : ∀{Γ} → Γ ⊆ Γ
⊆-refl {∅}     = empty
⊆-refl {Γ , τ} = keep (⊆-refl)

⊆-∅ : ∀{Γ} → ∅ ⊆ Γ
⊆-∅ {∅}     = empty
⊆-∅ {Γ , _} = drop ⊆-∅

⊆-wk : ∀{Γ τ} → Γ ⊆ Γ , τ
⊆-wk = drop ⊆-refl

{-
Contexts are foldable
-}
context-foldr : {A : Set} → (Type → A → A) → A → Context → A
context-foldr f v  ∅      = v
context-foldr f v (Γ , τ) = f τ (context-foldr f v Γ)

length : Context → ℕ
length = context-foldr (λ _ → suc) 0

{-
Calculate De Bruijn Indices and Levels
-}
bind-index : ∀{Γ τ} → τ ∈ Γ → ℕ
bind-index here      = 0
bind-index (there e) = suc (bind-index e)

bind-level : ∀{Γ τ} → τ ∈ Γ → ℕ
bind-level {Γ , τ} {_}  here = length Γ
bind-level {Γ} {_} (there e) = bind-level e
