{-# OPTIONS --safe #-}

module L.Semantics.Definitional where

open import Common.Type
open import Common.Context
open import L.Syntax
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to _/\_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)

T⟦_⟧ : Type → Set
T⟦ ℕ´ ⟧      = ℕ ⊎ ⊤
T⟦ τ₁ ⇒ τ₂ ⟧ = (T⟦ τ₁ ⟧ → T⟦ τ₂ ⟧) ⊎ ⊤

C⟦_⟧ : Context → Set
C⟦ ∅ ⟧     = ⊤
C⟦ Γ , τ ⟧ = T⟦ τ ⟧ × C⟦ Γ ⟧

V⟦_⟧ : ∀{τ Γ} → τ ∈ Γ → C⟦ Γ ⟧ → T⟦ τ ⟧
V⟦ here ⟧    (x /\ xs) = x
V⟦ there e ⟧ (x /\ xs) = V⟦ e ⟧ xs

eval : ∀{Γ τ} → Γ ⊪ τ → C⟦ Γ ⟧ → T⟦ τ ⟧
eval  {τ = ℕ´}      error env      = inj₂ tt
eval  {τ = τ₁ ⇒ τ₂} error env      = inj₂ tt
eval  zero´               env      = inj₁ zero
eval (suc´ t)             env
  with eval t env
... | inj₁ n                       = inj₁ (suc n)
... | inj₂ _                       = inj₂ tt
eval (var x)              env      = V⟦ x ⟧ env
eval (abs t)              env      = inj₁ (λ x → eval t (x /\ env))
eval {τ = ℕ´}  (app t t₁) env
  with eval t env | eval t₁ env
... | inj₁ f | y                   = f y
... | inj₂ _ | y                   = inj₂ tt
eval {τ = τ ⇒ τ₁} (app t t₁) env
  with eval t env | eval t₁ env
... | inj₁ f | y                   = f y
... | inj₂ _ | y                   = inj₂ tt
eval {τ = ℕ´} (match t t₁ t₂) env
  with eval t env
... | inj₁ zero                    = eval t₁ env
... | inj₁ (suc n)                 = eval t₂ ((inj₁ n) /\ env)
... | inj₂ _                       = inj₂ tt
eval {τ = τ ⇒ τ₁} (match t t₁ t₂) env
  with eval t env
... | inj₁ zero                    = eval t₁ env
... | inj₁ (suc n)                 = eval t₂ ((inj₁ n) /\ env)
... | inj₂ _                       = inj₂ tt

∅-eval : ∀{τ} → ∅ ⊪ τ → T⟦ τ ⟧
∅-eval t = eval t tt
