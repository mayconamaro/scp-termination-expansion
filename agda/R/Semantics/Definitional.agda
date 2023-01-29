{-# OPTIONS --safe #-}

module R.Semantics.Definitional where

open import Common.Type
open import Common.Context
open import Common.Fuel
open import R.Syntax.Base
open import R.Syntax

open import Data.Nat     using (ℕ; suc; zero)
open import Data.Unit    using (⊤; tt)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to _/\_)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Maybe   using (Maybe; just; nothing)

T⟦_⟧ : Type → Set
T⟦ ℕ´ ⟧      = ℕ ⊎ ⊤
T⟦ τ₁ ⇒ τ₂ ⟧ = (T⟦ τ₁ ⟧ → T⟦ τ₂ ⟧) ⊎ ⊤

C⟦_⟧ : Context → Set
C⟦ ∅ ⟧     = ⊤
C⟦ Γ , τ ⟧ = T⟦ τ ⟧ × C⟦ Γ ⟧

V⟦_⟧ : ∀{Γ τ} → τ ∈ Γ → C⟦ Γ ⟧ → T⟦ τ ⟧
V⟦ here ⟧    (x /\ env) = x
V⟦ there e ⟧ (x /\ env) = V⟦ e ⟧ env

eval' : ∀{Γ τ} → Γ ⊢ τ → C⟦ Γ ⟧ → T⟦ τ ⟧
eval'  zero´          env = inj₁ zero
eval' (suc´ t)        env with eval' t env
... | inj₁ n = inj₁ (suc n)
... | inj₂ _ = inj₂ tt
eval' (var x)         env = V⟦ x ⟧ env
eval' (abs t)         env = inj₁ (λ x → eval' t (x /\ env))
eval' {τ = ℕ´} (app t t₁) env with eval' t env | eval' t₁ env
... | inj₁ x  | y = x y
... | inj₂ _  | _ = inj₂ tt
eval' {τ = τ ⇒ τ₁} (app t t₁) env with eval' t env | eval' t₁ env
... | inj₁ x | y = x y
... | inj₂ _ | _ = inj₂ tt
eval' {τ = ℕ´} (match t t₁ t₂) env with eval' t env
... | inj₁ zero    = eval' t₁ env
... | inj₁ (suc n) = eval' t₂ ((inj₁ n) /\ env)
... | inj₂ _       = inj₂ tt
eval' {τ = τ ⇒ τ₁} (match t t₁ t₂) env with eval' t env
... | inj₁ zero    = eval' t₁ env
... | inj₁ (suc n) = eval' t₂ ((inj₁ n) /\ env)
... | inj₂ _       = inj₂ tt

eval : ∀{Γ τ n} → Fuel n → Γ ⊩ τ → C⟦ Γ ⟧ → T⟦ τ ⟧
eval {τ = ℕ´}     (gas zero) t _ = inj₂ tt
eval {τ = τ ⇒ τ₁} (gas zero) t _ = inj₂ tt
eval (gas (suc f)) (rec t x)  env with eval (gas f) (rec t x) env
... | inj₁ z = eval' t ((inj₁ z) /\ env)
... | inj₂ _ = eval' t ((inj₂ tt) /\ env)
eval {τ = ℕ´}     (gas (suc f)) (rec∙ t x) env with eval (gas (suc f)) t env
... | inj₁ z = z (eval' x env)
... | inj₂ _ = inj₂ tt
eval {τ = τ ⇒ τ₁} (gas (suc f)) (rec∙ t x) env with eval (gas (suc f)) t env
... | inj₁ z = z (eval' x env)
... | inj₂ _ = inj₂ tt

∅-eval : ∀{τ n} → Fuel n → ∅ ⊩ τ → T⟦ τ ⟧
∅-eval f t = eval f t tt
