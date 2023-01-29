{-# OPTIONS --safe #-}

module Transform.Translation where

open import Common.Fuel
open import Common.Type
open import Common.Context
open import R.Syntax.Base
open import R.Syntax
open import R.Syntax.Properties
open import R.Syntax.Unrolling
open import L.Syntax
open import L.Syntax.Properties renaming (_not-called-in_ to _n-c_) hiding (⊆-subs)

open import Data.Product using (∃; proj₁; proj₂) renaming (_,_ to _/\_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)

⊢-to-⊪ : ∀{Γ τ} → Γ ⊢ τ → Γ ⊪ τ
⊢-to-⊪  zero´          = zero´
⊢-to-⊪ (suc´ t)        = suc´ (⊢-to-⊪ t)
⊢-to-⊪ (var x)         = var x
⊢-to-⊪ (abs t)         = abs (⊢-to-⊪ t)
⊢-to-⊪ (app t t₁)      = app (⊢-to-⊪ t) (⊢-to-⊪ t₁)
⊢-to-⊪ (match t t₁ t₂) = match (⊢-to-⊪ t) (⊢-to-⊪ t₁) (⊢-to-⊪ t₂)

⊢-to-⊪-nc : ∀{Γ τ τ'}{t : Γ ⊢ τ} → τ' not-called-in t → τ' n-c (⊢-to-⊪ t)
⊢-to-⊪-nc no-call-zero            = no-call-zero
⊢-to-⊪-nc (no-call-suc c)         = no-call-suc (⊢-to-⊪-nc c)
⊢-to-⊪-nc (no-call-var x)         = no-call-var x
⊢-to-⊪-nc (no-call-app c c₁)      = no-call-app (⊢-to-⊪-nc c) (⊢-to-⊪-nc c₁)
⊢-to-⊪-nc (no-call-abs c)         = no-call-abs (⊢-to-⊪-nc c)
⊢-to-⊪-nc (no-call-match c c₁ c₂) = no-call-match (⊢-to-⊪-nc c)
                                          (⊢-to-⊪-nc c₁) (⊢-to-⊪-nc c₂)

call-elimination : ∀{Γ τ τ₁}{t : Γ ⊢ τ} → τ₁ called-in t → Γ ⊪ τ
call-elimination {t = .(var _)}    call-var
  = error
call-elimination {t = .(abs _)}   (call-abs c)
  = abs (call-elimination c)
call-elimination {t = .(suc´ _)}  (call-suc c)
  = suc´ (call-elimination c)
call-elimination {t = app _ t₂}   (call-app1 c _)
  = app (call-elimination c) (⊢-to-⊪ t₂)
call-elimination {t = app t₁ _}   (call-app2 _ c)
  = app (⊢-to-⊪ t₁) (call-elimination c)
call-elimination {t = .(app _ _)} (call-app12 c c₁)
  = app (call-elimination c) (call-elimination c₁)
call-elimination {t = match _ t₁ t₂} (call-match1 c _ _)
  = match (call-elimination c) (⊢-to-⊪ t₁) (⊢-to-⊪ t₂)
call-elimination {t = match t _ t₂} (call-match2 _ c _)
  = match (⊢-to-⊪ t) (call-elimination c) (⊢-to-⊪ t₂)
call-elimination {t = match t t₁ _} (call-match3 _ _ c)
  = match (⊢-to-⊪ t) (⊢-to-⊪ t₁) (call-elimination c)
call-elimination {t = match _ _ t₂} (call-match12 c c₁ _)
  = match (call-elimination c) (call-elimination c₁) (⊢-to-⊪ t₂)
call-elimination {t = match _ t₁ _} (call-match13 c _ c₁)
  = match (call-elimination c) (⊢-to-⊪ t₁) (call-elimination c₁)
call-elimination {t = match t _ _} (call-match23 _ c c₁)
  = match (⊢-to-⊪ t) (call-elimination c) (call-elimination c₁)
call-elimination {t = .(match _ _ _)} (call-match123 c c₁ c₂)
  = match (call-elimination c) (call-elimination c₁) (call-elimination c₂)

no-call-in-elimination : ∀{Γ τ τ₁}{t : Γ ⊢ τ}(c : τ₁ called-in t)
                         → τ₁ n-c (call-elimination c)
no-call-in-elimination call-var
  = no-call-err
no-call-in-elimination (call-abs c)
  = no-call-abs (no-call-in-elimination c)
no-call-in-elimination (call-suc c)
  = no-call-suc (no-call-in-elimination c)
no-call-in-elimination (call-app1 c x)
  = no-call-app (no-call-in-elimination c) (⊢-to-⊪-nc x)
no-call-in-elimination (call-app2 x c)
  = no-call-app (⊢-to-⊪-nc x) (no-call-in-elimination c)
no-call-in-elimination (call-app12 c c₁)
  = no-call-app (no-call-in-elimination c) (no-call-in-elimination c₁)
no-call-in-elimination (call-match1 c x x₁)
  = no-call-match (no-call-in-elimination c) (⊢-to-⊪-nc x) (⊢-to-⊪-nc x₁)
no-call-in-elimination (call-match2 x c x₁)
  = no-call-match (⊢-to-⊪-nc x) (no-call-in-elimination c) (⊢-to-⊪-nc x₁)
no-call-in-elimination (call-match3 x x₁ c)
  = no-call-match (⊢-to-⊪-nc x) (⊢-to-⊪-nc x₁) (no-call-in-elimination c)
no-call-in-elimination (call-match12 c c₁ x)
  = no-call-match (no-call-in-elimination c) (no-call-in-elimination c₁) (⊢-to-⊪-nc x)
no-call-in-elimination (call-match13 c x c₁)
  = no-call-match (no-call-in-elimination c) (⊢-to-⊪-nc x) (no-call-in-elimination c₁)
no-call-in-elimination (call-match23 x c c₁)
  = no-call-match (⊢-to-⊪-nc x) (no-call-in-elimination c) (no-call-in-elimination c₁)
no-call-in-elimination (call-match123 c c₁ c₂)
  = no-call-match (no-call-in-elimination c)
    (no-call-in-elimination c₁) (no-call-in-elimination c₂)

trivial-term : ∀{Γ} (τ : Type) → Γ ⊪ τ
trivial-term  ℕ´      = zero´
trivial-term (τ ⇒ τ₁) = abs (trivial-term τ₁)

closure : ∀{τ₁ τ₂} → ∅ , τ₁ ⊪ τ₂ → ∅ ⊪ τ₂
closure {τ₁} {τ₂} t = app (abs t) (trivial-term τ₁)

translate : ∀{τ} → ∅ ⊩ τ → ∅ ⊪ τ
translate (rec t x)  = closure (call-elimination x)
translate (rec∙ t x) = app (translate t) (⊢-to-⊪ x)

-- Alternative translation, if you don't want closure or closed terms
translate' : ∀{τ} → ∅ ⊩ τ → ∃ (λ Δ → Δ ⊪ τ)
translate' (rec {_} {τ₁} {τ₂} t x)
  = (∅ , τ₁ ⇒ τ₂) /\ (call-elimination x)
translate' (rec∙ t x)
  = (proj₁ (translate' t)) /\ app (proj₂ (translate' t)) (⊢-to-⊪ (⊆-subs ⊆-∅ x))

transform : ∀{τ n} → Fuel n → ∅ ⊩ τ → ∅ ⊪ τ
transform f t = translate (unroll f t)
