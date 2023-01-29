{-# OPTIONS --safe #-}

module R.Syntax.IR.Properties where

open import Common.Type using (Type; ℕ´; _⇒_; _≟_)
open import Common.Context using (Context; _,_; _∈_; _⊆_; ∈-subs; keep; here; there)
open import R.Syntax.IR
open import R.Syntax.Base
open import R.Syntax

open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)

{- plfa substitution properties -}
ext : ∀ {Γ Δ}
  → (∀ {τ₁} → τ₁ ∈ Γ → τ₁ ∈ Δ)
    ---------------------------------
  → (∀ {τ₁ τ₂} → τ₁ ∈ Γ , τ₂ → τ₁ ∈ Δ , τ₂)
ext f  here       =  here
ext f (there τ∈Γ) =  there (f τ∈Γ)

rename : ∀ {Γ Δ}
  → (∀ {τ} → τ ∈ Γ → τ ∈ Δ)
    -----------------------
  → (∀ {τ} → Γ ⊢´ τ → Δ ⊢´ τ)
rename f  zero´     = zero´
rename f (suc´ t)   = suc´ (rename f t)
rename f (var x)    = var (f x)
rename f (abs t)    = abs (rename (ext f) t)
rename f (app t t₁) = app (rename f t) (rename f t₁)
rename f (match t t₁ t₂) = match (rename f t) (rename f t₁) (rename (ext f) t₂)
rename f (rec t)    = rec (rename (ext f) t)

exts : ∀ {Γ Δ}
  → (∀ {τ₁} → τ₁ ∈ Γ → Δ ⊢´ τ₁)
    -------------------------------------------
  → (∀ {τ₁ τ₂} → τ₁ ∈ Γ , τ₂ → Δ , τ₂ ⊢´ τ₁)
exts f here      = var here
exts f (there x) = rename there (f x)

subst : ∀ {Γ Δ}
  → (∀ {τ} → τ ∈ Γ → Δ ⊢´ τ)
    --------------------------------
  → (∀ {τ} → Γ ⊢´ τ → Δ ⊢´ τ)
subst f  zero´     = zero´
subst f (suc´ t)   = suc´ (subst f t)
subst f (var x)    = f x
subst f (abs t)    = abs (subst (exts f) t)
subst f (app t t₁) = app (subst f t) (subst f t₁)
subst f (match t t₁ t₂) = match (subst f t) (subst f t₁) (subst (exts f) t₂)
subst f (rec t)    = rec (subst (exts f) t)

subs-lemma : ∀ {Γ τ₁ τ₂} → Γ , τ₂ ⊢´ τ₁ → Γ ⊢´ τ₂ → Γ ⊢´ τ₁
subs-lemma {Γ} {τ₁} {τ₂} t₁ t₂
  = subst {Γ , τ₂} {Γ} (λ {here → t₂ ; (there x) → var x}) {τ₁} t₁
{- end of plfa substitution properties -}

⊢-to-IR : ∀{Γ τ} → Γ ⊢ τ → Γ ⊢´ τ
⊢-to-IR  zero´          = zero´
⊢-to-IR (suc´ t)        = suc´ (⊢-to-IR t)
⊢-to-IR (var x)         = var x
⊢-to-IR (abs t)         = abs (⊢-to-IR t)
⊢-to-IR (app t t₁)      = app (⊢-to-IR t) (⊢-to-IR t₁)
⊢-to-IR (match t t₁ t₂) = match (⊢-to-IR t) (⊢-to-IR t₁) (⊢-to-IR t₂)

⊩-to-IR : ∀{Γ τ} → Γ ⊩ τ → Γ ⊢´ τ
⊩-to-IR (rec t x)  = rec (⊢-to-IR t)
⊩-to-IR (rec∙ t x) = app (⊩-to-IR t) (⊢-to-IR x)
