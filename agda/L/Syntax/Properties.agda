{-# OPTIONS --safe #-}
module L.Syntax.Properties where

open import Common.Type using (Type; ℕ´; _⇒_)
open import Common.Context using (Context; _,_; _∈_; here; there; _⊆_; ∈-subs; keep)
open import L.Syntax

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

data _not-called-in_ : ∀{Γ τ} → Type → Γ ⊪ τ → Set where
  no-call-err : ∀{Γ τ}
    → τ not-called-in (error {Γ} {τ})

  no-call-zero : ∀{Γ τ}
    → τ not-called-in (zero´ {Γ})

  no-call-suc : ∀{Γ τ}{t : Γ ⊪ ℕ´}
    → τ not-called-in t
    → τ not-called-in suc´ t

  no-call-var : ∀{Γ τ₁ τ₂}{τ∈Γ : τ₂ ∈ Γ}
    → τ₁ ≢ τ₂
    → τ₁ not-called-in var τ∈Γ

  no-call-app : ∀{Γ τ τ₁ τ₂}{t₁ : Γ ⊪ τ₁ ⇒ τ₂}{t₂ : Γ ⊪ τ₁}
    → τ not-called-in t₁
    → τ not-called-in t₂
    → τ not-called-in app t₁ t₂

  no-call-abs : ∀{Γ τ τ₁ τ₂}{t : Γ , τ₁ ⊪ τ₂}
    → τ not-called-in t
    → τ not-called-in abs t

  no-call-match : ∀{Γ τ₁ τ₂}{t₁ : Γ ⊪ ℕ´}{t₂ : Γ ⊪ τ₂}{t₃ : Γ , ℕ´ ⊪ τ₂}
    → τ₁ not-called-in t₁
    → τ₁ not-called-in t₂
    → τ₁ not-called-in t₃
    → τ₁ not-called-in match t₁ t₂ t₃

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
  → (∀ {τ} → Γ ⊪ τ → Δ ⊪ τ)
rename f  error     = error
rename f  zero´     = zero´
rename f (suc´ t)   = suc´ (rename f t)
rename f (var x)    = var (f x)
rename f (abs t)    = abs (rename (ext f) t)
rename f (app t t₁) = app (rename f t) (rename f t₁)
rename f (match t t₁ t₂) = match (rename f t) (rename f t₁) (rename (ext f) t₂)

exts : ∀ {Γ Δ}
  → (∀ {τ₁} → τ₁ ∈ Γ → Δ ⊪ τ₁)
    -------------------------------------------
  → (∀ {τ₁ τ₂} → τ₁ ∈ Γ , τ₂ → Δ , τ₂ ⊪ τ₁)
exts f here      = var here
exts f (there x) = rename there (f x)

subst : ∀ {Γ Δ}
  → (∀ {τ} → τ ∈ Γ → Δ ⊪ τ)
    --------------------------------
  → (∀ {τ} → Γ ⊪ τ → Δ ⊪ τ)
subst f  error     = error
subst f  zero´     = zero´
subst f (suc´ t)   = suc´ (subst f t)
subst f (var x)    = f x
subst f (abs t)    = abs (subst (exts f) t)
subst f (app t t₁) = app (subst f t) (subst f t₁)
subst f (match t t₁ t₂) = match (subst f t) (subst f t₁) (subst (exts f) t₂)

subs-lemma : ∀ {Γ τ₁ τ₂} → Γ , τ₂ ⊪ τ₁ → Γ ⊪ τ₂ → Γ ⊪ τ₁
subs-lemma {Γ} {τ₁} {τ₂} t₁ t₂
  = subst {Γ , τ₂} {Γ} (λ {here → t₂ ; (there x) → var x}) {τ₁} t₁
{- end of plfa substitution properties -}

⊆-subs : ∀ {Γ Δ τ} → Γ ⊆ Δ → Γ ⊪ τ → Δ ⊪ τ
⊆-subs Γ⊆Δ error           = error
⊆-subs Γ⊆Δ zero´           = zero´
⊆-subs Γ⊆Δ (suc´ t)        = suc´ (⊆-subs Γ⊆Δ t)
⊆-subs Γ⊆Δ (var x)         = var (∈-subs Γ⊆Δ x)
⊆-subs Γ⊆Δ (abs t)         = abs (⊆-subs (keep Γ⊆Δ) t)
⊆-subs Γ⊆Δ (app t t₁)      = app (⊆-subs Γ⊆Δ t) (⊆-subs Γ⊆Δ t₁)
⊆-subs Γ⊆Δ (match t t₁ t₂) = match (⊆-subs Γ⊆Δ t) (⊆-subs Γ⊆Δ t₁) (⊆-subs (keep Γ⊆Δ) t₂)
