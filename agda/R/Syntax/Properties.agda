{-# OPTIONS --safe #-}

module R.Syntax.Properties where

open import Common.Type using (Type; ℕ´; _⇒_; _≟_)
open import Common.Context using (Context; _,_; _∈_; _⊆_; ∈-subs; keep; here; there)
open import R.Syntax.Base

open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)

{-
Using ¬ for “not called” raises issues with strict positivity.
A custom not-called relation helps with it.
-}

data _not-called-in_ : ∀{Γ τ} → Type → Γ ⊢ τ → Set where
  no-call-zero : ∀{Γ τ}
    → τ not-called-in (zero´ {Γ})

  no-call-suc : ∀{Γ τ}{t : Γ ⊢ ℕ´}
    → τ not-called-in t
    → τ not-called-in suc´ t

  no-call-var : ∀{Γ τ₁ τ₂}{τ∈Γ : τ₂ ∈ Γ}
    → τ₁ ≢ τ₂
    → τ₁ not-called-in var τ∈Γ

  no-call-app : ∀{Γ τ τ₁ τ₂}{t₁ : Γ ⊢ τ₁ ⇒ τ₂}{t₂ : Γ ⊢ τ₁}
    → τ not-called-in t₁
    → τ not-called-in t₂
    → τ not-called-in app t₁ t₂

  no-call-abs : ∀{Γ τ τ₁ τ₂}{t : Γ , τ₁ ⊢ τ₂}
    → τ not-called-in t
    → τ not-called-in abs t

  no-call-match : ∀{Γ τ₁ τ₂}{t₁ : Γ ⊢ ℕ´}{t₂ : Γ ⊢ τ₂}{t₃ : Γ , ℕ´ ⊢ τ₂}
    → τ₁ not-called-in t₁
    → τ₁ not-called-in t₂
    → τ₁ not-called-in t₃
    → τ₁ not-called-in match t₁ t₂ t₃

data _called-in_ : ∀{Γ τ} → Type → Γ ⊢ τ → Set where
  call-var : ∀{Γ τ}{τ∈Γ : τ ∈ Γ}
    → τ called-in var τ∈Γ

  call-abs : ∀{Γ τ τ₁ τ₂}{t : Γ , τ₁ ⊢ τ₂}
    → τ called-in t
    → τ called-in abs t

  call-suc : ∀{Γ τ}{t : Γ ⊢ ℕ´}
    → τ called-in t
    → τ called-in suc´ t

  call-app1 : ∀{Γ τ τ₁ τ₂}{t₁ : Γ ⊢ τ₁ ⇒ τ₂}{t₂ : Γ ⊢ τ₁}
    → τ called-in t₁
    → τ not-called-in t₂
    → τ called-in app t₁ t₂

  call-app2 : ∀{Γ τ τ₁ τ₂}{t₁ : Γ ⊢ τ₁ ⇒ τ₂}{t₂ : Γ ⊢ τ₁}
    → τ not-called-in t₁
    → τ called-in t₂
    → τ called-in app t₁ t₂

  call-app12 : ∀{Γ τ τ₁ τ₂}{t₁ : Γ ⊢ τ₁ ⇒ τ₂}{t₂ : Γ ⊢ τ₁}
    → τ called-in t₁
    → τ called-in t₂
    → τ called-in app t₁ t₂

  call-match1 : ∀{Γ τ₁ τ₂}{t₁ : Γ ⊢ ℕ´}{t₂ : Γ ⊢ τ₂}{t₃ : Γ , ℕ´ ⊢ τ₂}
    → τ₁ called-in t₁
    → τ₁ not-called-in t₂
    → τ₁ not-called-in t₃
    → τ₁ called-in match t₁ t₂ t₃

  call-match2 : ∀{Γ τ₁ τ₂}{t₁ : Γ ⊢ ℕ´}{t₂ : Γ ⊢ τ₂}{t₃ : Γ , ℕ´ ⊢ τ₂}
    → τ₁ not-called-in t₁
    → τ₁ called-in t₂
    → τ₁ not-called-in t₃
    → τ₁ called-in match t₁ t₂ t₃

  call-match3 : ∀{Γ τ₁ τ₂}{t₁ : Γ ⊢ ℕ´}{t₂ : Γ ⊢ τ₂}{t₃ : Γ , ℕ´ ⊢ τ₂}
    → τ₁ not-called-in t₁
    → τ₁ not-called-in t₂
    → τ₁ called-in t₃
    → τ₁ called-in match t₁ t₂ t₃

  call-match12 : ∀{Γ τ₁ τ₂}{t₁ : Γ ⊢ ℕ´}{t₂ : Γ ⊢ τ₂}{t₃ : Γ , ℕ´ ⊢ τ₂}
    → τ₁ called-in t₁
    → τ₁ called-in t₂
    → τ₁ not-called-in t₃
    → τ₁ called-in match t₁ t₂ t₃

  call-match13 : ∀{Γ τ₁ τ₂}{t₁ : Γ ⊢ ℕ´}{t₂ : Γ ⊢ τ₂}{t₃ : Γ , ℕ´ ⊢ τ₂}
    → τ₁ called-in t₁
    → τ₁ not-called-in t₂
    → τ₁ called-in t₃
    → τ₁ called-in match t₁ t₂ t₃

  call-match23 : ∀{Γ τ₁ τ₂}{t₁ : Γ ⊢ ℕ´}{t₂ : Γ ⊢ τ₂}{t₃ : Γ , ℕ´ ⊢ τ₂}
    → τ₁ not-called-in t₁
    → τ₁ called-in t₂
    → τ₁ called-in t₃
    → τ₁ called-in match t₁ t₂ t₃

  call-match123 : ∀{Γ τ₁ τ₂}{t₁ : Γ ⊢ ℕ´}{t₂ : Γ ⊢ τ₂}{t₃ : Γ , ℕ´ ⊢ τ₂}
    → τ₁ called-in t₁
    → τ₁ called-in t₂
    → τ₁ called-in t₃
    → τ₁ called-in match t₁ t₂ t₃

⊆-subs : ∀{Γ Δ τ} → Γ ⊆ Δ → Γ ⊢ τ → Δ ⊢ τ
⊆-subs Γ⊆Δ zero´      = zero´
⊆-subs Γ⊆Δ (suc´ t)   = suc´ (⊆-subs Γ⊆Δ t)
⊆-subs Γ⊆Δ (var x)    = var (∈-subs Γ⊆Δ x)
⊆-subs Γ⊆Δ (abs t)    = abs (⊆-subs (keep Γ⊆Δ) t)
⊆-subs Γ⊆Δ (app t t₁) = app (⊆-subs Γ⊆Δ t) (⊆-subs Γ⊆Δ t₁)
⊆-subs Γ⊆Δ (match t t₁ t₂) = match (⊆-subs Γ⊆Δ t) (⊆-subs Γ⊆Δ t₁) (⊆-subs (keep Γ⊆Δ) t₂)

no-call-subs : ∀{Γ Δ τ₁ τ₂}{t₁ : Γ ⊢ τ₂}
  → (Γ⊆Δ : Γ ⊆ Δ)
  → τ₁ not-called-in t₁
  → τ₁ not-called-in (⊆-subs Γ⊆Δ t₁)
no-call-subs Γ⊆Δ no-call-zero    = no-call-zero
no-call-subs Γ⊆Δ (no-call-suc c) = no-call-suc (no-call-subs Γ⊆Δ c)
no-call-subs Γ⊆Δ (no-call-var x) = no-call-var x
no-call-subs Γ⊆Δ (no-call-app c c₁)
  = no-call-app (no-call-subs Γ⊆Δ c) (no-call-subs Γ⊆Δ c₁)
no-call-subs Γ⊆Δ (no-call-abs c)
  = no-call-abs (no-call-subs (keep Γ⊆Δ) c)
no-call-subs Γ⊆Δ (no-call-match c c₁ c₂)
  = no-call-match (no-call-subs Γ⊆Δ c)
   (no-call-subs Γ⊆Δ c₁) (no-call-subs (keep Γ⊆Δ) c₂)

call-subs : ∀{Γ Δ τ₁ τ₂}{t₁ : Γ ⊢ τ₂}
  → (Γ⊆Δ : Γ ⊆ Δ)
  → τ₁ called-in t₁
  → τ₁ called-in (⊆-subs Γ⊆Δ t₁)
call-subs Γ⊆Δ call-var     = call-var
call-subs Γ⊆Δ (call-abs c) = call-abs (call-subs (keep Γ⊆Δ) c)
call-subs Γ⊆Δ (call-suc c) = call-suc (call-subs Γ⊆Δ c)
call-subs Γ⊆Δ (call-app1 c x)
  = call-app1 (call-subs Γ⊆Δ c) (no-call-subs Γ⊆Δ x)
call-subs Γ⊆Δ (call-app2 x c)
  = call-app2 (no-call-subs Γ⊆Δ x) (call-subs Γ⊆Δ c)
call-subs Γ⊆Δ (call-app12 c c₁)
  = call-app12 (call-subs Γ⊆Δ c) (call-subs Γ⊆Δ c₁)
call-subs Γ⊆Δ (call-match1 c x x₁)
  = call-match1 (call-subs Γ⊆Δ c) (no-call-subs Γ⊆Δ x)
   (no-call-subs (keep Γ⊆Δ) x₁)
call-subs Γ⊆Δ (call-match2 x c x₁)
  = call-match2 (no-call-subs Γ⊆Δ x) (call-subs Γ⊆Δ c)
   (no-call-subs (keep Γ⊆Δ) x₁)
call-subs Γ⊆Δ (call-match3 x x₁ c)
  = call-match3 (no-call-subs Γ⊆Δ x) (no-call-subs Γ⊆Δ x₁)
   (call-subs (keep Γ⊆Δ) c)
call-subs Γ⊆Δ (call-match12 c c₁ x)
  = call-match12 (call-subs Γ⊆Δ c) (call-subs Γ⊆Δ c₁)
   (no-call-subs (keep Γ⊆Δ) x)
call-subs Γ⊆Δ (call-match13 c x c₁)
  = call-match13 (call-subs Γ⊆Δ c) (no-call-subs Γ⊆Δ x)
   (call-subs (keep Γ⊆Δ) c₁)
call-subs Γ⊆Δ (call-match23 x c c₁)
  = call-match23 (no-call-subs Γ⊆Δ x) (call-subs Γ⊆Δ c)
   (call-subs (keep Γ⊆Δ) c₁)
call-subs Γ⊆Δ (call-match123 c c₁ c₂)
  = call-match123 (call-subs Γ⊆Δ c) (call-subs Γ⊆Δ c₁)
   (call-subs (keep Γ⊆Δ) c₂)
