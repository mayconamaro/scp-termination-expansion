{-# OPTIONS --safe #-}

module R.Syntax.Unrolling where

open import Common.Type using (Type; ℕ´; _⇒_)
open import Common.Fuel using (Fuel; gas)
import Common.Context as Ctx
open Ctx using (Context; _,_; _∈_; _⊆_; ∈-subs; keep; drop; ⊆-refl)
open import R.Syntax.Base
open import R.Syntax.Properties
open import R.Syntax

open import Data.Product using (∃; proj₁; proj₂) renaming (_,_ to _/\_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

{-
Inlines term t₂ into t₁ replacing τ₂.
Inlining preserves variable calls.
-}
inline : ∀{Γ Δ τ₁ τ₂}{t₁ : Γ ⊢ τ₁}{t₂ : Δ ⊢ τ₂}
  → τ₂ called-in t₁
  → τ₂ called-in t₂
  → Δ ⊆ Γ
  → ∃ (λ (t₃ : Γ ⊢ τ₁) → τ₂ called-in t₃)
inline {t₂ = t₂} call-var c₂ Δ⊆Γ
  = ⊆-subs Δ⊆Γ t₂ /\ call-subs Δ⊆Γ c₂
inline (call-abs c₁) c₂ Δ⊆Γ
  = abs (proj₁ (inline c₁ c₂ (drop Δ⊆Γ)))
    /\ call-abs (proj₂ (inline c₁ c₂ (drop Δ⊆Γ)))
inline (call-suc c₁) c₂ Δ⊆Γ
  = suc´ (proj₁ (inline c₁ c₂ Δ⊆Γ))
    /\ call-suc (proj₂ (inline c₁ c₂ Δ⊆Γ))
inline {t₁ = app t t'} (call-app1 c₁ x) c₂ Δ⊆Γ
  = app (proj₁ (inline c₁ c₂ Δ⊆Γ)) t'
    /\ call-app1 (proj₂ (inline c₁ c₂ Δ⊆Γ)) x
inline {t₁ = app t t'} (call-app2 x c₁) c₂ Δ⊆Γ
  = (app t (proj₁ (inline c₁ c₂ Δ⊆Γ)))
    /\ (call-app2 x (proj₂ (inline c₁ c₂ Δ⊆Γ)))
inline (call-app12 c₁ c₃) c₂ Δ⊆Γ
  = (app (proj₁ (inline c₁ c₂ Δ⊆Γ)) (proj₁ (inline c₃ c₂ Δ⊆Γ)))
    /\ (call-app12 (proj₂ (inline c₁ c₂ Δ⊆Γ)) (proj₂ (inline c₃ c₂ Δ⊆Γ)))
inline {t₁ = match t t₁ t₂}(call-match1 c₁ x x₁) c₂ Δ⊆Γ
  = match (proj₁ (inline c₁ c₂ Δ⊆Γ)) t₁ t₂
    /\ call-match1 (proj₂ (inline c₁ c₂ Δ⊆Γ)) x x₁
inline {t₁ = match t t₁ t₂} (call-match2 x c₁ x₁) c₂ Δ⊆Γ
  = match t (proj₁ (inline c₁ c₂ Δ⊆Γ)) t₂
    /\ call-match2 x (proj₂ (inline c₁ c₂ Δ⊆Γ)) x₁
inline {t₁ = match t t₁ t₂} (call-match3 x x₁ c₁) c₂ Δ⊆Γ
  = match t t₁ (proj₁ (inline c₁ c₂ (drop Δ⊆Γ)))
    /\ call-match3 x x₁ (proj₂ (inline c₁ c₂ (drop Δ⊆Γ)))
inline {t₁ = match t t₁ t₂} (call-match12 c₁ c₃ x) c₂ Δ⊆Γ
  = match (proj₁ (inline c₁ c₂ Δ⊆Γ)) (proj₁ (inline c₃ c₂ Δ⊆Γ)) t₂
    /\ call-match12 (proj₂ (inline c₁ c₂ Δ⊆Γ)) (proj₂ (inline c₃ c₂ Δ⊆Γ)) x
inline {t₁ = match t t₁ t₂} (call-match13 c₁ x c₃) c₂ Δ⊆Γ
  = match (proj₁ (inline c₁ c₂ Δ⊆Γ)) t₁ (proj₁ (inline c₃ c₂ (drop Δ⊆Γ)))
    /\ call-match13 (proj₂ (inline c₁ c₂ Δ⊆Γ)) x
      (proj₂ (inline c₃ c₂ (drop Δ⊆Γ)))
inline {t₁ = match t t₁ t₂} (call-match23 x c₁ c₃) c₂ Δ⊆Γ
  = match t (proj₁ (inline c₁ c₂ Δ⊆Γ)) (proj₁ (inline c₃ c₂ (drop Δ⊆Γ)))
    /\ call-match23 x (proj₂ (inline c₁ c₂ Δ⊆Γ))
      (proj₂ (inline c₃ c₂ (drop Δ⊆Γ)))
inline (call-match123 c₁ c₃ c₄) c₂ Δ⊆Γ
  = match (proj₁ (inline c₁ c₂ Δ⊆Γ)) (proj₁ (inline c₃ c₂ Δ⊆Γ))
   (proj₁ (inline c₄ c₂ (drop Δ⊆Γ)))
    /\ call-match123  (proj₂ (inline c₁ c₂ Δ⊆Γ)) (proj₂ (inline c₃ c₂ Δ⊆Γ))
     (proj₂ (inline c₄ c₂ (drop Δ⊆Γ)))

{-
A partial order to relate
terms with their expansions.
By definition, it preserves
variable calls.
-}
data _expands-to_in´_steps : ∀{Γ τ}{t₁ t₂ : Γ ⊢ τ}
  → τ called-in t₁ → τ called-in t₂ → ℕ → Set where
  ex-refl : ∀{Γ τ}{t : Γ , τ ⊢ τ}{c : τ called-in t}
    → c expands-to c in´ 0 steps

  ex-one : ∀{Γ τ}{t₁ t₂ : Γ , τ ⊢ τ}{c₁ : τ called-in t₁}{c₂ : τ called-in t₂}
    → c₁ expands-to (proj₂ (inline c₁ c₂ ⊆-refl)) in´ 1 steps

  ex-trans : ∀{Γ τ n₁ n₂}{t₁ t₂ t₃ : Γ , τ ⊢ τ}
    {c₁ : τ called-in t₁}{c₂ : τ called-in t₂}{c₃ : τ called-in t₃}
    → c₁ expands-to c₂ in´ n₁ steps
    → c₂ expands-to c₃ in´ n₂ steps
    → c₁ expands-to c₃ in´ n₂ + n₁ steps

{-
Expansion is a repeating inlining
of a term with a original, and thus doesn't
grow super exponentially large.
By definition, it preserves variable calls.
-}
expansion : ∀{Γ τ n}{t : Γ , τ ⊢ τ}(c : τ called-in t)
  → Fuel n
  → ∃ ( λ (t' : Γ , τ ⊢ τ)
   → ∃ ( λ (c' : τ called-in t') → c expands-to c' in´ n steps ) )
expansion {t = t} c (gas 0)
  = t /\ c /\ ex-refl
expansion c (gas 1)
  = proj₁ (inline c c ⊆-refl)
    /\ proj₂ (inline c c ⊆-refl) /\ ex-one
expansion {t = t} c (gas (suc n))
  = proj₁ (inline (proj₁ (proj₂ IH)) c ⊆-refl)
    /\ proj₂ (inline (proj₁ (proj₂ IH)) c ⊆-refl)
    /\ ex-trans (proj₂ (proj₂ IH)) ex-one
  where
    IH = expansion c (gas n)

unroll : ∀{Γ τ n} → Fuel n → Γ ⊩ τ → Γ ⊩ τ
unroll f (rec  t x) = rec (proj₁ (expansion x f)) (proj₁ (proj₂ (expansion x f)))
unroll f (rec∙ t x) = rec∙ (unroll f t) x
