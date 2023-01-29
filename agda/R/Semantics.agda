{-# OPTIONS --safe #-}

module R.Semantics where

open import Common.Type
open import Common.Context
open import Common.Fuel
open import R.Syntax.Properties
open import R.Syntax.IR
open import R.Syntax.IR.Properties
open import R.Syntax

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃; proj₁; proj₂) renaming (_,_ to _/\_)

data Value : ∀{Γ τ } → Γ ⊢´ τ → Set where
  v-zero : ∀{Γ}
    → Value (zero´ {Γ})

  v-suc : ∀{Γ}{t : Γ ⊢´ ℕ´}
    → Value t
    --------------
    → Value (suc´ t)

  v-abs : ∀{Γ τ₁ τ₂}{t : Γ , τ₁ ⊢´ τ₂}
    → Value (abs t)

infix 8 _—→_
data _—→_ : ∀ {Γ τ} → (Γ ⊢´ τ) → (Γ ⊢´ τ) → Set where
  ξ-1 : ∀{Γ τ₁ τ₂}{t₁ t₃ : Γ ⊢´ τ₁ ⇒ τ₂}{t₂ : Γ ⊢´ τ₁}
    → t₁ —→ t₃
      ----------------------
    → app t₁ t₂ —→ app t₃ t₂

  ξ-2 : ∀{Γ τ₁ τ₂}{t₁ : Γ ⊢´ τ₁ ⇒ τ₂}{t₂ t₃ : Γ ⊢´ τ₁}
    → Value t₁
    → t₂ —→ t₃
    ----------------
    → app t₁ t₂ —→ app t₁ t₃

  β-abs : ∀{Γ τ₁ τ₂}{t₁ : Γ , τ₁ ⊢´ τ₂}{t₂ : Γ ⊢´ τ₁}
    → Value t₂
    → app (abs t₁) t₂ —→ subs-lemma t₁ t₂

  ξ-suc : ∀{Γ}{t₁ t₂ : Γ ⊢´ ℕ´}
    → t₁ —→ t₂
    → suc´ t₁ —→ suc´ t₂

  ξ-mtc : ∀{Γ τ}{t₁ t₂ : Γ ⊢´ ℕ´}{t₃ : Γ ⊢´ τ}{t₄ : Γ , ℕ´ ⊢´ τ}
    → t₁ —→ t₂
    → match t₁ t₃ t₄ —→ match t₂ t₃ t₄

  β-zero : ∀{Γ τ}{t₁ : Γ ⊢´ τ}{t₂ : Γ , ℕ´ ⊢´ τ}
    → match zero´ t₁ t₂ —→ t₁

  β-suc : ∀{Γ τ}{t₁ : Γ ⊢´ ℕ´}{t₂ : Γ ⊢´ τ}{t₃ : Γ , ℕ´ ⊢´ τ}
    → Value t₁
    → match (suc´ t₁) t₂ t₃ —→ subs-lemma t₃ t₁

  β-rec : ∀{Γ τ}{t : Γ , τ ⊢´ τ}
    → rec t —→ subs-lemma t (rec t)

infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎
data _—↠_ {Γ τ} : (Γ ⊢´ τ) → (Γ ⊢´ τ) → Set where
  _∎ : (t : Γ ⊢´ τ)
      ------
    → t —↠ t

  _—→⟨_⟩_ : (t : Γ ⊢´ τ) {t₁ t₂ : Γ ⊢´ τ}
    → t  —→ t₁
    → t₁ —↠ t₂
      ------
    → t  —↠ t₂

begin_ : ∀ {Γ τ} {t₁ t₂ : Γ ⊢´ τ}
  → t₁ —↠ t₂
    ------
  → t₁ —↠ t₂
begin t = t

data Progress {A} (t₁ : ∅ ⊢´ A) : Set where
  step : ∀ {t₂ : ∅ ⊢´ A}
    → t₁ —→ t₂
      ----------
    → Progress t₁

  done :
      Value t₁
      ----------
    → Progress t₁

progress : ∀ {A} → (M : ∅ ⊢´ A) → Progress M
progress (var ())
progress (abs N)                        =  done v-abs
progress (app L M) with progress L
...    | step L—→L′                     =  step (ξ-1 L—→L′)
...    | done v-abs with progress M
...        | step M—→M′                 =  step (ξ-2 v-abs M—→M′)
...        | done VM                    =  step (β-abs VM)
progress (zero´)                        =  done v-zero
progress (suc´ M) with progress M
...    | step M—→M′                     =  step (ξ-suc M—→M′)
...    | done VM                        =  done (v-suc VM)
progress (match L M N) with progress L
...    | step L—→L′                     =  step (ξ-mtc L—→L′)
...    | done v-zero                    =  step (β-zero)
...    | done (v-suc VL)                =  step (β-suc VL)
progress (rec L)                        =  step (β-rec)

data Finished {Γ A} (N : Γ ⊢´ A) : Set where
  done :
     Value N
     ----------
   → Finished N

  out-of-gas :
     ----------
     Finished N

data Steps {A} : ∅ ⊢´ A → Set where

  steps : {L N : ∅ ⊢´ A}
   → L —↠ N
   → Finished N
     ----------
   → Steps L

eval1 : ∀ {A n}
 → Fuel n
 → (L : ∅ ⊢´ A)
   -----------
 → Steps L
eval1 (gas zero)    L                    =  steps (L ∎) out-of-gas
eval1 (gas (suc m)) L with progress L
... | done VL                            =  steps (L ∎) (done VL)
... | step {M} L—→M with eval1 (gas m) M
...    | steps M—↠N fin                  =  steps (L —→⟨ L—→M ⟩ M—↠N) fin

⊩-eval : ∀ {τ n} → Fuel n → (t : ∅ ⊩ τ) → Steps (⊩-to-IR t)
⊩-eval f t = eval1 f (⊩-to-IR t)

output : ∀{τ}{t₁ : ∅ ⊢´ τ} → Steps t₁ → ∃ (λ t₂ → Finished t₂)
output (steps {L} {N} x y) = N /\ y
