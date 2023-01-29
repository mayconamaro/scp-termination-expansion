{-# OPTIONS --safe #-}

module Examples.R where

open import Common.Fuel
open import Common.Type using (Type; ℕ´; _⇒_)
import Common.Context as C
open C using (Context; _,_; _∈_; _⊆_; ∈-subs; keep; drop; ⊆-refl; ∅; here; there)
open import R.Syntax.Base
open import R.Syntax.Properties
open import R.Syntax.IR
open import R.Syntax.IR.Properties
open import R.Syntax
open import R.Syntax.Unrolling
open import R.Semantics
open import R.Semantics.Definitional

open import Data.Product using (∃; proj₁; proj₂) renaming (_,_ to _/\_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Sum using (inj₁)

infixl 20 _∙_
_∙_ : ∀{Γ τ₁ τ₂} → Γ ⊢ τ₁ ⇒ τ₂ → Γ ⊢ τ₁ → Γ ⊢ τ₂
_∙_ = app

infixl 20 _∙∙_
_∙∙_ : ∀{Γ τ₁ τ₂} → Γ ⊩ τ₁ ⇒ τ₂ → Γ ⊢ τ₁ → Γ ⊩ τ₂
_∙∙_ = rec∙

#_ : ℕ → ∅ ⊢ ℕ´
# 0 = zero´
# (suc n) = suc´ (# n)

f≢ℕ : ∀{τ₁ τ₂} → τ₁ ⇒ τ₂ ≢ ℕ´
f≢ℕ ()

{- Function that sums naturals -}
sum : ∅ ⊩ ℕ´ ⇒ ℕ´ ⇒ ℕ´
sum = rec {- sum -}
      (abs {- x -}
        (abs {- y -}
          (match (var {- x -} (there here))
{- zero -}  (var {- y -} here)
{- suc w -}   (app
                (app (var {- sum -} (there (there (there here)))) (var {- w -} here)
                )
              (suc´ (var (there here)))
              )
           )
         )
      ) (call-abs (call-abs (call-match3
                              (no-call-var f≢ℕ)
                              (no-call-var f≢ℕ)
                              (call-app1
                                (call-app1 call-var (no-call-var f≢ℕ))
                                (no-call-suc (no-call-var f≢ℕ))))))



1+2 : ∅ ⊩ ℕ´
1+2 = sum ∙∙ suc´ zero´ ∙∙ suc´ (suc´ zero´)

id : ∀{τ} → ∅ ⊢ τ ⇒ τ
id = abs (var here)

loop : ∀{τ} → ∅ ⊩ τ
loop = (rec {- loop -} (var {- loop -} here) call-var) ∙∙ zero´

+1 : ∅ ⊢ ℕ´ ⇒ ℕ´
+1 = abs (suc´ (var here))

2+1 : ∅ ⊢ ℕ´
2+1 = +1 ∙ (suc´ (suc´ zero´))

1+2≡3 : proj₂ (output (⊩-eval (gas 100) 1+2)) ≡ done (v-suc (v-suc (v-suc v-zero)))
1+2≡3 = refl

unr1f-1+2 : unroll (gas 1) 1+2 ≡
  rec∙
  (rec∙
   (rec
    (abs
     (abs
      (match (var (there here)) (var here)
       (app
        (app
         (abs
          (abs
           (match (var (there here)) (var here)
            (app
             (app (var (there (there (there (there (there (there here)))))))
              (var here))
             (suc´ (var (there here)))))))
         (var here))
        (suc´ (var (there here)))))))
    (call-abs
     (call-abs
      (call-match3 (no-call-var f≢ℕ) (no-call-var f≢ℕ)
       (call-app1
        (call-app1
         (call-abs
          (call-abs
           (call-match3 (no-call-var f≢ℕ) (no-call-var f≢ℕ)
            (call-app1 (call-app1 call-var (no-call-var f≢ℕ))
             (no-call-suc (no-call-var f≢ℕ))))))
         (no-call-var f≢ℕ))
        (no-call-suc (no-call-var f≢ℕ)))))))
   (suc´ zero´))
  (suc´ (suc´ zero´))
unr1f-1+2 = refl

_ : ∅-eval (gas 5) 1+2 ≡ inj₁ 3
_ = refl
