{-# OPTIONS --safe #-}

module Examples.Translation where

open import Common.Fuel
open import Common.Context
open import Common.Type
open import Transform.Translation
open import Examples.R
open import R.Syntax
open import L.Syntax
open import L.Semantics
open import L.Semantics.Definitional

open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; suc)
open import Data.Sum using (inj₁)

-- This is term expected when transforming term `1+2` from Examples.R
-- with gas 3. Notice l-term has an additional app, because of closure.
l-term : ∅ ⊪ ℕ´
l-term = app
          (app
           (app
            (abs
             (abs
              (abs
               (match (var (there here)) (var here)
                (app
                 (app
                  (abs
                   (abs
                    (match (var (there here)) (var here)
                     (app
                      (app
                       (abs
                        (abs
                         (match (var (there here)) (var here)
                          (app
                           (app
                            (abs
                             (abs
                              (match (var (there here)) (var here)
                               (app (app error (var here)) (suc´ (var (there here)))))))
                            (var here))
                           (suc´ (var (there here)))))))
                       (var here))
                      (suc´ (var (there here)))))))
                  (var here))
                 (suc´ (var (there here))))))))
            (abs {τ₁ = ℕ´} (abs {τ₁ = ℕ´} zero´)))
           (suc´ zero´))
          (suc´ (suc´ zero´))

-- The result of transformation
tr-term : ∅ ⊪ ℕ´
tr-term = transform (gas 3) 1+2

-- It is as expected
_ : tr-term ≡ l-term
_ = refl

-- The evalation of the closure yields the expected result
_ : proj₁ (output (⊪-eval (gas 100) tr-term)) ≡ suc´ (suc´ (suc´ zero´))
_ = refl
