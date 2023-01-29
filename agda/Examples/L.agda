{-# OPTIONS --safe #-}

module Examples.L where

open import Common.Fuel using (Fuel; gas)
open import Common.Type using (Type; ℕ´; _⇒_)
open import Common.Context using (Context; _,_; _∈_; here; there; ∅)
open import L.Syntax
open import L.Syntax.Properties
open import L.Semantics
open import L.Semantics.Definitional

-- open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃; ∄; proj₁; proj₂) renaming (_,_ to _/\_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Sum using (inj₁)
-- open import Relation.Binary using (Rel)
-- open import Relation.Nullary using (¬_)
-- open import Data.Empty using (⊥-elim)

sum1f : ∅ ⊪ ℕ´ ⇒ ℕ´ ⇒ ℕ´
sum1f = abs {- x -}(abs {- y -}
         (match {- x = 0 or suc w -}
           (var {- x -} (there here))
           (var {- y -}here)
           (app
             (app (abs {- x1 -}(abs {- y1 -}
                     (match {- x1 = 0 or suc w1 -}
                       (var {- x1 -} (there here))
                       (var {- y1 -}here)
                       (app
                         (app error (var {- w1 -} here) )
                         (suc´ (var {- y1 -}(there here)))))))
                 (var {- w -} here) )
             (suc´ (var {- y -}(there here))))))

1+1 : ∅ ⊪ ℕ´
1+1 = app (app sum1f (suc´ zero´)) (suc´ zero´)

1+1≡2 : proj₁ (output (⊪-eval (gas 100) 1+1)) ≡ suc´ (suc´ zero´)
1+1≡2 = refl

4+1 : ∅ ⊪ ℕ´
4+1 = app (app sum1f (suc´ (suc´ (suc´ (suc´ zero´))))) (suc´ zero´)

4+1≡err : proj₁ (output (⊪-eval (gas 100) 4+1)) ≡ error
4+1≡err = refl

_ : ∅-eval 1+1 ≡ inj₁ 2
_ = refl
