{-# OPTIONS --safe #-}

module L.Semantics.Normalization where

open import Common.Type using (Type; ℕ´; _⇒_)
open import Common.Context using (Context; _,_; _∈_; here; there; ∅; _⊆_; ⊆-refl; ⊆-wk)
open import L.Syntax
open import L.Syntax.Properties
open import L.Semantics

open import Data.Product using (∃; ∄; proj₁; proj₂; _×_) renaming (_,_ to _/\_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_; id)
{-
Tait's Normalization Proof as seen in Pierce (2002) and
https://github.com/gergoerdi/syntactic-stlc/blob/master/STLC/Norm.agda
-}

{-
   The —→ and —↠ are defined in L.Semantics and
   they follow PLFA with additional rules for error.
   Definition of Value and NormalForm are also on L.Semantics.
   The syntax of System L is in L.Syntax
   Substitution Lemma (following PLFA) for System L is in L.Syntax.Properties
-}

-- A term halts if there is a normal form to which it evaluates
data Halts : ∀{Γ τ} → Γ ⊪ τ → Set where
  halts : ∀{Γ τ}{t t' : Γ ⊪ τ} → NormalForm t' → t —↠ t' → Halts t

-- Trivially, normal forms halts
nf-halts : ∀{Γ τ}{t : Γ ⊪ τ} → NormalForm t → Halts t
nf-halts {t = t}      (value x) = halts (value x) (t ∎)
nf-halts {t = .error}  nf-err   = halts nf-err (error ∎)

-- This is the defitinion of NormalForm used on georgi's repo
-- NF : ∀ {a b} {A : Set a} → Rel A b → A → Set _
-- NF next x = ∄ (next x)

-- NormalForms do not reduce (Following PLFA). Needed for proving determinism
nf-¬-—→ : ∀{Γ τ t}{t' : Γ ⊪ τ} → NormalForm {Γ} {τ} t → ¬ (t —→ t')
nf-¬-—→ (value v-zero) ()
nf-¬-—→ (value v-abs)  ()
nf-¬-—→  nf-err        ()
nf-¬-—→ (value (v-suc x)) (ξ-suc y) = nf-¬-—→ (value x) y

-- The evaluation relation is deterministic. This is needed to prove halt preservation
deterministic : ∀{Γ τ}{t₁ t₂ t₃ : Γ ⊪ τ} → t₁ —→ t₂ → t₁ —→ t₃ → t₂ ≡ t₃
deterministic (ξ-1 x) (ξ-1 y) rewrite deterministic x y = refl
deterministic (ξ-1 x) (ξ-2 x₁ y)     = ⊥-elim (nf-¬-—→ (value x₁) x)
deterministic (ξ-1 x) (β-err3 x₁)    = ⊥-elim (nf-¬-—→ (value x₁) x)
deterministic (ξ-2 x x₁) (ξ-1 y)     = ⊥-elim (nf-¬-—→ (value x) y)
deterministic (ξ-2 x x₁) (ξ-2 x₂ y) rewrite deterministic x₁ y = refl
deterministic (ξ-2 x x₁) (β-abs x₂)  = ⊥-elim (nf-¬-—→ (value x₂) x₁)
deterministic (β-abs x) (ξ-2 x₁ y)   = ⊥-elim (nf-¬-—→ (value x) y)
deterministic (β-abs x) (β-abs x₁)   = refl
deterministic (ξ-suc x) (ξ-suc y) rewrite deterministic x y = refl
deterministic (ξ-mtc x) (ξ-mtc y) rewrite deterministic x y = refl
deterministic (ξ-mtc x) (β-suc x₁)   = ⊥-elim (nf-¬-—→ (value (v-suc x₁)) x)
deterministic β-zero β-zero          = refl
deterministic (β-suc x) (ξ-mtc y)    = ⊥-elim (nf-¬-—→ (value (v-suc x)) y)
deterministic (β-suc x) (β-suc x₁)   = refl
deterministic β-err1 β-err1          = refl
deterministic β-err2 β-err2          = refl
deterministic (β-err3 x) (ξ-1 y)     = ⊥-elim (nf-¬-—→ (value x) y)
deterministic (β-err3 x) (β-err3 x₁) = refl
deterministic β-err4 β-err4          = refl

{-
This definition of Saturated is from georgi's repo.
-}
mutual
  Saturated : ∀{τ} → ∅ ⊪ τ → Set
  Saturated t = Halts t × Saturated' _ t

  Saturated' : ∀(τ : Type) → ∅ ⊪ τ → Set
  Saturated' (τ₁ ⇒ τ₂) f   = ∀{e} → Saturated e → Saturated (app f e)
  Saturated'  ℕ´        _  = ⊤


-- not strictly positive
-- data Saturated : ∀{τ} → ∅ ⊪ τ → Set where
--   s-nat : ∀{t : ∅ ⊪ ℕ´} → Saturated' ℕ´ t
--   s-fun : ∀{τ₁ τ₂}{t : ∅ ⊪ τ₁ ⇒ τ₂} → ∀{e} → Saturated e → Saturated' (τ₂) (app t e)

-- A saturated term halts. Trivial, it is part of the definition.
sat-halts : ∀ {τ}{t : ∅ ⊪ τ} → Saturated t → Halts t
sat-halts = proj₁

-- My own definition for biconditional
infix 0 _↔_
record _↔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
open _↔_

-- The evaluation relation preserves halting (-->)
—→-halts-→ : ∀{τ}{t t' : ∅ ⊪ τ} → t —→ t' → Halts t → Halts t'
—→-halts-→ {t = t} x (halts nf (_ ∎)) = ⊥-elim (nf-¬-—→ nf x)
—→-halts-→ {t = t} x (halts nf (t —→⟨ x₂ ⟩ y)) rewrite deterministic x x₂
  = halts nf y

-- The evaluation relation preserves halting (<--)
—→-halts-← : ∀{τ}{t t' : ∅ ⊪ τ} → t —→ t' → Halts t' → Halts t
—→-halts-← {t = t} x (halts nf y) = halts nf (t —→⟨ x ⟩ y)

-- The evaluation relation preserves halting (<-->)
—→-halts : ∀{τ}{t t' : ∅ ⊪ τ} → t —→ t' → Halts t ↔ Halts t'
—→-halts x = record {to = —→-halts-→ x; from = —→-halts-← x}

-- The evaluation relation preserves saturation (-->)
—→-saturated-→ : ∀{τ}{t t' : ∅ ⊪ τ} → t —→ t' → Saturated t → Saturated t'
—→-saturated-→ {ℕ´}      x (h /\ _)  = (—→-halts-→ x h) /\ tt
—→-saturated-→ {τ₁ ⇒ τ₂} x (h /\ s)  = (—→-halts-→ x h) /\ λ e → —→-saturated-→ (ξ-1 x) (s e)

-- The evaluation relation preserves saturation (<--)
—→-saturated-← : ∀{τ}{t t' : ∅ ⊪ τ} → t —→ t' → Saturated t' → Saturated t
—→-saturated-← {ℕ´}      x (h /\ _)  = (—→-halts-← x h) /\ tt
—→-saturated-← {τ₁ ⇒ τ₂} x (h /\ s)  = (—→-halts-← x h) /\ λ e → —→-saturated-← (ξ-1 x) (s e)

-- The evaluation relation preserves saturation (<-->)
—→-saturated : ∀{τ}{t t' : ∅ ⊪ τ} → t —→ t' → Saturated t ↔ Saturated t'
—→-saturated x = record {to = —→-saturated-→ x; from = —→-saturated-← x}

-- The refl and trans closure also preserves saturation (-->)
—↠-saturated-→ : ∀{τ}{t t' : _ ⊪ τ} → t —↠ t' → Saturated t → Saturated t'
—↠-saturated-→ (_ ∎)          = id
—↠-saturated-→ (_ —→⟨ x ⟩ x₁) = —↠-saturated-→ x₁ ∘ —→-saturated-→ x

-- The refl and trans closure also preserves saturation (<--)
—↠-saturated-← : ∀{τ}{t t' : _ ⊪ τ} → t —↠ t' → Saturated t' → Saturated t
—↠-saturated-← (_ ∎)          = id
—↠-saturated-← (Z —→⟨ x ⟩ x₁) st with —↠-saturated-← x₁ st
...| k with —→-saturated-← x k
...   | q = q

-- The refl and trans closure also preserves saturation (<-->)
—↠-saturated : ∀{τ}{t t' : ∅ ⊪ τ} → t —↠ t' → Saturated t ↔ Saturated t'
—↠-saturated x = record { to = —↠-saturated-→ x ; from = —↠-saturated-← x}

-- A relation from Georgo which seems to store types of terms that are
-- typable in some context
data _⊢⋆_ (Γ : Context) : Context → Set where
  ∅´   : Γ ⊢⋆ ∅
  _,,_ : ∀ {τ Δ} → Γ ⊢⋆ Δ → Γ ⊪ τ → Γ ⊢⋆ (Δ , τ)

-- Already have these on L.Syntax.Properties as lemma for substitution
-- but this one uses this datatype
sub-var : ∀{Γ Δ τ} → Γ ⊢⋆ Δ → τ ∈ Δ → Γ ⊪ τ
sub-var (σ ,, τ) here      = τ
sub-var (σ ,, τ) (there e) = sub-var σ e

⊆-⊢⋆ : ∀{Γ₁ Γ₂ Δ} → Γ₁ ⊆ Γ₂ → Γ₁ ⊢⋆ Δ → Γ₂ ⊢⋆ Δ
⊆-⊢⋆ ope ∅´        = ∅´
⊆-⊢⋆ ope (x ,, x₁) = ⊆-⊢⋆ ope x ,, ⊆-subs ope x₁

shift : ∀ {τ Γ Δ} → Γ ⊢⋆ Δ → (Γ , τ) ⊢⋆ (Δ , τ)
shift σ = ⊆-⊢⋆ ⊆-wk σ ,, var here

⊢⋆-refl : ∀{Γ} → Γ ⊢⋆ Γ
⊢⋆-refl {∅}     = ∅´
⊢⋆-refl {Γ , x} = shift ⊢⋆-refl

-- substitution using above mentioned relation
sub : ∀ {Γ Δ τ} → Γ ⊢⋆ Δ → Δ ⊪ τ → Γ ⊪ τ
sub σ (var x)         = sub-var σ x
sub σ (abs t)         = abs (sub (shift σ) t)
sub σ (app f t)       = app (sub σ f) (sub σ t)
sub σ zero´           = zero´
sub σ (suc´ t)        = suc´ (sub σ t)
sub σ (match t t₁ t₂) = match (sub σ t) (sub σ t₁) (sub (shift σ) t₂)
sub σ error           = error

-- sub-refl : ∀{Γ τ}(t : Γ ⊪ τ) → sub ⊢⋆-refl t ≡ t
-- sub-refl t = {!   !}

⊢⋆-trans : ∀{Γ₁ Γ₂ Δ} → Γ₁ ⊢⋆ Γ₂ → Γ₂ ⊢⋆ Δ → Γ₁ ⊢⋆ Δ
⊢⋆-trans _ ∅´ = ∅´
⊢⋆-trans Γ⊢⋆Γ (Γ⊢⋆Δ ,, t) = ⊢⋆-trans Γ⊢⋆Γ Γ⊢⋆Δ ,, sub Γ⊢⋆Γ t

-- An environment of saturated-value terms
data Instantiation : ∀ {Γ} → ∅ ⊢⋆ Γ → Set where
  ∅´   : Instantiation ∅´
  _,,_ : ∀ {Γ t σ}
    → Instantiation {Γ} σ
    → ∀ {e} → Value {_} {t} e × Saturated e → Instantiation (σ ,, e)

-- saturation of variables
saturate-var : ∀ {Γ σ} → Instantiation σ → ∀ {τ} (x : τ ∈ Γ) → Saturated (sub-var σ x)
saturate-var (_ ,, (_ /\ sat)) here     = sat
saturate-var (env ,, _)       (there e) = saturate-var env e

-- -- applications result in substitution
-- —↠-sub-app : ∀ {Γ τ} {t₁ t₂ : Γ ⊪ τ}
--   → t₁ —↠ t₂
--   → Value t₂
--   → ∀ {t} (f : _ ⊪ t) → app (abs {τ₁ = τ} f) t₁ —↠ sub (⊢⋆-refl ,, t₂) f
-- —↠-sub-app t₁—↠t₂ v f = {!   !}
--
-- -- As Gergo puts it:
-- -- "It basically states that you can push in outer arguments before the innermost one.
-- -- Should this be called some kind of constant propagation?"
-- innermost-last : ∀ {Γ τ} (σ : ∅ ⊢⋆ Γ) (t : ∅ ⊪ τ) → ⊢⋆-trans (∅ ,, t) (⊆-⊢⋆ ⊆-wk σ) ≡ σ
-- innermost-last  ∅       t = refl
-- innermost-last (σ , t') t
--   rewrite innermost-last σ t | sym (sub-⊢⋆⊇ (∅ , t) ⊆-wk e) | sub-refl t' = refl
