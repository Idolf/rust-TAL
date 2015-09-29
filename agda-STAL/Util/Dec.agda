module Util.Dec where

open import Relation.Binary.PropositionalEquality as P using (_≡_ ; _≢_ ; refl) public
open import Relation.Nullary using (Dec ; yes ; no) public

open import Data.Product using (_,_ ; _×_ ; proj₁ ; proj₂)

open import Function using (_∘_)

-- Some useful helper functions
dec-inj : ∀ {a b} {A : Set a} {B : Set b}
            {x₁ x₂ : A} →
            {f : A → B} →
            (f x₁ ≡ f x₂ → x₁ ≡ x₂) →
            Dec (x₁ ≡ x₂) →
            Dec (f x₁ ≡ f x₂)
dec-inj inj (yes refl) = yes refl
dec-inj inj (no ¬eq) = no (¬eq ∘ inj)

dec-inj₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
             {x₁ x₂ : A} {y₁ y₂ : B} →
             {f : A → B → C} →
             (f x₁ y₁ ≡ f x₂ y₂ → x₁ ≡ x₂ × y₁ ≡ y₂) →
             Dec (x₁ ≡ x₂) → Dec (y₁ ≡ y₂) →
             Dec (f x₁ y₁ ≡ f x₂ y₂)
dec-inj₂ inj (yes refl) (yes refl) = yes refl
dec-inj₂ inj (no ¬eq) _ = no (¬eq ∘ proj₁ ∘ inj)
dec-inj₂ inj _ (no ¬eq) = no (¬eq ∘ proj₂ ∘ inj)

dec-inj₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
             {x₁ x₂ : A} {y₁ y₂ : B} {z₁ z₂ : C} →
             {f : A → B → C → D} →
             (f x₁ y₁ z₁ ≡ f x₂ y₂ z₂ → x₁ ≡ x₂ × y₁ ≡ y₂ × z₁ ≡ z₂) →
             Dec (x₁ ≡ x₂) → Dec (y₁ ≡ y₂) → Dec (z₁ ≡ z₂) → Dec (f x₁ y₁ z₁ ≡ f x₂ y₂ z₂)
dec-inj₃ inj (yes refl) (yes refl) (yes refl) = yes refl
dec-inj₃ inj (no ¬eq) _ _ = no (¬eq ∘ proj₁ ∘ inj)
dec-inj₃ inj _ (no ¬eq) _ = no (¬eq ∘ proj₁ ∘ proj₂ ∘ inj)
dec-inj₃ inj _ _ (no ¬eq) = no (¬eq ∘ proj₂ ∘ proj₂ ∘ inj)

dec-inj₄ : ∀ {a b c d e} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e}
             {x₁ x₂ : A} {y₁ y₂ : B} {z₁ z₂ : C} {q₁ q₂ : D} →
             {f : A → B → C → D → E} →
             (f x₁ y₁ z₁ q₁ ≡ f x₂ y₂ z₂ q₂ → x₁ ≡ x₂ × y₁ ≡ y₂ × z₁ ≡ z₂ × q₁ ≡ q₂) →
             Dec (x₁ ≡ x₂) → Dec (y₁ ≡ y₂) → Dec (z₁ ≡ z₂) → Dec (q₁ ≡ q₂) →
             Dec (f x₁ y₁ z₁ q₁ ≡ f x₂ y₂ z₂ q₂)
dec-inj₄ inj (yes refl) (yes refl) (yes refl) (yes refl) = yes refl
dec-inj₄ inj (no ¬eq) _ _ _ = no (¬eq ∘ proj₁ ∘ inj)
dec-inj₄ inj _ (no ¬eq) _ _ = no (¬eq ∘ proj₁ ∘ proj₂ ∘ inj)
dec-inj₄ inj _ _ (no ¬eq) _ = no (¬eq ∘ proj₁ ∘ proj₂ ∘ proj₂ ∘ inj)
dec-inj₄ inj _ _ _ (no ¬eq) = no (¬eq ∘ proj₂ ∘ proj₂ ∘ proj₂ ∘ inj)

-- Some "typeclasses"
DecEqFun : ∀ {ℓ} (A : Set ℓ) → Set ℓ
DecEqFun A = (x y : A) → Dec (x ≡ y)

record DecEq {ℓ} (A : Set ℓ) : Set ℓ where
  constructor decEq
  field
    _≟_ : DecEqFun A

-- These two should be equivalent, but they are apparently not
-- open DecEq {{...}} public
_≟_ : ∀ {ℓ} {A : Set ℓ} {{r : DecEq A}} → DecEqFun A
_≟_ {{eq}} = DecEq._≟_ eq
