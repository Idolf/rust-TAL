module Util.Dec where

open import Relation.Nullary using (Dec ; yes ; no ; ¬_) public

open import Util.Function
open import Util.Eq
open import Data.Product using (_,_ ; _×_ ; proj₁ ; proj₂)
open import Function using (_∘_)
open import Level

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

-- Some useful helper functions
dec-cong : ∀ {a b} {A : Set a} {B : Set b}
             {x₁ x₂ : A} →
             {f : A → B} → IsInjective f →
             Dec (x₁ ≡ x₂) →
             Dec (f x₁ ≡ f x₂)
dec-cong isInj (yes refl) = yes refl
dec-cong isInj (no ¬eq) = no (¬eq ∘ isInj)

dec-cong₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
              {x₁ x₂ : A} {y₁ y₂ : B} →
              {f : A → B → C} → IsInjective₂ f →
              Dec (x₁ ≡ x₂) → Dec (y₁ ≡ y₂) →
              Dec (f x₁ y₁ ≡ f x₂ y₂)
dec-cong₂ isInj (yes refl) (yes refl) = yes refl
dec-cong₂ isInj (no ¬eq) _ = no (¬eq ∘ proj₁ ∘ isInj)
dec-cong₂ isInj _ (no ¬eq) = no (¬eq ∘ proj₂ ∘ isInj)

dec-inj : ∀ {a b} {A : Set a} {B : Set b}
            {{_ : DecEq B}} →
            {f : A → B} → IsInjective f →
            DecEqFun A
dec-inj {f = f} isInj x₁ x₂ with f x₁ ≟ f x₂
dec-inj {f = f} isInj x₁ x₂ | yes eq = yes (isInj eq)
dec-inj {f = f} isInj x₁ x₂ | no ¬eq = no (¬eq ∘ cong f)

HasInverse-eqFun : ∀ {a b} {A : Set a} {B : Set b}
                     {{_ : DecEq B}} →
                     {f : A → B} →
                     HasInverse f →
                     DecEqFun A
HasInverse-eqFun i = dec-inj (HasInverse→Injective i)
