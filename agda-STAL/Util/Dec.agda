module Util.Dec where

-- Re-exports
open import Relation.Nullary using (Dec ; yes ; no ; ¬_) public
open import Relation.Nullary.Decidable using (True) public
open import Relation.Binary using (tri< ; tri≈ ; tri> ; Trichotomous) public

-- Local imports
open import Util.Eq
open import Util.Function
open import Data.Product using (proj₁ ; proj₂ ; _×_)

-- A "typeclass" for decidable equality
-- I know there is one in the standard library, but this one is simpler
DecEqFun : ∀ {ℓ} (A : Set ℓ) → Set ℓ
DecEqFun A = (x y : A) → Dec (x ≡ y)

record DecEq {ℓ} (A : Set ℓ) : Set ℓ where
  constructor decEq
  field
    _≟_ : DecEqFun A

-- These two should be equivalent, but they are apparently not
-- then there is only a single field
-- open DecEq {{...}} public
_≟_ : ∀ {ℓ} {A : Set ℓ} {{r : DecEq A}} → DecEqFun A
_≟_ {{eq}} = DecEq._≟_ eq

-- Some useful helper functions
dec-cong : ∀ {a b} {A : Set a} {B : Set b}
             {x₁ x₂} →
             {f : A → B} → IsInjective f →
             Dec (x₁ ≡ x₂) →
             Dec (f x₁ ≡ f x₂)
dec-cong isInj (yes refl) = yes refl
dec-cong isInj (no ¬eq) = no (¬eq ∘ isInj)

dec-cong₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
              {x₁ x₂ y₁ y₂} →
              {f : A → B → C} → IsInjective₂ f →
              Dec (x₁ ≡ x₂) → Dec (y₁ ≡ y₂) →
              Dec (f x₁ y₁ ≡ f x₂ y₂)
dec-cong₂ isInj (yes refl) (yes refl) = yes refl
dec-cong₂ isInj (no ¬eq) _ = no (¬eq ∘ proj₁ ∘ isInj)
dec-cong₂ isInj _ (no ¬eq) = no (¬eq ∘ proj₂ ∘ isInj)

IsInjective→DecEqFun : ∀ {a b} {A : Set a} {B : Set b}
                         {{_ : DecEq B}} →
                         {f : A → B} → IsInjective f →
                         DecEqFun A
IsInjective→DecEqFun {f = f} isInj x₁ x₂ with f x₁ ≟ f x₂
IsInjective→DecEqFun {f = f} isInj x₁ x₂ | yes eq = yes (isInj eq)
IsInjective→DecEqFun {f = f} isInj x₁ x₂ | no ¬eq = no (¬eq ∘ cong f)

HasInverse→DecEqFun : ∀ {a b} {A : Set a} {B : Set b}
                        {{_ : DecEq B}} →
                        {f : A → B} →
                        HasInverse f →
                        DecEqFun A
HasInverse→DecEqFun = IsInjective→DecEqFun ∘ HasInverse→IsInjective

dec-inj : ∀ {a b} {A : Set a} {B : Set b} →
            (f : A → B) → (g : B → A) →
            Dec A → Dec B
dec-inj f g (yes a) = yes (f a)
dec-inj f g (no ¬a) = no (¬a ∘ g)

dec-inj₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
             (f : A → B → C) → (g : C → (A × B)) →
             Dec A → Dec B → Dec C
dec-inj₂ f g (yes a) (yes b) = yes (f a b)
dec-inj₂ f g (no ¬a) _ = no (¬a ∘ proj₁ ∘ g)
dec-inj₂ f g _ (no ¬b) = no (¬b ∘ proj₂ ∘ g)

dec-force : ∀ {a} {A : Set a} →
              (p : Dec A) → {{_ : True p}} →
              A
dec-force (yes p) = p
dec-force (no ¬p) {{()}}
