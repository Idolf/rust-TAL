module Util.Function where

-- Re-exports
open import Function using (_∘_ ; id) public

-- Local imports
open import Util.Maybe
open import Util.Eq
open import Data.Product using (_×_ ; ∃ ; _,_)
open import Level

-- Some predicates on functions
IsInjective : ∀ {a b} {A : Set a} {B : Set b} → (f : A → B) → Set (a ⊔ b)
IsInjective f = ∀ {x₁ x₂} → f x₁ ≡ f x₂ → x₁ ≡ x₂

IsInjective₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
                 (f : A → B → C) → Set (a ⊔ b ⊔ c)
IsInjective₂ f = ∀ {x₁ x₂ y₁ y₂} → f x₁ y₁ ≡ f x₂ y₂ → x₁ ≡ x₂ × y₁ ≡ y₂

IsInverse : ∀ {a b} {A : Set a} {B : Set b}
              (f : A → B) → (g : B → Maybe A) → Set a
IsInverse f g = ∀ x → g (f x) ≡ just x

HasInverse : ∀ {a b} {A : Set a} {B : Set b} →
            (f : A → B) → Set (a ⊔ b)
HasInverse f = ∃ λ g → IsInverse f g

HasInverse→IsInjective : ∀ {a b} {A : Set a} {B : Set b}
                           {f : A → B} →
                           HasInverse f →
                           IsInjective f
HasInverse→IsInjective {f = f} (g , eq₁) {x₁} {x₂} eq₂ =
  just-injective (
    begin
      just x₁
    ⟨ eq₁ x₁ ⟩≡
      g (f x₁)
    ≡⟨ eq₂ ∥ g ⟩
      g (f x₂)
    ≡⟨ eq₁ x₂ ⟩
      just x₂
    ∎
  )
  where open Eq-Reasoning

IsSurjective : ∀ {a b} {A : Set a} {B : Set b}
                 (f : A → Maybe B) → Set (a ⊔ b)
IsSurjective {A = A} {B} f = ∀ x → ∃ λ y → f y ≡ just x
