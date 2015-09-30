module Util.Function where

open import Function using (_∘_ ; id) public

open import Util.Eq
open import Util.Maybe
open import Data.Product using (_×_ ; ∃ ; _,_ ; Σ-syntax ; proj₁ ; proj₂)
open import Level

-- Some predicates on functions
IsInjective : ∀ {a b} {A : Set a} {B : Set b} → (f : A → B) → Set (a ⊔ b)
IsInjective f = ∀ {x₁ x₂} → f x₁ ≡ f x₂ → x₁ ≡ x₂

IsInjective₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
                 (f : A → B → C) → Set (a ⊔ b ⊔ c)
IsInjective₂ f = ∀ {x₁ x₂ y₁ y₂} → f x₁ y₁ ≡ f x₂ y₂ → x₁ ≡ x₂ × y₁ ≡ y₂

IsInverse : ∀ {a b} {A : Set a} {B : Set b}
              (f : A → B) → (g : B → ¿ A) → Set a
IsInverse f g = ∀ x → g (f x) ≡ Just x

HasInverse : ∀ {a b} {A : Set a} {B : Set b} →
            (f : A → B) → Set (a ⊔ b)
HasInverse f = ∃ λ g → IsInverse f g

HasInverse→Injective : ∀ {a b} {A : Set a} {B : Set b}
                         {f : A → B} →
                         HasInverse f →
                         IsInjective f
HasInverse→Injective {f = f} (g , eq₁) {x₁} {x₂} eq₂ =
  Just-injective (
    begin
      Just x₁
    ⟨ eq₁ x₁ ⟩≡
      g (f x₁)
    ≡⟨ eq₂ ∥ g ⟩
      g (f x₂)
    ≡⟨ eq₁ x₂ ⟩
      Just x₂
    ∎
  )

IsSurjective : ∀ {a b} {A : Set a} {B : Set b}
                 (f : A → ¿ B) → Set (a ⊔ b)
IsSurjective {A = A} {B} f = ∀ x → ∃ λ y → f y ≡ Just x
