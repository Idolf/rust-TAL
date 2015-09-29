module Util.Function where

open import Function using (_∘_ ; id) public

open import Util.Eq
open import Data.Product using (_×_ ; ∃ ; _,_)
open import Level

-- Some predicates on functions
IsInj : ∀ {a b} {A : Set a} {B : Set b} → (f : A → B) → Set (a ⊔ b)
IsInj f = ∀ {x₁ x₂} → f x₁ ≡ f x₂ → x₁ ≡ x₂

IsInj₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
           (f : A → B → C) → Set (a ⊔ b ⊔ c)
IsInj₂ f = ∀ {x₁ x₂ y₁ y₂} → f x₁ y₁ ≡ f x₂ y₂ → x₁ ≡ x₂ × y₁ ≡ y₂

IsInj₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
           (f : A → B → C → D) → Set (a ⊔ b ⊔ c ⊔ d)
IsInj₃ f = ∀ {x₁ x₂ y₁ y₂ z₁ z₂} → f x₁ y₁ z₁ ≡ f x₂ y₂ z₂ → x₁ ≡ x₂ × y₁ ≡ y₂ × z₁ ≡ z₂

IsInj₄ : ∀ {a b c d e} {A : Set a} {B : Set b} {C : Set c}
           {D : Set d} {E : Set e} →
           (f : A → B → C → D → E) → Set (a ⊔ b ⊔ c ⊔ d ⊔ e)
IsInj₄ f = ∀ {x₁ x₂ y₁ y₂ z₁ z₂ q₁ q₂} → f x₁ y₁ z₁ q₁ ≡ f x₂ y₂ z₂ q₂ → x₁ ≡ x₂ × y₁ ≡ y₂ × z₁ ≡ z₂ × q₁ ≡ q₂

IsInverse : ∀ {a b} {A : Set a} {B : Set b}
              (f : A → B) → (g : B → A) → Set a
IsInverse f g = ∀ x → g (f x) ≡ x

Inverse : ∀ {a b} {A : Set a} {B : Set b} →
            (f : A → B) → Set (a ⊔ b)
Inverse f = ∃ λ g → IsInverse f g

Inverse→Inj : ∀ {a b} {A : Set a} {B : Set b}
                {f : A → B} →
                Inverse f →
                IsInj f
Inverse→Inj {f = f} (g , eq₁) {x₁} {x₂} eq₂ =
  begin
    x₁
  ⟨ eq₁ x₁ ⟩≡
    g (f x₁)
  ≡⟨ eq₂ ∥ g ⟩
    g (f x₂)
  ≡⟨ eq₁ x₂ ⟩
    x₂
  ∎
