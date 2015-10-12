module Util.Eq where

-- Re-exports
open import Relation.Binary.PropositionalEquality
  using ( _≡_ ; _≢_ ; refl ; cong ; cong₂
        ; subst ; subst₂ ; sym ; trans) public

module Eq-Reasoning where
  infixr 3 _∎
  infix 3 _∥_ _∣_∥_
  infixr 2 _≡⟨_⟩_ _⟨_⟩≡_
  infixr 1 begin_
  _≡⟨_⟩_ : ∀ {a} {A : Set a} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ refl ⟩ refl = refl

  _⟨_⟩≡_ : ∀ {a} {A : Set a} (x : A) {y z : A} → y ≡ x → y ≡ z → x ≡ z
  x ⟨ refl ⟩≡ refl = refl

  _∥_ : ∀ {a b} {A : Set a} {B : Set b}
          {x₁ x₂} →
          x₁ ≡ x₂ →
          (f : A → B) →
          f x₁ ≡ f x₂
  refl ∥ f = refl

  _∣_∥_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
           {x₁ x₂ y₁ y₂} →
           x₁ ≡ x₂ →
           y₁ ≡ y₂ →
           (f : A → B → C) →
           f x₁ y₁ ≡ f x₂ y₂
  refl ∣ refl ∥ f = refl

  _∎ : ∀ {a} {A : Set a} → (x : A) → x ≡ x
  x ∎ = refl

  begin_ : ∀ {a} {A : Set a} → {x y : A} → x ≡ y → x ≡ y
  begin refl = refl
