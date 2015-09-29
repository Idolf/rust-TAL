module Util.Eq where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; subst ; sym) public

infixr 3 _∎
infixr 2 _≡⟨_⟩_ _⟨_⟩≡_ _≡⟨_∥_⟩_ _⟨_∥_⟩≡_
infixr 1 begin_
_≡⟨_⟩_ : ∀ {a} {A : Set a} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ refl ⟩ refl = refl

_⟨_⟩≡_ : ∀ {a} {A : Set a} (x : A) {y z : A} → y ≡ x → y ≡ z → x ≡ z
x ⟨ refl ⟩≡ refl = refl

_≡⟨_∥_⟩_ : ∀ {a b} {A : Set a} {B : Set b} (x : A) {x' y : B} {z : A} →
             x' ≡ y → (F : B → A) → {{_ : x ≡ F x'}} → F y ≡ z → x ≡ z
_≡⟨_∥_⟩_ x refl f {{x≡Fx'}} refl = x≡Fx'

_⟨_∥_⟩≡_ : ∀ {a b} {A : Set a} {B : Set b} (x : A) {x' y : B} {z : A} →
             y ≡ x' → (F : B → A) → {{_ : x ≡ F x'}} → F y ≡ z → x ≡ z
_⟨_∥_⟩≡_ x refl f {{x≡Fx'}} refl = x≡Fx'

_∎ : ∀ {a} {A : Set a} → (x : A) → x ≡ x
x ∎ = refl

begin_ : ∀ {a} {A : Set a} → {x y : A} → x ≡ y → x ≡ y
begin refl = refl

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
          (f : A → B → C → D) →
          ∀ {x₁ x₂ y₁ y₂ z₁ z₂} →
          x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
cong₃ f refl refl refl = refl

cong₄ : ∀ {a b c d e} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e}
          (f : A → B → C → D → E) →
          ∀ {x₁ x₂ y₁ y₂ z₁ z₂ q₁ q₂} →
          x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → q₁ ≡ q₂ →
          f x₁ y₁ z₁ q₁ ≡ f x₂ y₂ z₂ q₂
cong₄ f refl refl refl refl = refl
