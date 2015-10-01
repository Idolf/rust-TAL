module Util.Eq where

-- Re-exports
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; cong ; cong₂ ; subst ; sym ; trans) public

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
