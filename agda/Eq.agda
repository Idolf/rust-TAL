open import Relation.Binary.Core using (_≡_ ; Decidable ; refl)
open import Relation.Nullary using (Dec)
open import Level
import Data.Nat as N

DecidableEq : ∀ {a} → Set a → Set a
DecidableEq A = Decidable {A = A} _≡_

record Eq {a} (A : Set a) : Set a where
  infix 4 _≟_
  field
    _≟_ : DecidableEq A

open Eq {{...}} public

instance
  ℕ-Eq : Eq N.ℕ
  ℕ-Eq = record { _≟_ = N._≟_ }

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

cong₃ : ∀ {A B C D : Set}
          {a₁ a₂ : A} {b₁ b₂ : B} {c₁ c₂ : C}
          (F : A → B → C → D) →
          a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ →
          F a₁ b₁ c₁ ≡ F a₂ b₂ c₂
cong₃ _ refl refl refl = refl

cong₄ : ∀ {A B C D E : Set}
          {a₁ a₂ : A} {b₁ b₂ : B} {c₁ c₂ : C} {d₁ d₂ : D}
          (F : A → B → C → D → E) →
          a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → d₁ ≡ d₂ →
          F a₁ b₁ c₁ d₁ ≡ F a₂ b₂ c₂ d₂
cong₄ _ refl refl refl refl = refl
