module Util.Product where

open import Data.Product using (_×_ ; _,_ ; Σ-syntax ; proj₁ ; proj₂ ; <_,_>) renaming (map to ×-map) public
open import Util.Eq
open import Util.Dec


×-,-injective : ∀ {a b} {A : Set a} {B : Set b} →
                        {x₁ x₂ : A} {y₁ y₂ : B} →
                        x₁ , y₁ ≡ x₂ , y₂ → x₁ ≡ x₂ × y₁ ≡ y₂
×-,-injective refl = refl , refl

×-assoc→ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
             (A × B) × C → A × B × C
×-assoc→ ((a , b) , c) = a , b , c

×-assoc← : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
             A × B × C → (A × B) × C
×-assoc← (a , b , c) = (a , b) , c

instance
  Product-dec-eq : ∀ {a b} {A : Set a} {B : Set b} →
                     {{_ : DecEq A}} {{_ : DecEq B}} →
                     DecEq (A × B)
  Product-dec-eq = decEq (λ { (a₁ , b₁) (a₂ , b₂) → dec-inj₂ ×-,-injective (a₁ ≟ a₂) (b₁ ≟ b₂) })
