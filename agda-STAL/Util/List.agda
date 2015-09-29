module Util.List where

open import Data.List using (List ; [] ; _∷_) public
open import Data.List.All using (All) public
open import Data.List.Properties using () renaming (∷-injective to List-∷-injective) public

open import Util.Dec
open import Util.Eq
open import Util.Nat
open import Function using (id)

instance
  List-dec-eq : ∀ {ℓ} {A : Set ℓ} {{_ : DecEq A}} → DecEq (List A)
  List-dec-eq = decEq _==_
    where _==_ : ∀ {ℓ} {A : Set ℓ} {{_ : DecEq A}} → DecEqFun (List A)
          [] == [] = yes refl
          [] == (x₂ ∷ xs₂) = no (λ ())
          (x₁ ∷ xs₁) == [] = no (λ ())
          (x₁ ∷ xs₁) == (x₂ ∷ xs₂) = dec-inj₂ List-∷-injective (x₁ ≟ x₂) (xs₁ == xs₂)
