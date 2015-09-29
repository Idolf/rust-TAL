module Util.Vec where

open import Data.Vec using (Vec ; [] ; _∷_ ; toList) public
open import Data.Vec.Properties using () renaming (∷-injective to Vec-∷-injective) public

open import Util.Eq
open import Util.Nat
open import Util.Dec
open import Level
open import Function

instance
  Vec-dec-eq : ∀ {ℓ} {A : Set ℓ} {m} {{_ : DecEq A}} →
                 DecEq (Vec A m)
  Vec-dec-eq = decEq _==_
    where _==_ : ∀ {ℓ} {A : Set ℓ} {m} {{_ : DecEq A}} → DecEqFun (Vec A m)
          [] == [] = yes refl
          (x₁ ∷ xs₁) == (x₂ ∷ xs₂) = dec-inj₂ Vec-∷-injective (x₁ ≟ x₂) (xs₁ == xs₂)
