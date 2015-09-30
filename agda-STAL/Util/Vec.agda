module Util.Vec where

-- Re-exports
open import Data.Vec
  using (Vec ; [] ; _∷_ ; toList ; fromList) renaming (map to Vec-map) public
open import Data.Vec.Properties
  using () renaming (∷-injective to Vec-∷-injective) public

-- Local imports
open import Util.Maybe
open import Util.Eq
open import Util.Function
open import Util.Dec
open import Util.Tree
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Nat using (zero ; suc)
open import Data.List using (List ; map ; [] ; _∷_)

repeat : ∀ {a} {A : Set a} {m} → A → Vec A m
repeat {m = zero}  x = []
repeat {m = suc i} x = x ∷ repeat x

instance
  Vec-Tree : ∀ {ℓ} {A : Set ℓ} {{t : ToTree A}} {m} → ToTree (Vec A m)
  Vec-Tree = tree⋆ (λ { (node _ xs) → from xs })
                   (λ x → node 0 (proj₁ (sur x)) , proj₂ (sur x))
    where from : ∀ {ℓ} {A : Set ℓ} {{t : ToTree A}} {m} →
                   List Tree → ¿ Vec A m
          from {m = zero} [] = Just []
          from {m = zero} (x ∷ xs) = Nothing
          from {m = suc m} [] = Nothing
          from {m = suc m} (x ∷ xs) = _∷_ <$> fromTree x <*> from {m = m} xs
          sur : ∀ {ℓ} {A : Set ℓ} {{t : ToTree A}} {m} →
                  IsSurjective (from {{t}} {m})
          sur [] = [] , refl
          sur (x ∷ xs) = toTree x ∷ proj₁ (sur xs) ,
            _∷_ <$=> invTree x <*=> proj₂ (sur xs)
