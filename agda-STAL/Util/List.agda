module Util.List where

-- Re-exports
open import Data.List using (List ; [] ; _∷_ ; [_] ; map ; length) public
open import Data.List.All using (All) public
open import Data.List.Properties using ()
  renaming (∷-injective to List-∷-injective) public

-- Local imports
open import Util.Maybe
open import Util.Eq
open import Util.Function
open import Util.Tree
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_,_ ; proj₁ ; proj₂)

infix 4 _↓ₗ_⇒_
data _↓ₗ_⇒_ {ℓ} {A : Set ℓ} : (xs : List A) → ℕ → A → Set ℓ where
  here  : ∀ {x xs} →
            x ∷ xs ↓ₗ zero ⇒ x
  there : ∀ {x r xs i} →
            xs ↓ₗ i ⇒ r →
            x ∷ xs ↓ₗ suc i ⇒ r

instance
  List-Tree : ∀ {ℓ} {A : Set ℓ} {{t : ToTree A}} → ToTree (List A)
  List-Tree = tree⋆ (λ { (node _ xs) → from xs })
                    (λ x → node 0 (proj₁ (sur x)) , proj₂ (sur x))
    where from : ∀ {ℓ} {A : Set ℓ} {{t : ToTree A}} → List Tree → ¿ List A
          from [] = Just []
          from (x ∷ xs) = _∷_ <$> fromTree x <*> from xs
          sur : ∀ {ℓ} {A : Set ℓ} {{t : ToTree A}} → IsSurjective (from {{t}})
          sur [] = [] , refl
          sur (x ∷ xs) = toTree x ∷ proj₁ (sur xs) ,
            _∷_ <$=> invTree x <*=> proj₂ (sur xs)
