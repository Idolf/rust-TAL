module Util.List where

-- Re-exports
open import Data.List
  using (List ; [] ; _∷_ ; [_] ; map ; length ; zip ; _++_) public
open import Data.List.All
  using (All ; [] ; _∷_) renaming (map to All-map) public
open import Data.List.Properties using ()
  renaming (∷-injective to List-∷-injective) public

-- Local imports
open import Util.Maybe
open import Util.Eq
open import Util.Function
open import Util.Tree
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_,_ ; proj₁ ; proj₂ ; _×_)

infix 4 _↓_⇒_
data _↓_⇒_ {ℓ} {A : Set ℓ} : (xs : List A) → ℕ → A → Set ℓ where
  here  : ∀ {x xs} →
            x ∷ xs ↓ zero ⇒ x
  there : ∀ {x r xs i} →
            xs ↓ i ⇒ r →
            x ∷ xs ↓ suc i ⇒ r


All-zip : ∀ {a p} {A : Set a} {P : A × A → Set p} {L : List A} →
            All (λ x → P (x , x)) L →
            All P (zip L L)
All-zip [] = []
All-zip (p ∷ ps) = p ∷ All-zip ps

All-unzip : ∀ {a p} {A : Set a} {P : A × A → Set p} {L : List A} →
              All P (zip L L) →
              All (λ x → P (x , x)) L
All-unzip {L = []} [] = []
All-unzip {L = x ∷ L} (p ∷ ps) = p ∷ All-unzip ps

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
