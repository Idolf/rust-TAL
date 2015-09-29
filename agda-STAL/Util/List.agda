module Util.List where

open import Data.List using (List ; [] ; _∷_ ; [_] ; map ; length) public
open import Data.List.All using (All) public
open import Data.List.Properties using () renaming (∷-injective to List-∷-injective) public

open import Util.Tree
open import Util.Function
open import Util.Eq
open import Util.Nat
open import Data.Product using (_,_)
open import Function using (id)

infix 4 _↓ₗ_⇒_
data _↓ₗ_⇒_ {ℓ} {A : Set ℓ} : (xs : List A) → ℕ → A → Set ℓ where
  here  : ∀ {x xs} →
            x ∷ xs ↓ₗ zero ⇒ x
  there : ∀ {x r xs i} →
            xs ↓ₗ i ⇒ r →
            x ∷ xs ↓ₗ suc i ⇒ r

instance
  List-Tree : ∀ {ℓ} {A : Set ℓ} {{_ : ToTree A}} → ToTree (List A)
  List-Tree = tree to from eq
    where to : ∀ {ℓ} {A : Set ℓ} {{_ : ToTree A}} → List A → Tree
          to xs = node 0 (map toTree xs)
          from : ∀ {ℓ} {A : Set ℓ} {{_ : ToTree A}} → Tree → List A
          from (node _ xs) = map fromTree xs
          eq : ∀ {ℓ} {A : Set ℓ} {{t : ToTree A}} → IsInverse (to {{t}}) (from {{t}})
          eq [] = refl
          eq (x ∷ xs) = cong₂ _∷_ (invTree x) (eq xs)
