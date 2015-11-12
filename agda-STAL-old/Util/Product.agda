module Util.Product where

-- Re-exports
open import Data.Product
  using ( _×_ ; _,_ ; Σ ; Σ-syntax ; proj₁ ; proj₂ ; ∃ ; ∃₂)
  renaming (map to Σ-map ; zip to Σ-zip) public

-- Local imports
open import Util.Maybe
open import Util.Eq
open import Util.Function
open import Util.Tree
open import Data.List using (_∷_)

instance
  Product-Tree : ∀ {a b} {A : Set a} {B : A → Set b} →
                   {{_ : ToTree A}} {{_ : ∀ {x} → ToTree (B x)}} →
                   ToTree (Σ A B)
  Product-Tree {A = A} {B} = tree to from eq
    where to : Σ A B → Tree
          to (x , y) = T₂ 0 (toTree x) (toTree y)
          from : Tree → Maybe (Σ A B)
          from (node _ (x ∷ y ∷ _)) with fromTree x
          from (node _ (x ∷ y ∷ _)) | nothing = nothing
          from (node _ (x ∷ y ∷ _)) | just x' = _,_ x' <$> fromTree y
          from _ = nothing
          eq : IsInverse to from
          eq (x , y) rewrite invTree x | invTree y = refl
