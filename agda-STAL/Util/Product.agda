module Util.Product where

-- Re-exports
open import Data.Product
  using (_×_ ; _,_ ; Σ ; Σ-syntax ; proj₁ ; proj₂ ; ∃)
  renaming (map to ×-map) public

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
  Product-Tree = tree to from eq
    where to : ∀ {a b} {A : Set a} {B : A → Set b}
                 {{ta : ToTree A}} {{tb : ∀ {x} → ToTree (B x)}} →
                 Σ A B → Tree
          to (x , y) = T₂ 0 (toTree x) (toTree y)
          from : ∀ {a b} {A : Set a} {B : A → Set b}
                   {{ta : ToTree A}} {{tb : ∀ {x} → ToTree (B x)}} →
                   Tree → ¿ Σ A B
          from (node _ (x ∷ y ∷ _)) with fromTree x
          from (node _ (x ∷ y ∷ _)) | Nothing = Nothing
          from (node _ (x ∷ y ∷ _)) | Just x' = _,_ x' <$> fromTree y
          from _ = Nothing
          eq : ∀ {a b} {A : Set a} {B : A → Set b} {{ta : ToTree A}}
                 {{tb : ∀ {x} → ToTree (B x)}} →
                 IsInverse (to {B = B}) from
          eq (x , y) rewrite invTree x | invTree y = refl