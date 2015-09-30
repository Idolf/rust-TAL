module Util.Product where

open import Data.Product
  using (_×_ ; _,_ ; Σ ; Σ-syntax ; proj₁ ; proj₂ ; ∃)
  renaming (map to ×-map) public
open import Util.Eq
open import Util.Dec
open import Util.Tree
open import Util.Maybe
open import Util.Function

open import Data.List using (_∷_)

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
