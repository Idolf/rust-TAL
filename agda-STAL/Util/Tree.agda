module Util.Tree where

-- Local imports
open import Util.Maybe
open import Util.Eq
open import Util.Dec
open import Util.Function
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Nat as N using (ℕ)
open import Data.List using (List ; [] ; _∷_)
open import Data.List.Properties using (∷-injective)


-- The goal of this module is to establish an easy way to
-- get decidable equality for any type A. This is done by
-- creating a function (f : A → Tree) with an inverse
-- (g : Tree → ¿ A). Here "Tree" is a type containing
-- arbitrarily branching tree with a number at every nodes.
-- Sine f has an inverse, it must be injective. Since we can
-- decide equality on Tree, we can decide equality on A.

data Tree : Set where
  node : ℕ → List Tree → Tree

node-injective : IsInjective₂ node
node-injective refl = refl , refl

record ToTree {a} (A : Set a) : Set a where
  constructor tree
  field
    toTree : A → Tree
    fromTree : Tree → ¿ A
    invTree : IsInverse toTree fromTree

tree⋆ : ∀ {a} {A : Set a} →
          (fromTree : Tree → ¿ A) →
          IsSurjective fromTree →
          ToTree A
tree⋆ fromTree isSur = tree (proj₁ ∘ isSur) fromTree (proj₂ ∘ isSur)

toTree : ∀ {a} {A : Set a} {{_ : ToTree A}} → A → Tree
toTree {{t}} = ToTree.toTree t

fromTree : ∀ {a} {A : Set a} {{_ : ToTree A}} → Tree → ¿ A
fromTree {{t}} = ToTree.fromTree t

invTree : ∀ {a} {A : Set a} {{t : ToTree A}} →
            IsInverse toTree fromTree
invTree {{t}} = ToTree.invTree t

T₀ : ℕ → Tree
T₀ n = node n []

T₁ : ∀ {a} {A : Set a} {{_ : ToTree A}} → ℕ → A → Tree
T₁ n x = node n (toTree x ∷ [])

T₂ : ∀ {a b} {A : Set a} {B : Set b}
       {{_ : ToTree A}} {{_ : ToTree B}} →
       ℕ → A → B → Tree
T₂ n x y = node n (toTree x ∷ toTree y ∷ [])

T₃ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
       {{_ : ToTree A}} {{_ : ToTree B}} {{_ : ToTree C}} →
       ℕ → A → B → C → Tree
T₃ n x y z = node n (toTree x ∷ toTree y ∷ toTree z ∷ [])

T₄ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
       {{_ : ToTree A}} {{_ : ToTree B}} {{_ : ToTree C}} {{_ : ToTree D}} →
       ℕ → A → B → C → D → Tree
T₄ n x y z q = node n (toTree x ∷ toTree y ∷ toTree z ∷ toTree q ∷ [])

private
  Tree-eq-dec : DecEq Tree
  Tree-eq-dec = decEq _==_
    where
      mutual
        _==_ : DecEqFun Tree
        node i₁ nodes₁ == node i₂ nodes₂ =
          dec-cong₂ node-injective (i₁ N.≟ i₂) (nodes₁ ==Just nodes₂)

        -- This is just to make the termination checker happy
        _==Just_ : DecEqFun (List Tree)
        [] ==Just [] = yes refl
        [] ==Just (node₂ ∷ nodes₂) = no (λ ())
        (node₁ ∷ nodes₁) ==Just [] = no (λ ())
        (node₁ ∷ nodes₁) ==Just (node₂ ∷ nodes₂) =
          dec-cong₂ ∷-injective (node₁ == node₂) (nodes₁ ==Just nodes₂)

instance
  Tree-Tree : ToTree Tree
  Tree-Tree = tree id Just (λ x → refl)

  ToTree-dec-eq : ∀ {ℓ} {A : Set ℓ} {{_ : ToTree A}} → DecEq A
  ToTree-dec-eq {{t}} = decEq (
    HasInverse→DecEqFun {{Tree-eq-dec}}
      (ToTree.fromTree t , ToTree.invTree t))

  ¿-Tree : ∀ {a} {A : Set a} {{_ : ToTree A}} → ToTree (¿ A)
  ¿-Tree = tree⋆ (λ {(node 0 _)      → Just Nothing
                  ; (node 1 (v ∷ _)) → Just <$> fromTree v
                  ; _                → Nothing })
                 (λ {Nothing         → T₀ 0   , refl
                  ; (Just v)         → T₁ 1 v , Just <$=> invTree v })
