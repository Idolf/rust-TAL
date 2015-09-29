module Util.Tree where

open import Util.Dec
open import Util.Function

open import Data.Product using (_,_)
open import Data.Nat as N using (ℕ)
open import Data.List using (List ; [] ; _∷_)
import Data.List.Properties as LP

data Tree : Set where
  node : ℕ → List Tree → Tree

node-injective : IsInj₂ node
node-injective refl = refl , refl

record ToTree {a} (A : Set a) : Set a where
  constructor tree
  field
    toTree : A → Tree
    fromTree : Tree → A
    invTree : IsInverse toTree fromTree

toTree : ∀ {a} {A : Set a} {{_ : ToTree A}} → A → Tree
toTree {{t}} = ToTree.toTree t

fromTree : ∀ {a} {A : Set a} {{_ : ToTree A}} → Tree → A
fromTree {{t}} = ToTree.fromTree t

invTree : ∀ {a} {A : Set a} {{t : ToTree A}} → IsInverse (toTree {{t}}) (fromTree {{t}})
invTree {{t}} = ToTree.invTree t

default : ∀ {a} {A : Set a} {{t : ToTree A}} → A
default = fromTree (node 0 [])

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
        node i₁ nodes₁ == node i₂ nodes₂ = dec-cong₂ node-injective (i₁ N.≟ i₂) (nodes₁ ==⋆ nodes₂)

        -- This is just to make the termination checker happy
        _==⋆_ : DecEqFun (List Tree)
        [] ==⋆ [] = yes refl
        [] ==⋆ (node₂ ∷ nodes₂) = no (λ ())
        (node₁ ∷ nodes₁) ==⋆ [] = no (λ ())
        (node₁ ∷ nodes₁) ==⋆ (node₂ ∷ nodes₂) = dec-cong₂ LP.∷-injective (node₁ == node₂) (nodes₁ ==⋆ nodes₂)

instance
  Tree-Tree : ToTree Tree
  Tree-Tree = tree id id (λ x → refl)

  ToTree-dec-eq : ∀ {ℓ} {A : Set ℓ} {{_ : ToTree A}} → DecEq A
  ToTree-dec-eq {{t}} = decEq (to-eqfun t)
    where to-eqfun : ∀ {a} {A : Set a} → ToTree A → DecEqFun A
          to-eqfun t = Inverse-eqFun {{Tree-eq-dec}} (ToTree.fromTree t , ToTree.invTree t)
