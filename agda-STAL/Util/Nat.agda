module Util.Nat where

-- Re-exports
open import Data.Nat using (ℕ ; zero ; suc ; _<_ ; _≤_ ; _+_ ; _≤?_) public

-- Local imports
open import Util.Maybe
open import Util.Eq
open import Util.Dec
open import Util.Tree
open import Data.Product using (_,_)
import Data.Nat.Properties as NP
import Relation.Binary as B

Nat-cmp : Trichotomous {A = ℕ} _≡_ _<_
Nat-cmp = B.IsStrictTotalOrder.compare
  (B.StrictTotalOrder.isStrictTotalOrder NP.strictTotalOrder)

instance
  ℕ-Tree : ToTree ℕ
  ℕ-Tree = tree⋆ (λ { (node n _) → Just n }) (λ x → T₀ x , refl)
