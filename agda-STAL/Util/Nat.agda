module Util.Nat where

-- Re-exports
open import Data.Nat using (ℕ ; zero ; suc ; _≤?_) public

-- Local imports
open import Util.Maybe
open import Util.Eq
open import Util.Tree
open import Data.Product using (_,_)

instance
  ℕ-Tree : ToTree ℕ
  ℕ-Tree = tree⋆ (λ { (node n _) → Just n }) (λ x → T₀ x , refl)
