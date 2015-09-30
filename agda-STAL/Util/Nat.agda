module Util.Nat where

-- Re-exports
open import Data.Nat using (ℕ ; zero ; suc) public

-- Local imports
open import Util.Maybe
open import Util.Eq
open import Util.Tree

instance
  ℕ-Tree : ToTree ℕ
  ℕ-Tree = tree T₀ (λ { (node n _) → Just n }) (λ x → refl)
