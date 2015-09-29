module Util.Nat where

open import Data.Nat using (ℕ ; zero ; suc) public
import Data.Nat as N

open import Util.Eq
open import Util.Tree
open import Util.Maybe

instance
  ℕ-Tree : ToTree ℕ
  ℕ-Tree = tree T₀ (λ { (node n _) → Just n }) (λ x → refl)
