module Util.Fin where

open import Data.Fin using (Fin ; zero ; suc ; toℕ ; fromℕ≤ ; #_) public
import Data.Fin.Properties as FP

open import Data.Nat
open import Data.Fin.Properties
open import Util.Dec
open import Util.Tree
open import Util.Function

instance
  Fin-ToTree : ∀ {n} → ToTree (Fin (suc n))
  Fin-ToTree = tree to from eq
    where to : ∀ {n} → Fin (suc n) → Tree
          to v = T₀ (toℕ v)
          from : ∀ {n} → Tree → Fin (suc n)
          from {n} (node v _) with suc v ≤? suc n
          from (node v _) | yes sucv≤sucn = fromℕ≤ sucv≤sucn
          from (node v x) | no ¬p = zero
          eq : ∀ {n} → IsInverse (to {n}) from
          eq {n} v with suc (toℕ v) ≤? suc n
          eq v | yes sucv≤sucn = fromℕ≤-toℕ v sucv≤sucn
          eq v | no ¬le with ¬le (bounded v)
          eq v | no ¬le | ()
