module Util.Fin where

open import Data.Fin using (Fin ; zero ; suc ; toℕ ; fromℕ≤ ; #_) public
import Data.Fin.Properties as FP

open import Data.Nat
open import Data.Fin.Properties
open import Util.Dec
open import Util.Tree
open import Util.Maybe
open import Util.Function

instance
  Fin-ToTree : ∀ {n} → ToTree (Fin n)
  Fin-ToTree = tree to from eq
    where to : ∀ {n} → Fin n → Tree
          to v = T₀ (toℕ v)
          from : ∀ {n} → Tree → ¿ Fin n
          from {n} (node v _) with suc v ≤? n
          from (node v _) | yes v<n = Just (fromℕ≤ v<n)
          from (node v x) | no ¬p = Nothing
          eq : ∀ {n} → IsInverse (to {n}) from
          eq {n} v with suc (toℕ v) ≤? n
          eq v | yes v≤n rewrite fromℕ≤-toℕ v v≤n = refl
          eq v | no ¬le with ¬le (bounded v)
          eq v | no ¬le | ()
