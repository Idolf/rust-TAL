module Util.Fin where

-- Re-exports
open import Data.Fin using (Fin ; zero ; suc ; toℕ ; fromℕ≤ ; #_) public

-- Local imports
open import Util.Maybe
open import Util.Eq
open import Util.Function
open import Util.Dec
open import Util.Tree
open import Data.Nat using (_≤?_ ; suc)
open import Data.Fin.Properties using (fromℕ≤-toℕ ; bounded)

instance
  Fin-ToTree : ∀ {n} → ToTree (Fin n)
  Fin-ToTree = tree to from eq
    where to : ∀ {n} → Fin n → Tree
          to v = T₀ (toℕ v)
          from : ∀ {n} → Tree → ¿ Fin n
          from {n} (node v _) with suc v ≤? n
          from (node v _) | yes v<n = Just (fromℕ≤ v<n)
          from (node v x) | no ¬v≮n = Nothing
          eq : ∀ {n} → IsInverse (to {n}) from
          eq {n} v with suc (toℕ v) ≤? n
          eq v | yes v<n rewrite fromℕ≤-toℕ v v<n = refl
          eq v | no v≮n with v≮n (bounded v)
          eq v | no v≮n | ()
