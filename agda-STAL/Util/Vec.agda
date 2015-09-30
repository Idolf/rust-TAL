module Util.Vec where

open import Data.Vec
  using (Vec ; [] ; _∷_ ; toList ; fromList)
  renaming (map to Vec-map) public
open import Data.Vec.Properties using ()
  renaming (∷-injective to Vec-∷-injective) public

open import Util.Eq
open import Util.Dec
open import Util.Tree
open import Util.Maybe
open import Util.Function

open import Data.Nat using (zero ; suc)
open import Data.List using (List ; map ; [] ; _∷_)

repeat : ∀ {a} {A : Set a} {m} → A → Vec A m
repeat {m = zero}  x = []
repeat {m = suc i} x = x ∷ repeat x

instance
  Vec-Tree : ∀ {ℓ} {A : Set ℓ} {{t : ToTree A}} {m} → ToTree (Vec A m)
  Vec-Tree = tree to from eq
    where to : ∀ {ℓ} {A : Set ℓ} {{t : ToTree A}} {m} → Vec A m → Tree
          to xs = node 0 (map toTree (toList xs))
          from' : ∀ {ℓ} {A : Set ℓ} {{t : ToTree A}} {m} →
                    List Tree → ¿ Vec A m
          from' {m = zero} [] = Just []
          from' {m = zero} (x ∷ xs) = Nothing
          from' {m = suc m} [] = Nothing
          from' {m = suc m} (x ∷ xs) = _∷_ <$> fromTree x <*> from' {m = m} xs
          from : ∀ {ℓ} {A : Set ℓ} {{t : ToTree A}} {m} → Tree → ¿ Vec A m
          from (node _ xs) = from' xs
          eq : ∀ {ℓ} {A : Set ℓ} {{t : ToTree A}} {m} →
                 IsInverse (to {{t}} {m}) from
          eq [] = refl
          eq (x ∷ xs) = _∷_ <$=> invTree x <*=> eq xs
