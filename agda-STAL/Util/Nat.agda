module Util.Nat where

open import Data.Nat using (ℕ ; zero ; suc) public
import Data.Nat as N

open import Util.Eq
open import Util.Dec

suc-injective : ∀ {n₁ n₂} → suc n₁ ≡ suc n₂ → n₁ ≡ n₂
suc-injective refl = refl

instance
  ℕ-dec-eq : DecEq ℕ
  ℕ-dec-eq = decEq N._≟_
