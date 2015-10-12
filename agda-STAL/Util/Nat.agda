module Util.Nat where

-- Re-exports
open import Data.Nat
  using ( ℕ ; zero ; suc ; _<_ ; _>_ ; _≤_
        ; _≥_ ; _+_ ; _∸_ ; _≤?_ ; s≤s ; z≤n)
  public

-- Local imports
open import Util.Maybe
open import Util.Eq
open import Util.Dec
open import Util.Tree
open import Data.Product using (_,_ ; ,_ ; ∃ ; proj₂)
import Data.Nat as N
import Data.Nat.Properties as NP
import Relation.Binary as B

Nat-cmp : Trichotomous {A = ℕ} _≡_ _<_
Nat-cmp = B.StrictTotalOrder.compare NP.strictTotalOrder

Nat-≤-trans : ∀ {n₁ n₂ n₃} → n₁ ≤ n₂ → n₂ ≤ n₃ → n₁ ≤ n₃
Nat-≤-trans = B.DecTotalOrder.trans N.decTotalOrder

Nat-≤-refl : ∀ n → n ≤ n
Nat-≤-refl n = B.DecTotalOrder.reflexive N.decTotalOrder refl

≤⇒+ : ∀ {n m} → n ≤ m →
        ∃ λ k → m ≡ n + k
≤⇒+ z≤n = , refl
≤⇒+ (s≤s l) = , cong suc (proj₂ (≤⇒+ l))

instance
  ℕ-Tree : ToTree ℕ
  ℕ-Tree = tree⋆ (λ { (node n _) → Just n }) (λ x → T₀ x , refl)
