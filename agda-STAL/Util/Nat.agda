module Util.Nat where

-- Re-exports
open import Data.Nat
  using ( ℕ ; zero ; suc ; pred ; _<_ ; _>_ ; _≤_
        ; _≥_ ; _+_ ; _∸_ ; _≤?_ ; s≤s ; z≤n)
  public
module ≤-Reasoning = Data.Nat.≤-Reasoning
open import Data.Nat.Properties
  using ( 1+n≰n ; ≤⇒pred≤ ; pred-mono ; m≤m+n ; n≤m+n; ≰⇒>
        ; ≤-step ; ≤-steps ; m+n∸m≡n ; n∸n≡0)
  renaming ( <-trans to Nat-<-trans )
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
import Algebra as A

open A.CommutativeSemiring NP.commutativeSemiring
  using (+-comm ; +-assoc) public

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

l+m≤l+n : ∀ l {m n} → m ≤ n → l + m ≤ l + n
l+m≤l+n zero m≤n = m≤n
l+m≤l+n (suc l) m≤n = s≤s (l+m≤l+n l m≤n)

l+m<l+n : ∀ l {m n} → m < n → l + m < l + n
l+m<l+n zero m≤n = m≤n
l+m<l+n (suc l) m≤n = s≤s (l+m<l+n l m≤n)

l+m≤l+n⁻¹ : ∀ l {m n} → l + m ≤ l + n → m ≤ n
l+m≤l+n⁻¹ zero m≤n = m≤n
l+m≤l+n⁻¹ (suc l) (s≤s m≤n) = l+m≤l+n⁻¹ l m≤n

instance
  ℕ-Tree : ToTree ℕ
  ℕ-Tree = tree⋆ (λ { (node n _) → just n }) (λ x → T₀ x , refl)
