module Util.Fin where

-- Re-exports
open import Data.Fin using (Fin ; zero ; suc ; toℕ ; fromℕ≤ ; #_) public

-- Local imports
open import Util.Maybe
open import Util.Eq
open import Util.Function
open import Util.Tree
open import Data.List using ([])
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_,_ ; proj₁ ; proj₂)

instance
  Fin-ToTree : ∀ {n} → ToTree (Fin n)
  Fin-ToTree = tree⋆ (λ { (node n _) → from n })
                     (λ v → node (proj₁ (sur v)) [] , proj₂ (sur v))
    where from : ∀ {n} → ℕ → Maybe (Fin n)
          from {zero} _ = nothing
          from {suc n} zero = just zero
          from {suc n} (suc i) = suc <$> from i
          sur : ∀ {n} → IsSurjective (from {n})
          sur zero = zero , refl
          sur (suc v) = suc (proj₁ (sur v)) , suc <$=> proj₂ (sur v)
