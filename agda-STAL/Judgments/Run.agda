module Judgments.Run where

open import Util
open import Judgments.Grammar
open import Judgments.Substitution

data ReferenceMatch : TypeAssignmentValue → Instantiation → Set where
  match-α : ∀ {τ} → ReferenceMatch α (α τ)
  match-ρ : ∀ {σ} → ReferenceMatch ρ (ρ σ)

Strong→Weak : StrongCastValue → WeakCastValue
Strong→Weak (inst i) = inst i
Strong→Weak (weaken Δ⁺) = weaken (length Δ⁺)

infix 3 Run_⟦_⟧≡_
data Run_⟦_⟧≡_ : TypeAssignment → StrongCast → TypeAssignment → Set where
  run-inst :
            ∀ {Δ a i} →
         ReferenceMatch a i →
    ------------------------------
    Run a ∷ Δ ⟦ inst i / zero ⟧≡ Δ

  run-weaken :
               ∀ {Δ Δ⁺} →
    -----------------------------------
    Run Δ ⟦ weaken Δ⁺ / zero ⟧≡ Δ⁺ ++ Δ

  run-suc :
          ∀ {a a' Δ Δ' cᵥ ι} →
      a ⟦ Strong→Weak cᵥ / ι ⟧≡ a' →
         Run Δ ⟦ cᵥ / ι ⟧≡ Δ' →
    ---------------------------------
    Run a ∷ Δ ⟦ cᵥ / suc ι ⟧≡ a' ∷ Δ'
