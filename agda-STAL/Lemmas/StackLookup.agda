module Lemmas.StackLookup where

open import Util
open import Judgments

stack-lookup-dec : ∀ i σ → Dec (∃ λ τ → stack-lookup i σ τ)
stack-lookup-dec i (ρ⁼ ι) = no (λ { (_ , ()) })
stack-lookup-dec i [] = no (λ { (_ , ()) })
stack-lookup-dec zero (τ ∷ σ) = yes (τ , here)
stack-lookup-dec (suc i) (τ ∷ σ) with stack-lookup-dec i σ
... | yes (τ' , l) = yes (τ' , there l)
... | no ¬l = no (λ { (τ' , there l) → ¬l (τ' , l)})

stack-lookup-unique : ∀ {i σ τ₁ τ₂} →
                        stack-lookup i σ τ₁ →
                        stack-lookup i σ τ₂ →
                        τ₁ ≡ τ₂
stack-lookup-unique here here = refl
stack-lookup-unique (there l₁) (there l₂) = stack-lookup-unique l₁ l₂

stack-update-dec : ∀ i τ σ → Dec (∃ λ σ' → stack-update i τ σ σ')
stack-update-dec i τ (ρ⁼ ι) = no (λ { (_ , ()) })
stack-update-dec i τ [] = no (λ { (_ , ()) })
stack-update-dec zero τ (τ' ∷ σ) = yes (τ ∷ σ , here)
stack-update-dec (suc i) τ (τ' ∷ σ) with stack-update-dec i τ σ
... | yes (σ' , up) = yes (τ' ∷ σ' , there up)
... | no ¬up = no (λ { (.τ' ∷ σ' , there up) → ¬up (σ' , up)})

stack-update-unique : ∀ {i τ σ σ₁ σ₂} →
                        stack-update i τ σ σ₁ →
                        stack-update i τ σ σ₂ →
                        σ₁ ≡ σ₂
stack-update-unique here here = refl
stack-update-unique (there up₁) (there up₂)
  rewrite stack-update-unique up₁ up₂ = refl
