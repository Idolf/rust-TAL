module Judgments.StackLookup where

open import Util
open import Judgments.Grammar

data stack-lookup : ℕ → StackType → Type → Set where
  here :
            ∀ {τ σ} →
    ---------------------------
    stack-lookup zero (τ ∷ σ) τ

  there :
            ∀ {i σ τ₁ τ₂} →
          stack-lookup i σ τ₁ →
    --------------------------------
    stack-lookup (suc i) (τ₂ ∷ σ) τ₁

data stack-update : ℕ → Type → StackType → StackType → Set where
  here :
                ∀ {τ₁ τ₂ σ} →
    --------------------------------------
    stack-update zero τ₁ (τ₂ ∷ σ) (τ₁ ∷ σ)

  there :
               ∀ {i τ₁ τ₂ σ₁ σ₂} →
            stack-update i τ₁ σ₁ σ₂ →
    -------------------------------------------
    stack-update (suc i) τ₁ (τ₂ ∷ σ₁) (τ₂ ∷ σ₂)

register-stack-lookup : ℕ → RegisterAssignment → Type → Set
register-stack-lookup n (registerₐ sp regs) τ = stack-lookup n sp τ
