module Judgments.StackOperations where

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

stack-append : List Type → StackType → StackType
stack-append [] σ = σ
stack-append (τ ∷ τs) σ = τ ∷ stack-append τs σ

data stack-drop : ℕ → StackType → StackType → Set where
  here : ∀ {σ} → stack-drop 0 σ σ
  there : ∀ {n τ σ σ'} → stack-drop n σ σ' → stack-drop (suc n) (τ ∷ σ) σ'
