module Lemmas.StackSubtyping where

open import Util
open import Judgments

-- The purpose of this file is to prove that:
-- * The stack operations preserves subtyping

stack-lookup-subtype : ∀ {Δ sp₁ sp₂ i τ₂} →
                         Δ ⊢ sp₁ ≤ sp₂ →
                         stack-lookup i sp₂ τ₂ →
                         ∃ λ τ₁ →
                             Δ ⊢ τ₁ ≤ τ₂ ×
                             stack-lookup i sp₁ τ₁
stack-lookup-subtype (τ₁≤τ₂ ∷ sp₁≤sp₂) here = _ , τ₁≤τ₂ , here
stack-lookup-subtype (τ₁≤τ₂ ∷ sp₁≤sp₂) (there l)
  with stack-lookup-subtype sp₁≤sp₂ l
... | τ₂' , τ₁≤τ₂' , l' = τ₂' , τ₁≤τ₂' , there l'

stack-update-subtype : ∀ {Δ sp₁ sp₂ sp₂' i τ₁ τ₂} →
                         Δ ⊢ sp₁ ≤ sp₂ →
                         Δ ⊢ τ₁ ≤ τ₂ →
                         stack-update i τ₂ sp₂ sp₂' →
                         ∃ λ sp₁' →
                             stack-update i τ₁ sp₁ sp₁' ×
                             Δ ⊢ sp₁' ≤ sp₂'
stack-update-subtype (τ₁≤τ₂' ∷ sp₁≤sp₂) τ₁≤τ₂ here = _ , here , τ₁≤τ₂ ∷ sp₁≤sp₂
stack-update-subtype (τ₁≤τ₂' ∷ sp₁≤sp₂) τ₁≤τ₂ (there up)
  with stack-update-subtype sp₁≤sp₂ τ₁≤τ₂ up
... | sp₁' , up' , sp₁'≤sp₂' = _ , there up' , τ₁≤τ₂' ∷ sp₁'≤sp₂'

stack-append-subtype : ∀ {Δ τs₁ τs₂ σ₁ σ₂} →
                         Δ ⊢ τs₁ ≤ τs₂ →
                         Δ ⊢ σ₁ ≤ σ₂ →
                         Δ ⊢ stack-append τs₁ σ₁ ≤ stack-append τs₂ σ₂
stack-append-subtype [] σ₁≤σ₂ = σ₁≤σ₂
stack-append-subtype (τ₁≤τ₂ ∷ τs₁≤τs₂) σ₁≤σ₂ = τ₁≤τ₂ ∷ stack-append-subtype τs₁≤τs₂ σ₁≤σ₂

stack-drop-subtype : ∀ {Δ i σ₁ σ₂ σ₂'} →
                     Δ ⊢ σ₁ ≤ σ₂ →
                     stack-drop i σ₂ σ₂' →
                     ∃ λ σ₁' →
                       stack-drop i σ₁ σ₁' ×
                       Δ ⊢ σ₁' ≤ σ₂'
stack-drop-subtype (ρ⁼-≤ l) here = _ , here , ρ⁼-≤ l
stack-drop-subtype [] here = _ , here , []
stack-drop-subtype σ₁≤σ₂ here = _ , here , σ₁≤σ₂
stack-drop-subtype (τ₁≤τ₂ ∷ σ₁≤σ₂) (there drop₁) =
  Σ-map _ (Σ-map there id) (stack-drop-subtype σ₁≤σ₂ drop₁)
