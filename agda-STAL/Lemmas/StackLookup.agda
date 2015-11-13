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

stack-lookup-valid : ∀ {Δ i σ τ} →
                       Δ ⊢ σ Valid →
                       stack-lookup i σ τ →
                       Δ ⊢ τ Valid
stack-lookup-valid (τ⋆ ∷ σ⋆) here = τ⋆
stack-lookup-valid (τ⋆ ∷ σ⋆) (there l) = stack-lookup-valid σ⋆ l

stack-update-valid : ∀ {Δ i σ σ' τ} →
                       Δ ⊢ σ Valid →
                       Δ ⊢ τ Valid →
                       stack-update i τ σ σ' →
                       Δ ⊢ σ' Valid
stack-update-valid (τ'⋆ ∷ σ⋆) τ⋆ here = τ⋆ ∷ σ⋆
stack-update-valid (τ'⋆ ∷ σ⋆) τ⋆ (there up) = τ'⋆ ∷ stack-update-valid σ⋆ τ⋆ up

stack-append-valid : ∀ {Δ τs σ} →
                       Δ ⊢ τs Valid →
                       Δ ⊢ σ Valid →
                       Δ ⊢ stack-append τs σ Valid
stack-append-valid [] σ⋆ = σ⋆
stack-append-valid (τ⋆ ∷ τs⋆) σ⋆ = τ⋆ ∷ stack-append-valid τs⋆ σ⋆

stack-append-subtype : ∀ {Δ τs₁ τs₂ σ₁ σ₂} →
                         Δ ⊢ τs₁ ≤ τs₂ →
                         Δ ⊢ σ₁ ≤ σ₂ →
                         Δ ⊢ stack-append τs₁ σ₁ ≤ stack-append τs₂ σ₂
stack-append-subtype [] σ₁≤σ₂ = σ₁≤σ₂
stack-append-subtype (τ₁≤τ₂ ∷ τs₁≤τs₂) σ₁≤σ₂ = τ₁≤τ₂ ∷ stack-append-subtype τs₁≤τs₂ σ₁≤σ₂

stack-drop-valid : ∀ {Δ i σ σ'} →
                     Δ ⊢ σ Valid →
                     stack-drop i σ σ' →
                     Δ ⊢ σ' Valid
stack-drop-valid (valid-ρ⁼ l) here = valid-ρ⁼ l
stack-drop-valid [] here = []
stack-drop-valid σ⋆ here = σ⋆
stack-drop-valid (τ⋆ ∷ σ⋆) (there drop) = stack-drop-valid σ⋆ drop

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

stack-drop-dec : ∀ i σ → Dec (∃ λ σ' → stack-drop i σ σ')
stack-drop-dec zero σ = yes (σ , here)
stack-drop-dec (suc i) (ρ⁼ ι) = no (λ { (_ , ()) })
stack-drop-dec (suc i) [] = no (λ { (_ , ()) })
stack-drop-dec (suc i) (τ ∷ σ)
  with stack-drop-dec i σ
... | yes (σ' , drop) = yes (σ' , there drop)
... | no ¬drop = no (λ { (σ' , there drop) → ¬drop (σ' , drop) })
