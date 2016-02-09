module Lemmas.TermWeaken where

open import Util
open import Judgments
open import Lemmas.TypeSubstitution using (valid-++ ; ≤-++)

-- The purpose of this file is to prove a simple theorem:
-- * If an InstructionSequence is valid in a context,
--     then it is also valid if we extend the context.

private
  instantiation-weaken : ∀ Δ₁ Δ₂ {θ a} →
                           Δ₁ ⊢ θ of a instantiation →
                           Δ₁ ++ Δ₂ ⊢ θ of a instantiation
  instantiation-weaken Δ₁ Δ₂ (of-α τ⋆) = of-α (valid-++ τ⋆)
  instantiation-weaken Δ₁ Δ₂ (of-ρ σ⋆) = of-ρ (valid-++ σ⋆)

  instantiations-weaken : ∀ Δ₁ Δ₂ {θs Δ} →
                            Δ₁ ⊢ θs of Δ instantiations →
                            Δ₁ ++ Δ₂ ⊢ θs of Δ instantiations
  instantiations-weaken Δ₁ Δ₂ [] = []
  instantiations-weaken Δ₁ Δ₂ (_∷_ {Δ' = Δ'} θ⋆ θs⋆)
    with instantiation-weaken (Δ' ++ Δ₁) Δ₂ θ⋆
  ... | θ⋆'
    rewrite List-++-assoc Δ' Δ₁ Δ₂
      = θ⋆' ∷ instantiations-weaken Δ₁ Δ₂ θs⋆

  vval-weaken : ∀ Δ₁ Δ₂ {ψ₁ Γ v τ} →
                  ψ₁ , Δ₁ ⊢ v of Γ ⇒ τ vval →
                  ψ₁ , Δ₁ ++ Δ₂ ⊢ v of Γ ⇒ τ vval
  vval-weaken Δ₁ Δ₂ of-reg = of-reg
  vval-weaken Δ₁ Δ₂ (of-globval l) = of-globval l
  vval-weaken Δ₁ Δ₂ of-int = of-int
  vval-weaken Δ₁ Δ₂ (of-Λ {Δ₂ = Δ} v⋆ θs⋆ subs-Γ)
    with instantiations-weaken (Δ ++ Δ₁) Δ₂ θs⋆
  ... | θs⋆'
    rewrite List-++-assoc Δ Δ₁ Δ₂
    = of-Λ (vval-weaken Δ₁ Δ₂ v⋆) θs⋆' subs-Γ

  instruction-weaken : ∀ {ψ₁} Δ₁ Δ₂ {ι Γ Γ'} →
                         ψ₁ , Δ₁ ⊢ ι of Γ ⇒ Γ' instruction →
                         ψ₁ , Δ₁ ++ Δ₂ ⊢ ι of Γ ⇒ Γ' instruction
  instruction-weaken Δ₁ Δ₂ (of-add eq v⋆) = of-add eq (vval-weaken Δ₁ Δ₂ v⋆)
  instruction-weaken Δ₁ Δ₂ (of-sub eq v⋆) = of-sub eq (vval-weaken Δ₁ Δ₂ v⋆)
  instruction-weaken Δ₁ Δ₂ of-salloc = of-salloc
  instruction-weaken Δ₁ Δ₂ (of-sfree drop) = of-sfree drop
  instruction-weaken Δ₁ Δ₂ (of-sld l) = of-sld l
  instruction-weaken Δ₁ Δ₂ (of-sst up) = of-sst up
  instruction-weaken Δ₁ Δ₂ (of-ld eq l) = of-ld eq l
  instruction-weaken Δ₁ Δ₂ (of-st eq lookup≤τ l up) = of-st eq (≤-++ lookup≤τ) l up
  instruction-weaken Δ₁ Δ₂ (of-malloc τs⋆) = of-malloc (valid-++ τs⋆)
  instruction-weaken Δ₁ Δ₂ (of-mov v⋆) = of-mov (vval-weaken Δ₁ Δ₂ v⋆)
  instruction-weaken Δ₁ Δ₂ (of-beq eq v⋆ Γ≤Γ') = of-beq eq (vval-weaken Δ₁ Δ₂ v⋆) (≤-++ Γ≤Γ')

instructionsequence-weaken : ∀ {ψ₁} Δ₁ Δ₂ {Γ I} →
                               ψ₁ , Δ₁ ⊢ I of Γ instructionsequence →
                               ψ₁ , Δ₁ ++ Δ₂ ⊢ I of Γ instructionsequence
instructionsequence-weaken Δ₁ Δ₂ (of-~> ι⋆ I⋆)
  with instruction-weaken Δ₁ Δ₂ ι⋆
... | ι⋆'
  = of-~> ι⋆' (instructionsequence-weaken Δ₁ Δ₂ I⋆)
instructionsequence-weaken Δ₁ Δ₂ (of-jmp v⋆ Γ≤Γ') = of-jmp (vval-weaken Δ₁ Δ₂ v⋆) (≤-++ Γ≤Γ')
instructionsequence-weaken Δ₁ Δ₂ of-halt = of-halt
