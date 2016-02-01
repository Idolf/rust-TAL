module Lemmas.WeakenRight where

open import Util
open import Judgments
open import Lemmas.TypeSubstitution

instantiation-weaken-right : ∀ Δ₁ Δ₂ {i a} →
                         Δ₁ ⊢ i of a instantiation →
                         Δ₁ ++ Δ₂ ⊢ i of a instantiation
instantiation-weaken-right Δ₁ Δ₂ (of-α τ⋆) = of-α (valid-++ τ⋆)
instantiation-weaken-right Δ₁ Δ₂ (of-ρ σ⋆) = of-ρ (valid-++ σ⋆)

instantiations-weaken-right : ∀ Δ₁ Δ₂ {is Δ} →
                          Δ₁ ⊢ is of Δ instantiations →
                          Δ₁ ++ Δ₂ ⊢ is of Δ instantiations
instantiations-weaken-right Δ₁ Δ₂ [] = []
instantiations-weaken-right Δ₁ Δ₂ (_∷_ {Δ' = Δ'} i⋆ is⋆)
  with instantiation-weaken-right (Δ' ++ Δ₁) Δ₂ i⋆
... | i⋆'
  rewrite List-++-assoc Δ' Δ₁ Δ₂
    = i⋆' ∷ instantiations-weaken-right Δ₁ Δ₂ is⋆

vval-weaken-right : ∀ Δ₁ Δ₂ {ψ₁ Γ v τ} →
                      ψ₁ , Δ₁ , Γ ⊢ v of τ vval →
                      ψ₁ , Δ₁ ++ Δ₂ , Γ ⊢ v of τ vval
vval-weaken-right Δ₁ Δ₂ of-reg = of-reg
vval-weaken-right Δ₁ Δ₂ (of-globval l) = of-globval l
vval-weaken-right Δ₁ Δ₂ of-int = of-int
vval-weaken-right Δ₁ Δ₂ of-ns = of-ns
vval-weaken-right Δ₁ Δ₂ (of-Λ {Δ₂ = Δ} v⋆ is⋆ subs-Γ)
  with instantiations-weaken-right (Δ ++ Δ₁) Δ₂ is⋆
... | is⋆'
  rewrite List-++-assoc Δ Δ₁ Δ₂
  = of-Λ (vval-weaken-right Δ₁ Δ₂ v⋆) is⋆' subs-Γ

instruction-weaken-right : ∀ {ψ₁} Δ₁ Δ₂ {ι Γ Γ'} →
                       ψ₁ , Δ₁ , Γ ⊢ ι ⇒ Γ' instruction →
                       ψ₁ , Δ₁ ++ Δ₂ , Γ ⊢ ι ⇒ Γ' instruction
instruction-weaken-right Δ₁ Δ₂ (of-add eq v⋆) = of-add eq (vval-weaken-right Δ₁ Δ₂ v⋆)
instruction-weaken-right Δ₁ Δ₂ (of-sub eq v⋆) = of-sub eq (vval-weaken-right Δ₁ Δ₂ v⋆)
instruction-weaken-right Δ₁ Δ₂ of-salloc = of-salloc
instruction-weaken-right Δ₁ Δ₂ (of-sfree drop) = of-sfree drop
instruction-weaken-right Δ₁ Δ₂ (of-sld l) = of-sld l
instruction-weaken-right Δ₁ Δ₂ (of-sst up) = of-sst up
instruction-weaken-right Δ₁ Δ₂ (of-ld eq l) = of-ld eq l
instruction-weaken-right Δ₁ Δ₂ (of-st eq lookup≤τ l up) = of-st eq (≤-++ lookup≤τ) l up
instruction-weaken-right Δ₁ Δ₂ (of-malloc τs⋆) = of-malloc (valid-++ τs⋆)
instruction-weaken-right Δ₁ Δ₂ (of-mov v⋆) = of-mov (vval-weaken-right Δ₁ Δ₂ v⋆)
instruction-weaken-right Δ₁ Δ₂ (of-beq eq v⋆ Γ≤Γ') = of-beq eq (vval-weaken-right Δ₁ Δ₂ v⋆) (≤-++ Γ≤Γ')

instructionsequence-weaken-right : ∀ {ψ₁} Δ₁ Δ₂ {Γ I} →
                                     ψ₁ , Δ₁ , Γ ⊢ I instructionsequence →
                                     ψ₁ , Δ₁ ++ Δ₂ , Γ ⊢ I instructionsequence
instructionsequence-weaken-right Δ₁ Δ₂ (of-~> ι⋆ I⋆)
  with instruction-weaken-right Δ₁ Δ₂ ι⋆
... | ι⋆'
  = of-~> ι⋆' (instructionsequence-weaken-right Δ₁ Δ₂ I⋆)
instructionsequence-weaken-right Δ₁ Δ₂ (of-jmp v⋆ Γ≤Γ') = of-jmp (vval-weaken-right Δ₁ Δ₂ v⋆) (≤-++ Γ≤Γ')
instructionsequence-weaken-right Δ₁ Δ₂ of-halt = of-halt
