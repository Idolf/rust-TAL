module Lemmas.TermHeapCast where

open import Util
open import Judgments
open import Lemmas.Types using (≤-trans)

-- The purpose if this file is to have lemmas,
-- that allows on to exchange the heap assumption with a more
-- restricted type.

private
  wval-heapcast : ∀ {ψ₁ ψ₂ ψ₂' w τ} →
                   [] ⊢ ψ₂' ≤ ψ₂ →
                   ψ₁ , ψ₂  ⊢ w of τ wval →
                   ψ₁ , ψ₂' ⊢ w of τ wval
  wval-heapcast ψ₂'≤ψ₂ (of-globval l τ'≤τ) = of-globval l τ'≤τ
  wval-heapcast ψ₂'≤ψ₂ (of-heapval l τ'≤τ)
    with allzip-lookup₂ l ψ₂'≤ψ₂
  ... | τ' , l' , τ''≤τ' = of-heapval l' (≤-trans τ''≤τ' τ'≤τ)
  wval-heapcast ψ₂'≤ψ₂ of-int = of-int
  wval-heapcast ψ₂'≤ψ₂ of-uninit = of-uninit
  wval-heapcast ψ₂'≤ψ₂ (of-Λ w⋆ θs⋆ subs-Γ Γ₃≤Γ₂) = of-Λ (wval-heapcast ψ₂'≤ψ₂ w⋆) θs⋆ subs-Γ Γ₃≤Γ₂

  wval⁰-heapcast : ∀ {ψ₁ ψ₂ ψ₂' w τ⁻} →
                     [] ⊢ ψ₂' ≤ ψ₂ →
                     ψ₁ , ψ₂  ⊢ w of τ⁻ wval⁰ →
                     ψ₁ , ψ₂' ⊢ w of τ⁻ wval⁰
  wval⁰-heapcast ψ₂'≤ψ₂ (of-uninit τ⋆) = of-uninit τ⋆
  wval⁰-heapcast ψ₂'≤ψ₂ (of-init w⋆) = of-init (wval-heapcast ψ₂'≤ψ₂ w⋆)

  hval-heapcast : ∀ {ψ₁ ψ₂' ψ₂ h τ} →
                    [] ⊢ ψ₂' ≤ ψ₂ →
                    ψ₁ , ψ₂  ⊢ h of τ hval →
                    ψ₁ , ψ₂' ⊢ h of τ hval
  hval-heapcast ψ₂'≤ψ₂ (of-tuple eqs ws⋆) = of-tuple eqs (AllZip-map (wval⁰-heapcast ψ₂'≤ψ₂) ws⋆)

regs-heapcast : ∀ {ψ₁ ψ₂ ψ₂' n ws} {τs : Vec Type n} →
                  [] ⊢ ψ₂' ≤ ψ₂ →
                  AllZipᵥ (λ w τ → ψ₁ , ψ₂  ⊢ w of τ wval) ws τs →
                  AllZipᵥ (λ w τ → ψ₁ , ψ₂' ⊢ w of τ wval) ws τs
regs-heapcast ψ₂'≤ψ₂ ws⋆ = AllZipᵥ-map (wval-heapcast ψ₂'≤ψ₂) ws⋆

stack-heapcast : ∀ {ψ₁ ψ₂ ψ₂' S σ} →
                   [] ⊢ ψ₂' ≤ ψ₂ →
                   ψ₁ , ψ₂ ⊢ S of σ stack →
                   ψ₁ , ψ₂' ⊢ S of σ stack
stack-heapcast ψ₂'≤ψ₂ [] = []
stack-heapcast ψ₂'≤ψ₂ (w⋆ ∷ S⋆) = wval-heapcast ψ₂'≤ψ₂ w⋆ ∷ stack-heapcast ψ₂'≤ψ₂ S⋆

register-heapcast : ∀ {ψ₁ ψ₂ ψ₂' R Γ} →
                      [] ⊢ ψ₂' ≤ ψ₂ →
                      ψ₁ , ψ₂ ⊢ R of Γ register →
                      ψ₁ , ψ₂' ⊢ R of Γ register
register-heapcast ψ₂'≤ψ₂ (of-register sp⋆ regs⋆)
  = of-register (stack-heapcast ψ₂'≤ψ₂ sp⋆) (AllZipᵥ-map (wval-heapcast ψ₂'≤ψ₂) regs⋆)

hvals-heapcast : ∀ {ψ₁ ψ₂ ψ₂' hs τs} →
                   [] ⊢ ψ₂' ≤ ψ₂ →
                   AllZip (λ h τ → ψ₁ , ψ₂  ⊢ h of τ hval) hs τs →
                   AllZip (λ h τ → ψ₁ , ψ₂' ⊢ h of τ hval) hs τs
hvals-heapcast ψ₂'≤ψ₂ hs⋆ = AllZip-map (hval-heapcast ψ₂'≤ψ₂) hs⋆
