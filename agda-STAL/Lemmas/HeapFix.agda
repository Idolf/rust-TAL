module Lemmas.HeapFix where

open import Util
open import Judgments
open import Lemmas.Types using (≤-trans)

-- The purpose if this file is to have lemmas,
-- that allows on to exchange the heap assumption with a more
-- restricted type.

wval-heapfix : ∀ {ψ₁ ψ₂ ψ₂' w τ} →
                 [] ⊢ ψ₂' ≤ ψ₂ →
                 ψ₁ , ψ₂  ⊢ w of τ wval →
                 ψ₁ , ψ₂' ⊢ w of τ wval
wval-heapfix ψ₂'≤ψ₂ (of-globval l τ'≤τ) = of-globval l τ'≤τ
wval-heapfix ψ₂'≤ψ₂ (of-heapval l τ'≤τ)
  with allzip-lookup₂ l ψ₂'≤ψ₂
... | τ' , l' , τ''≤τ' = of-heapval l' (≤-trans τ''≤τ' τ'≤τ)
wval-heapfix ψ₂'≤ψ₂ of-int = of-int
wval-heapfix ψ₂'≤ψ₂ of-ns = of-ns
wval-heapfix ψ₂'≤ψ₂ (of-Λ w⋆ θs⋆ subs-Γ Γ₃≤Γ₂) = of-Λ (wval-heapfix ψ₂'≤ψ₂ w⋆) θs⋆ subs-Γ Γ₃≤Γ₂

wval⁰-heapfix : ∀ {ψ₁ ψ₂ ψ₂' w τ⁻} →
                  [] ⊢ ψ₂' ≤ ψ₂ →
                  ψ₁ , ψ₂  ⊢ w of τ⁻ wval⁰ →
                  ψ₁ , ψ₂' ⊢ w of τ⁻ wval⁰
wval⁰-heapfix ψ₂'≤ψ₂ (of-uninit τ⋆) = of-uninit τ⋆
wval⁰-heapfix ψ₂'≤ψ₂ (of-init w⋆) = of-init (wval-heapfix ψ₂'≤ψ₂ w⋆)

stack-heapfix : ∀ {ψ₁ ψ₂ ψ₂' S σ} →
                  [] ⊢ ψ₂' ≤ ψ₂ →
                  ψ₁ , ψ₂ ⊢ S of σ stack →
                  ψ₁ , ψ₂' ⊢ S of σ stack
stack-heapfix ψ₂'≤ψ₂ [] = []
stack-heapfix ψ₂'≤ψ₂ (w⋆ ∷ S⋆) = wval-heapfix ψ₂'≤ψ₂ w⋆ ∷ stack-heapfix ψ₂'≤ψ₂ S⋆

hval-heapfix : ∀ {ψ₁ ψ₂' ψ₂ h τ} →
                 [] ⊢ ψ₂' ≤ ψ₂ →
                 ψ₁ , ψ₂  ⊢ h of τ hval →
                 ψ₁ , ψ₂' ⊢ h of τ hval
hval-heapfix ψ₂'≤ψ₂ (of-tuple eqs ws⋆) = of-tuple eqs (AllZip-map (wval⁰-heapfix ψ₂'≤ψ₂) ws⋆)

register-heapfix : ∀ {ψ₁ ψ₂ ψ₂' R Γ} →
                   [] ⊢ ψ₂' ≤ ψ₂ →
                   ψ₁ , ψ₂ ⊢ R of Γ register →
                   ψ₁ , ψ₂' ⊢ R of Γ register
register-heapfix ψ₂'≤ψ₂ (of-register sp⋆ regs⋆)
  = of-register (stack-heapfix ψ₂'≤ψ₂ sp⋆) (AllZipᵥ-map (wval-heapfix ψ₂'≤ψ₂) regs⋆)
