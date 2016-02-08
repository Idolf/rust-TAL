module Lemmas.HeapPush where

open import Util
open import Judgments
open HighGrammar

-- The purpose of this file is prove theorems related
-- to pushing values to the stack. Specifically all
-- things of relevance will preserve their type after
-- expanding the heap.

wval-++ : ∀ {ψ₁ ψ₂ ψ₂⁺ w τ} →
            ψ₁ , ψ₂ ⊢ w of τ wval →
            ψ₁ , ψ₂ ++ ψ₂⁺ ⊢ w of τ wval
wval-++ (of-globval l lookup≤τ) = of-globval l lookup≤τ
wval-++ {ψ₂⁺ = ψ₂⁺} (of-heapval l lookup≤τ) = of-heapval (↓-add-right ψ₂⁺ l) lookup≤τ
wval-++ of-int = of-int
wval-++ of-ns = of-ns
wval-++ (of-Λ w⋆ θs⋆ subs-Γ Γ₃≤Γ₂) = of-Λ (wval-++ w⋆) θs⋆ subs-Γ Γ₃≤Γ₂

private
  wval⁰-++ : ∀ {ψ₁ ψ₂ ψ₂⁺ w τ⁻} →
               ψ₁ , ψ₂ ⊢ w of τ⁻ wval⁰ →
               ψ₁ , ψ₂ ++ ψ₂⁺ ⊢ w of τ⁻ wval⁰
  wval⁰-++ (of-uninit τ⋆) = of-uninit τ⋆
  wval⁰-++ (of-init w⋆) = of-init (wval-++ w⋆)

  hval-++ : ∀ {ψ₁ ψ₂ ψ₂⁺ h τ} →
              ψ₁ , ψ₂ ⊢ h of τ hval →
              ψ₁ , ψ₂ ++ ψ₂⁺ ⊢ h of τ hval
  hval-++ (of-tuple ws⋆) = of-tuple (AllZip-map wval⁰-++ ws⋆)

  hvals-++ : ∀ {ψ₁ ψ₂ ψ₂⁺ hs τs} →
                 AllZip (λ h τ → ψ₁ , ψ₂ ⊢ h of τ hval) hs τs →
                 AllZip (λ h τ → ψ₁ , ψ₂ ++ ψ₂⁺ ⊢ h of τ hval) hs τs
  hvals-++ hs⋆ = AllZip-map hval-++ hs⋆

stack-++ : ∀ {ψ₁ ψ₂ ψ₂⁺ sp σ} →
              ψ₁ , ψ₂ ⊢ sp of σ stack →
              ψ₁ , ψ₂ ++ ψ₂⁺ ⊢ sp of σ stack
stack-++ [] = []
stack-++ (w⋆ ∷ sp⋆) = wval-++ w⋆ ∷ stack-++ sp⋆

heap-push : ∀ {ψ₁ H ψ₂ h τ} →
              ψ₁ ⊢ H of ψ₂ heap →
              ψ₁ , ψ₂ ⊢ h of τ hval →
              ψ₁ ⊢ H ∷ʳ h of ψ₂ ∷ʳ τ heap
heap-push {τ = τₐ} (of-heap hs⋆) h⋆
  with hvals-++ hs⋆ | hval-++ h⋆
... | hs⋆' | h⋆' = of-heap (AllZip-++ hs⋆' (h⋆' ∷ []))
