module HeapPush where

open import Util
open import Judgments
open import Lemmas

wval-++ : ∀ {ψ₁ ψ₂ ψ₂⁺ w τ} →
            ψ₁ , ψ₂ ⊢ w of τ wval →
            ψ₁ , ψ₂ ++ ψ₂⁺ ⊢ w of τ wval
wval-++ (of-globval l lookup≤τ) = of-globval l lookup≤τ
wval-++ {ψ₂⁺ = ψ₂⁺} (of-heapval l lookup≤τ) = of-heapval (↓-add-right ψ₂⁺ l) lookup≤τ
wval-++ of-int = of-int
wval-++ of-ns = of-ns
wval-++ (of-Λ w⋆ is⋆ subs-Γ Γ₃≤Γ₂) = of-Λ (wval-++ w⋆) is⋆ subs-Γ Γ₃≤Γ₂

wval⁰-++ : ∀ {ψ₁ ψ₂ ψ₂⁺ w τ⁻} →
             ψ₁ , ψ₂ ⊢ w of τ⁻ wval⁰ →
             ψ₁ , ψ₂ ++ ψ₂⁺ ⊢ w of τ⁻ wval⁰
wval⁰-++ (of-uninit τ⋆) = of-uninit τ⋆
wval⁰-++ (of-init w⋆) = of-init (wval-++ w⋆)

wvals⁰-++ : ∀ {ψ₁ ψ₂ ψ₂⁺ ws τs⁻} →
              AllZip (λ w τ⁻ → ψ₁ , ψ₂ ⊢ w of τ⁻ wval⁰) ws τs⁻ →
              AllZip (λ w τ⁻ → ψ₁ , ψ₂ ++ ψ₂⁺ ⊢ w of τ⁻ wval⁰) ws τs⁻
wvals⁰-++ [] = []
wvals⁰-++ (w⋆ ∷ ws⋆) = wval⁰-++ w⋆ ∷ wvals⁰-++ ws⋆

hval-++ : ∀ {ψ₁ ψ₂ ψ₂⁺ h τ} →
            ψ₁ , ψ₂ ⊢ h of τ hval →
            ψ₁ , ψ₂ ++ ψ₂⁺ ⊢ h of τ hval
hval-++ (of-tuple ws⋆) = of-tuple (wvals⁰-++ ws⋆)

hvals-++ : ∀ {ψ₁ ψ₂ ψ₂⁺ hs τs} →
               AllZip (λ h τ → ψ₁ , ψ₂ ⊢ h of τ hval) hs τs →
               AllZip (λ h τ → ψ₁ , ψ₂ ++ ψ₂⁺ ⊢ h of τ hval) hs τs
hvals-++ [] = []
hvals-++ (h⋆ ∷ hs⋆) = hval-++ h⋆ ∷ hvals-++ hs⋆

stack-++ : ∀ {ψ₁ ψ₂ ψ₂⁺ sp σ} →
              ψ₁ , ψ₂ ⊢ sp of σ stack →
              ψ₁ , ψ₂ ++ ψ₂⁺ ⊢ sp of σ stack
stack-++ [] = []
stack-++ (w⋆ ∷ sp⋆) = wval-++ w⋆ ∷ stack-++ sp⋆

regs-++ : ∀ {n} {ψ₁ ψ₂ ψ₂⁺} {regs : Vec WordValue n} {τs} →
            AllZipᵥ (λ w τ → ψ₁ , ψ₂ ⊢ w of τ wval) regs τs →
            AllZipᵥ (λ w τ → ψ₁ , ψ₂ ++ ψ₂⁺ ⊢ w of τ wval) regs τs
regs-++ [] = []
regs-++ (w⋆ ∷ regs⋆) = wval-++ w⋆ ∷ regs-++ regs⋆

heap-push : ∀ {ψ₁ H ψ₂ h τ} →
              ψ₁ ⊢ H of ψ₂ heap →
              ψ₁ , ψ₂ ⊢ h of τ hval →
              ψ₁ ⊢ H ∷ʳ h of  ψ₂ ∷ʳ τ heap
heap-push {τ = τₐ} (of-heap hs⋆) h⋆
  with hvals-++ hs⋆ | hval-++ h⋆
... | hs⋆' | h⋆' = of-heap (AllZip-++ hs⋆' (h⋆' ∷ []))
