module HeapUpdate where

open import Util
open import Judgments
open import Lemmas

φ-init-≤ : ∀ {φ} → init ≤φ φ
φ-init-≤ {init} = φ-≤-init
φ-init-≤ {uninit} = φ-≤-uninit


update-helper : ∀ {τs⁻₁ τs⁻₂ : List InitType} {i τ φ} →
                  [] ⊢ τ Valid →
                  [] ⊢ τs⁻₁ Valid →
                  τs⁻₁ ↓ i ⇒ (τ , φ) →
                  τs⁻₁ ⟦ i ⟧← (τ , init) ⇒ τs⁻₂ →
                  [] ⊢ τs⁻₂ ≤ τs⁻₁
update-helper τ⋆ (τ⁻₁⋆ ∷ τs⁻₁⋆) here here = τ⁻-≤ τ⋆ φ-init-≤ ∷ (≤-refl τs⁻₁⋆)
update-helper τ⋆ (τ⁻₁⋆ ∷ τs⁻₁⋆) (there l) (there up) = (≤-refl τ⁻₁⋆) ∷ update-helper τ⋆ τs⁻₁⋆ l up

wval-helper : ∀ {ψ₁ ψ₂ ψ₂' w τ} →
                [] ⊢ ψ₂' ≤ ψ₂ →
                ψ₁ , ψ₂ ⊢ w of τ wval →
                ψ₁ , ψ₂' ⊢ w of τ wval
wval-helper ψ₂'≤ψ₂ (of-globval l τ'≤τ) = of-globval l τ'≤τ
wval-helper ψ₂'≤ψ₂ (of-heapval l τ'≤τ)
  with allzip-lookup₂ l ψ₂'≤ψ₂
... | τ' , l' , τ''≤τ'  = of-heapval l' (≤-trans τ''≤τ' τ'≤τ)
wval-helper ψ₂'≤ψ₂ of-int = of-int
wval-helper ψ₂'≤ψ₂ of-ns = of-ns
wval-helper ψ₂'≤ψ₂ (of-Λ w⋆ is⋆ subs-Γ Γ₃≤Γ₂) = of-Λ (wval-helper ψ₂'≤ψ₂ w⋆) is⋆ subs-Γ Γ₃≤Γ₂

wval⁰-helper : ∀ {ψ₁ ψ₂ ψ₂' w τ⁻} →
                 [] ⊢ ψ₂' ≤ ψ₂ →
                 ψ₁ , ψ₂ ⊢ w of τ⁻ wval⁰ →
                 ψ₁ , ψ₂' ⊢ w of τ⁻ wval⁰
wval⁰-helper ψ₂'≤ψ₂ (of-uninit τ⋆) = of-uninit τ⋆
wval⁰-helper ψ₂'≤ψ₂ (of-init w⋆) = of-init (wval-helper ψ₂'≤ψ₂ w⋆)

wvals⁰-helper : ∀ {ψ₁ ψ₂ ψ₂' ws τs⁻} →
                  [] ⊢ ψ₂' ≤ ψ₂ →
                  AllZip (λ w τ⁻ → ψ₁ , ψ₂  ⊢ w of τ⁻ wval⁰) ws τs⁻ →
                  AllZip (λ w τ⁻ → ψ₁ , ψ₂' ⊢ w of τ⁻ wval⁰) ws τs⁻
wvals⁰-helper ψ₂'≤ψ₂ [] = []
wvals⁰-helper ψ₂'≤ψ₂ (w⋆ ∷ ws⋆) = wval⁰-helper ψ₂'≤ψ₂ w⋆ ∷ wvals⁰-helper ψ₂'≤ψ₂ ws⋆

hval-helper : ∀ {ψ₁ ψ₂' ψ₂ h τ} →
                [] ⊢ ψ₂' ≤ ψ₂ →
                ψ₁ , ψ₂  ⊢ h of τ hval →
                ψ₁ , ψ₂' ⊢ h of τ hval
hval-helper ψ₂'≤ψ₂ (of-tuple ws⋆) = of-tuple (wvals⁰-helper ψ₂'≤ψ₂ ws⋆)

heap-helper₁ : ∀ {ψ₁ ψ₂ hs hs' τs lₕ h τ τ'} →
                 AllZip (λ h τ → ψ₁ , ψ₂ ⊢ h of τ hval) hs τs →
                 τs ↓ lₕ ⇒ τ' →
                 [] ⊢ τ ≤ τ' →
                 hs  ⟦ lₕ ⟧← h ⇒ hs' →
                 ∃ λ τs' →
                     τs ⟦ lₕ ⟧← τ ⇒ τs' ×
                     [] ⊢ τs' ≤ τs
heap-helper₁ (h⋆ ∷ hs⋆) here τ≤τ' here = _ , here , τ≤τ' ∷ ≤-refl (hvals-valid-type hs⋆)
heap-helper₁ (h⋆ ∷ hs⋆) (there l) τ≤τ' (there up)
  with heap-helper₁ hs⋆ l τ≤τ' up
... | ψ₂' , up' , ψ₂'≤ψ₂ = _ , there up' , ≤-refl (hval-valid-type h⋆) ∷ ψ₂'≤ψ₂

heap-helper₂ : ∀ {ψ₁ ψ₂' ψ₂ hs τs} →
                 [] ⊢ ψ₂' ≤ ψ₂ →
                 AllZip (λ h τ → ψ₁ , ψ₂  ⊢ h of τ hval) hs τs →
                 AllZip (λ h τ → ψ₁ , ψ₂' ⊢ h of τ hval) hs τs
heap-helper₂ ψ₂'≤ψ₂ [] = []
heap-helper₂ ψ₂'≤ψ₂ (h⋆ ∷ hs⋆) = hval-helper ψ₂'≤ψ₂ h⋆ ∷ heap-helper₂ ψ₂'≤ψ₂ hs⋆

heap-helper : ∀ {ψ₁ H H' ψ₂ lₕ h τ τ'} →
                ψ₁ ⊢ H of ψ₂ heap →
                ψ₂ ↓ lₕ ⇒ τ' →
                [] ⊢ τ ≤ τ' →
                ψ₁ , ψ₂ ⊢ h of τ hval →
                H  ⟦ lₕ ⟧← h ⇒ H' →
                ∃ λ ψ₂' →
                    ψ₂ ⟦ lₕ ⟧← τ ⇒ ψ₂' ×
                    [] ⊢ ψ₂' ≤ ψ₂ ×
                    ψ₁ ⊢ H' of ψ₂' heap
heap-helper (of-heap hs⋆) l τ≤τ' h⋆ up₁
  with heap-helper₁ hs⋆ l τ≤τ' up₁
... | ψ₂' , up₂ , ψ₂'≤ψ₂
  with heap-helper₂ ψ₂'≤ψ₂ hs⋆
... | hs⋆'
  with allzip-update up₁ up₂ (hval-helper ψ₂'≤ψ₂ h⋆) hs⋆'
... | hs⋆'' = ψ₂' , up₂ , ψ₂'≤ψ₂ , of-heap hs⋆''

stack-helper : ∀ {ψ₁ ψ₂ ψ₂' S σ} →
                 [] ⊢ ψ₂' ≤ ψ₂ →
                 ψ₁ , ψ₂ ⊢ S of σ stack →
                 ψ₁ , ψ₂' ⊢ S of σ stack
stack-helper ψ₂'≤ψ₂ [] = []
stack-helper ψ₂'≤ψ₂ (w⋆ ∷ S⋆) = wval-helper ψ₂'≤ψ₂ w⋆ ∷ stack-helper ψ₂'≤ψ₂ S⋆
