module Lemmas.HeapUpdate where

open import Util
open import Judgments
open import Lemmas.Types
open import Lemmas.Terms
open HighGrammar

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

update-helper₂ : ∀ {ψ₁ ψ₂ τs⁻₁ τs⁻₂ ws i w τ φ} →
                   τs⁻₁ ↓ i ⇒ (τ , φ) →
                   [] ⊢ τs⁻₂ ≤ τs⁻₁ →
                   ψ₁ , ψ₂ ⊢ w of τ wval →
                   AllZip (λ w τ⁻ → ψ₁ , ψ₂ ⊢ w of τ⁻ wval⁰) ws τs⁻₂ →
                   ∃₂ λ ws' τs⁻₃ →
                      ws   ⟦ i ⟧← w ⇒ ws' ×
                      τs⁻₂ ⟦ i ⟧← (τ , init) ⇒ τs⁻₃ ×
                      AllZip (λ w τ⁻ → ψ₁ , ψ₂ ⊢ w of τ⁻ wval⁰) ws' τs⁻₃ ×
                      [] ⊢ τs⁻₃ ≤ τs⁻₂
update-helper₂ here (τ⁻-≤ τ⋆ φ₂≤φ₁ ∷ τs⁻₂≤τs⁻₁) w⋆ (w'⋆ ∷ ws⋆)
  = _ , _ , here , here , of-init w⋆ ∷ ws⋆ , τ⁻-≤ τ⋆ φ-init-≤ ∷ ≤-refl (wvals⁰-valid-type ws⋆)
update-helper₂ (there l) (τ⁻₂≤τ⁻₁ ∷ τs⁻₂≤τs⁻₁) w⋆ (w'⋆ ∷ ws⋆)
  with update-helper₂ l τs⁻₂≤τs⁻₁ w⋆ ws⋆
... | ws' , τs⁻₃ , up₁ , up₂ , ws'⋆ , τs⁻₃≤τs⁻₂
  = _ , _ , there up₁ , there up₂ , w'⋆ ∷ ws'⋆ , ≤-refl (wval⁰-valid-type w'⋆) ∷ τs⁻₃≤τs⁻₂

update-helper₃ : ∀ {τs⁻₁ τs⁻₁' τs⁻₂ τs⁻₂' : List InitType} {i τ} →
                   [] ⊢ τ Valid →
                   [] ⊢ τs⁻₁ ≤ τs⁻₂ →
                   τs⁻₁ ⟦ i ⟧← (τ , init) ⇒ τs⁻₁' →
                   τs⁻₂ ⟦ i ⟧← (τ , init) ⇒ τs⁻₂' →
                   [] ⊢ τs⁻₁' ≤ τs⁻₂'
update-helper₃ τ⋆ (τ⁻₁≤τ⁻₂ ∷ τs⁻₁≤τs⁻₂) here here = τ⁻-≤ τ⋆ φ-≤-init ∷ τs⁻₁≤τs⁻₂
update-helper₃ τ⋆ (τ⁻₁≤τ⁻₂ ∷ τs⁻₁≤τs⁻₂) (there up₁) (there up₂)
  = τ⁻₁≤τ⁻₂ ∷ update-helper₃ τ⋆ τs⁻₁≤τs⁻₂ up₁ up₂

wval-helper : ∀ {ψ₁ ψ₂ ψ₂' w τ} →
                [] ⊢ ψ₂' ≤ ψ₂ →
                ψ₁ , ψ₂ ⊢ w of τ wval →
                ψ₁ , ψ₂' ⊢ w of τ wval
wval-helper ψ₂'≤ψ₂ (of-globval l τ'≤τ) = of-globval l τ'≤τ
wval-helper ψ₂'≤ψ₂ (of-heapval l τ'≤τ)
  with allzip-lookup₂ l ψ₂'≤ψ₂
... | τ' , l' , τ''≤τ' = of-heapval l' (≤-trans τ''≤τ' τ'≤τ)
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

heap-helper₁ : ∀ {ψ₁ ψ₂ hs τs lₕ h τ τ'} →
                 ψ₁ , ψ₂ ⊢ h of τ hval →
                 AllZip (λ h τ → ψ₁ , ψ₂ ⊢ h of τ hval) hs τs →
                 τs ↓ lₕ ⇒ τ' →
                 [] ⊢ τ ≤ τ' →
                 ∃₂ λ hs' τs' →
                   hs ⟦ lₕ ⟧← h ⇒ hs' ×
                   τs ⟦ lₕ ⟧← τ ⇒ τs' ×
                   AllZip (λ h' τ' → ψ₁ , ψ₂ ⊢ h' of τ' hval) hs' τs' ×
                   [] ⊢ τs' ≤ τs
heap-helper₁ h⋆ (h'⋆ ∷ hs⋆) here τ≤τ'
  = _ , _ , here , here , h⋆ ∷ hs⋆ , τ≤τ' ∷ ≤-refl (hvals-valid-type hs⋆)
heap-helper₁ h⋆ (h'⋆ ∷ hs⋆) (there l) τ≤τ'
  with heap-helper₁ h⋆ hs⋆ l τ≤τ'
... | hs' , τs' , up₁ , up₂ , hs'⋆ , τs'≤τs
  = _ , _ , there up₁ , there up₂ , h'⋆ ∷ hs'⋆ , ≤-refl (hval-valid-type h'⋆) ∷ τs'≤τs

heap-helper₂ : ∀ {ψ₁ ψ₂' ψ₂ hs τs} →
                 [] ⊢ ψ₂' ≤ ψ₂ →
                 AllZip (λ h τ → ψ₁ , ψ₂  ⊢ h of τ hval) hs τs →
                 AllZip (λ h τ → ψ₁ , ψ₂' ⊢ h of τ hval) hs τs
heap-helper₂ ψ₂'≤ψ₂ [] = []
heap-helper₂ ψ₂'≤ψ₂ (h⋆ ∷ hs⋆) = hval-helper ψ₂'≤ψ₂ h⋆ ∷ heap-helper₂ ψ₂'≤ψ₂ hs⋆

heap-helper : ∀ {ψ₁ H ψ₂ lₕ h τ τ'} →
                ψ₁ , ψ₂ ⊢ h of τ hval →
                ψ₁ ⊢ H of ψ₂ heap →
                ψ₂ ↓ lₕ ⇒ τ' →
                [] ⊢ τ ≤ τ' →
                ∃₂ λ H' ψ₂' →
                   H  ⟦ lₕ ⟧← h ⇒ H' ×
                   ψ₂ ⟦ lₕ ⟧← τ ⇒ ψ₂' ×
                   ψ₁ ⊢ H' of ψ₂' heap ×
                   [] ⊢ ψ₂' ≤ ψ₂
heap-helper h⋆ (of-heap hs⋆) l τ≤τ'
  with heap-helper₁ h⋆ hs⋆ l τ≤τ'
... | hs' , ψ₂' , up₁ , up₂ , hs'⋆ , ψ₂'≤ψ₂
  = hs' , ψ₂' , up₁ , up₂ , of-heap (heap-helper₂ ψ₂'≤ψ₂ hs'⋆) , ψ₂'≤ψ₂

stack-helper : ∀ {ψ₁ ψ₂ ψ₂' S σ} →
                 [] ⊢ ψ₂' ≤ ψ₂ →
                 ψ₁ , ψ₂ ⊢ S of σ stack →
                 ψ₁ , ψ₂' ⊢ S of σ stack
stack-helper ψ₂'≤ψ₂ [] = []
stack-helper ψ₂'≤ψ₂ (w⋆ ∷ S⋆) = wval-helper ψ₂'≤ψ₂ w⋆ ∷ stack-helper ψ₂'≤ψ₂ S⋆

regs-helper : ∀ {ψ₁ ψ₂ ψ₂' n} {regs : Vec WordValue n} {τs} →
                [] ⊢ ψ₂' ≤ ψ₂ →
                AllZipᵥ (λ w τ → ψ₁ , ψ₂  ⊢ w of τ wval) regs τs →
                AllZipᵥ (λ w τ → ψ₁ , ψ₂' ⊢ w of τ wval) regs τs
regs-helper ψ₂'≤ψ₂ [] = []
regs-helper ψ₂'≤ψ₂ (w⋆ ∷ S⋆) = wval-helper ψ₂'≤ψ₂ w⋆ ∷ regs-helper ψ₂'≤ψ₂ S⋆

regs-helper₂ : ∀ {ψ₁ ψ₂ n} {regs : Vec WordValue n} {τs} ♯rd {labₕ τ} →
                 [] ⊢ ψ₂ Valid →
                 lookup ♯rd regs ≡ heapval labₕ →
                 ψ₂ ↓ labₕ ⇒ τ →
                 AllZipᵥ (λ w τ → ψ₁ , ψ₂ ⊢ w of τ wval) regs τs →
                 AllZipᵥ (λ w τ → ψ₁ , ψ₂ ⊢ w of τ wval) regs (update ♯rd τ τs)
regs-helper₂ {regs = ._ ∷ regs} zero ψ₂⋆ refl l (w⋆ ∷ regs⋆) = of-heapval l (≤-refl (All-lookup l ψ₂⋆)) ∷ regs⋆
regs-helper₂ (suc ♯rd) ψ₂⋆ eq l (w⋆ ∷ regs⋆) = w⋆ ∷ regs-helper₂ ♯rd ψ₂⋆ eq l regs⋆
