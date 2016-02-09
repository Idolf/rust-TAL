module Lemmas.HeapSteps where

open import Util
open import Judgments
open import Lemmas.Types
open import Lemmas.TermValidType
open import Lemmas.TermCasting using (wval-cast)
open HighGrammar
open HighSemantics

-- The purpose of this file is prove the step related
-- to store and load.

private
  wval-helper : ∀ {ψ₁ ψ₂ ψ₂' w τ} →
                  [] ⊢ ψ₂' ≤ ψ₂ →
                  ψ₁ , ψ₂  ⊢ w of τ wval →
                  ψ₁ , ψ₂' ⊢ w of τ wval
  wval-helper ψ₂'≤ψ₂ (of-globval l τ'≤τ) = of-globval l τ'≤τ
  wval-helper ψ₂'≤ψ₂ (of-heapval l τ'≤τ)
    with allzip-lookup₂ l ψ₂'≤ψ₂
  ... | τ' , l' , τ''≤τ' = of-heapval l' (≤-trans τ''≤τ' τ'≤τ)
  wval-helper ψ₂'≤ψ₂ of-int = of-int
  wval-helper ψ₂'≤ψ₂ of-ns = of-ns
  wval-helper ψ₂'≤ψ₂ (of-Λ w⋆ θs⋆ subs-Γ Γ₃≤Γ₂) = of-Λ (wval-helper ψ₂'≤ψ₂ w⋆) θs⋆ subs-Γ Γ₃≤Γ₂

  wval⁰-helper : ∀ {ψ₁ ψ₂ ψ₂' w τ⁻} →
                   [] ⊢ ψ₂' ≤ ψ₂ →
                   ψ₁ , ψ₂  ⊢ w of τ⁻ wval⁰ →
                   ψ₁ , ψ₂' ⊢ w of τ⁻ wval⁰
  wval⁰-helper ψ₂'≤ψ₂ (of-uninit τ⋆) = of-uninit τ⋆
  wval⁰-helper ψ₂'≤ψ₂ (of-init w⋆) = of-init (wval-helper ψ₂'≤ψ₂ w⋆)

  hval-helper : ∀ {ψ₁ ψ₂' ψ₂ h τ} →
                  [] ⊢ ψ₂' ≤ ψ₂ →
                  ψ₁ , ψ₂  ⊢ h of τ hval →
                  ψ₁ , ψ₂' ⊢ h of τ hval
  hval-helper ψ₂'≤ψ₂ (of-tuple ws⋆) = of-tuple (AllZip-map (wval⁰-helper ψ₂'≤ψ₂) ws⋆)

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
    = , , here , here , of-init w⋆ ∷ ws⋆ , τ⁻-≤ τ⋆ φ-≤-init ∷ ≤-refl (AllZip-extract→ wval⁰-valid-type ws⋆)
  update-helper₂ (there l) (τ⁻₂≤τ⁻₁ ∷ τs⁻₂≤τs⁻₁) w⋆ (w'⋆ ∷ ws⋆)
    with update-helper₂ l τs⁻₂≤τs⁻₁ w⋆ ws⋆
  ... | ws' , τs⁻₃ , up₁ , up₂ , ws'⋆ , τs⁻₃≤τs⁻₂
    = , , there up₁ , there up₂ , w'⋆ ∷ ws'⋆ , ≤-refl (wval⁰-valid-type w'⋆) ∷ τs⁻₃≤τs⁻₂

  heap-update : ∀ {ψ₁ ψ₂ h τ τ' H labₕ} →
                  ψ₁ , ψ₂ ⊢ h of τ hval →
                  ψ₁ ⊢ H of ψ₂ heap →
                  ψ₂ ↓ labₕ ⇒ τ' →
                  [] ⊢ τ ≤ τ' →
                  ∃₂ λ H' ψ₂' →
                     H  ⟦ labₕ ⟧← h ⇒ H' ×
                     ψ₂ ⟦ labₕ ⟧← τ ⇒ ψ₂' ×
                     ψ₁ ⊢ H' of ψ₂' heap ×
                     [] ⊢ ψ₂' ≤ ψ₂
  heap-update {ψ₁} {ψ₂} {h} {τ} {τ'} h⋆ (of-heap hs⋆) l τ≤τ'
    with help hs⋆ l
    where help : ∀ {hs τs labₕ} →
                   AllZip (λ h τ → ψ₁ , ψ₂ ⊢ h of τ hval) hs τs →
                   τs ↓ labₕ ⇒ τ' →
                   ∃₂ λ hs' τs' →
                     hs ⟦ labₕ ⟧← h ⇒ hs' ×
                     τs ⟦ labₕ ⟧← τ ⇒ τs' ×
                     AllZip (λ h' τ' → ψ₁ , ψ₂ ⊢ h' of τ' hval) hs' τs' ×
                     [] ⊢ τs' ≤ τs
          help (h'⋆ ∷ hs⋆) here = , , here , here , h⋆ ∷ hs⋆ , τ≤τ' ∷ ≤-refl (AllZip-extract→ hval-valid-type hs⋆)
          help (h'⋆ ∷ hs⋆) (there l)
            with help hs⋆ l
          ... | _ , _ , up₁ , up₂ , hs'⋆ , τs'≤τs
            = , , there up₁ , there up₂ , h'⋆ ∷ hs'⋆ , ≤-refl (hval-valid-type h'⋆) ∷ τs'≤τs
  ... | hs' , ψ₂' , up₁ , up₂ , hs'⋆ , ψ₂'≤ψ₂
    = hs' , ψ₂' , up₁ , up₂ , of-heap (AllZip-map (hval-helper ψ₂'≤ψ₂) hs'⋆) , ψ₂'≤ψ₂

  stack-helper : ∀ {ψ₁ ψ₂ ψ₂' S σ} →
                   [] ⊢ ψ₂' ≤ ψ₂ →
                   ψ₁ , ψ₂ ⊢ S of σ stack →
                   ψ₁ , ψ₂' ⊢ S of σ stack
  stack-helper ψ₂'≤ψ₂ [] = []
  stack-helper ψ₂'≤ψ₂ (w⋆ ∷ S⋆) = wval-helper ψ₂'≤ψ₂ w⋆ ∷ stack-helper ψ₂'≤ψ₂ S⋆

  regs-helper : ∀ {ψ₁ ψ₂ n} {regs : Vec WordValue n} {τs} ♯rd {labₕ τ} →
                  [] ⊢ τ Valid →
                  lookup ♯rd regs ≡ heapval labₕ →
                  ψ₂ ↓ labₕ ⇒ τ →
                  AllZipᵥ (λ w τ → ψ₁ , ψ₂ ⊢ w of τ wval) regs τs →
                  AllZipᵥ (λ w τ → ψ₁ , ψ₂ ⊢ w of τ wval) regs (update ♯rd τ τs)
  regs-helper {regs = regs} ♯rd τ⋆ eq l regs⋆
    with allzipᵥ-update ♯rd (of-heapval l (≤-refl τ⋆)) regs⋆
  ... | regs'⋆
    rewrite sym eq
          | []≔-lookup regs ♯rd
    = regs'⋆

  wval-tuple-helper : ∀ {G ψ₁ H ψ₂ w τs⁻} →
                        ⊢ G of ψ₁ globals →
                        ψ₁ ⊢ H of ψ₂ heap →
                        ψ₁ , ψ₂ ⊢ w of tuple τs⁻ wval →
                        ∃₂ λ labₕ ws → ∃ λ τs⁻' →
                          w ≡ heapval labₕ ×
                          H ↓ labₕ ⇒ tuple ws ×
                          ψ₂ ↓ labₕ ⇒ tuple τs⁻' ×
                          AllZip (λ τ⁻' τ⁻ → [] ⊢ τ⁻' ≤ τ⁻) τs⁻' τs⁻ ×
                          AllZip (λ w τ⁻ → ψ₁ , ψ₂ ⊢ w of τ⁻ wval⁰) ws τs⁻'
  wval-tuple-helper (of-globals gs⋆) H⋆ (of-globval l τ≤tuple) with allzip-lookup₂ l gs⋆
  wval-tuple-helper (of-globals gs⋆) H⋆ (of-globval l ()) | _ , l' , of-gval Γ⋆ I⋆
  wval-tuple-helper G⋆ (of-heap hs⋆) (of-heapval l τ≤tuple)
    with allzip-lookup₂ l hs⋆
  wval-tuple-helper G⋆ (of-heap hs⋆) (of-heapval l (tuple-≤ τs'≤τs))
      | tuple ws , l' , of-tuple ws⋆
    = , , , refl , l' , l , τs'≤τs , ws⋆

store-step : ∀ {G ψ₁ H ψ₂ regs sp σ τs ♯rd ♯rs τs⁻₁ τs⁻₂ τ φ i I} →
               ⊢ G of ψ₁ globals →
               ψ₁ ⊢ H of ψ₂ heap →
               ψ₁ , ψ₂ ⊢ sp of σ stack →
               AllZipᵥ (λ w τ → ψ₁ , ψ₂ ⊢ w of τ wval) regs τs →
               lookup ♯rd τs ≡ tuple τs⁻₁ →
               [] ⊢ lookup ♯rs τs ≤ τ →
               τs⁻₁ ↓ i ⇒ (τ , φ) →
               τs⁻₁ ⟦ i ⟧← τ , init ⇒ τs⁻₂ →
               ∃₂ λ H' ψ₂' →
                 ψ₁ ⊢ H' of ψ₂' heap ×
                 ψ₁ , ψ₂' ⊢ register sp regs of registerₐ σ (update ♯rd (tuple τs⁻₂) τs) register ×
                 G ⊢ (H , register sp regs , st ♯rd i ♯rs ~> I) ⇒ (H' , register sp regs , I)
store-step {♯rd = ♯rd} {♯rs} G⋆ H⋆ sp⋆ regs⋆ eq lookup≤τ l up
  with allzipᵥ-lookup ♯rd regs⋆ | wval-cast (allzipᵥ-lookup ♯rs regs⋆) lookup≤τ
... | ♯rd⋆ | ♯rs⋆
  rewrite eq
  with wval-tuple-helper G⋆ H⋆ ♯rd⋆
... | labₕ , ws , τs⁻₂ , eq₁ , l₁ , l₂ , τs⁻₂≤τs⁻₁ , ws⋆
  with update-helper₂ l τs⁻₂≤τs⁻₁ ♯rs⋆ ws⋆
... | ws' , τs⁻₃ , up₁ , up₂ , ws'⋆ , τs⁻₃≤τs⁻₂
  with heap-update (of-tuple ws'⋆) H⋆ l₂ (tuple-≤ τs⁻₃≤τs⁻₂)
... | H' , ψ₂' , up₃ , up₄ , H'⋆ , ψ₂'≤ψ₂
  with regs-helper ♯rd (valid-tuple (≤-valid₁ τs⁻₃≤τs⁻₂)) eq₁ (←-to-↓ up₄) (AllZipᵥ-map (wval-helper ψ₂'≤ψ₂) regs⋆)
... | regs'⋆
  with allzip-update up₂ up (≤-refl (valid-τ⁻ (≤-valid₂ lookup≤τ))) τs⁻₂≤τs⁻₁
... | τs⁻₃≤τs⁻₁'
  = , , H'⋆ , of-register (stack-helper ψ₂'≤ψ₂ sp⋆) (AllZipᵥ-trans wval-cast regs'⋆ (allzipᵥ-update ♯rd (tuple-≤ τs⁻₃≤τs⁻₁') (≤-refl (AllZipᵥ-extract→ wval-valid-type regs⋆)))) , step-st eq₁ l₁ up₁ up₃

load-step : ∀ {G ψ₁ H ψ₂ regs sp σ τs ♯rd ♯rs τs⁻ τ i I} →
              ⊢ G of ψ₁ globals →
              ψ₁ ⊢ H of ψ₂ heap →
              ψ₁ , ψ₂ ⊢ sp of σ stack →
              AllZipᵥ (λ w τ → ψ₁ , ψ₂ ⊢ w of τ wval) regs τs →
              lookup ♯rs τs ≡ tuple τs⁻ →
              τs⁻ ↓ i ⇒ (τ , init) →
              ∃ λ R' →
                  ψ₁ , ψ₂ ⊢ R' of registerₐ σ (update ♯rd τ τs) register ×
                  G ⊢ (H , register sp regs , ld ♯rd ♯rs i ~> I) ⇒ (H , R' , I)
load-step {♯rd = ♯rd} {♯rs} G⋆ H⋆ sp⋆ regs⋆ eq l
  with allzipᵥ-lookup ♯rs regs⋆
... | lookup⋆
  rewrite eq
  with wval-tuple-helper G⋆ H⋆ lookup⋆
... | labₕ , ws , τs⁻ , eq₁ , l₁ , l₂ , τs'≤τs , ws⋆
  with allzip-lookup₂ l τs'≤τs
... | (τ , init) , l₃ , (τ⁻-≤ τ⋆ φ-≤-init)
  with allzip-lookup₂ l₃ ws⋆
... | w , l₄ , of-init w⋆
  = , of-register sp⋆ (allzipᵥ-update ♯rd w⋆ regs⋆) , step-ld eq₁ l₁ l₄
