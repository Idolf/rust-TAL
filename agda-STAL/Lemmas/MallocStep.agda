module Lemmas.MallocStep where

open import Util
open import Judgments
open import Lemmas.Types using (≤-refl)
open HighGrammar

-- The purpose of this file is prove the step related
-- to malloc.

private
  wval-++ : ∀ {ψ₁ ψ₂ ψ₂⁺ w τ} →
              ψ₁ , ψ₂ ⊢ w of τ wval →
              ψ₁ , ψ₂ ++ ψ₂⁺ ⊢ w of τ wval
  wval-++ (of-globval l lookup≤τ) = of-globval l lookup≤τ
  wval-++ {ψ₂⁺ = ψ₂⁺} (of-heapval l lookup≤τ) = of-heapval (↓-add-right ψ₂⁺ l) lookup≤τ
  wval-++ of-int = of-int
  wval-++ of-ns = of-ns
  wval-++ (of-Λ w⋆ θs⋆ subs-Γ Γ₃≤Γ₂) = of-Λ (wval-++ w⋆) θs⋆ subs-Γ Γ₃≤Γ₂

  wval⁰-++ : ∀ {ψ₁ ψ₂ ψ₂⁺ w τ⁻} →
               ψ₁ , ψ₂ ⊢ w of τ⁻ wval⁰ →
               ψ₁ , ψ₂ ++ ψ₂⁺ ⊢ w of τ⁻ wval⁰
  wval⁰-++ (of-uninit τ⋆) = of-uninit τ⋆
  wval⁰-++ (of-init w⋆) = of-init (wval-++ w⋆)

  hval-++ : ∀ {ψ₁ ψ₂ ψ₂⁺ h τ} →
              ψ₁ , ψ₂ ⊢ h of τ hval →
              ψ₁ , ψ₂ ++ ψ₂⁺ ⊢ h of τ hval
  hval-++ (of-tuple eqs ws⋆) = of-tuple eqs (AllZip-map wval⁰-++ ws⋆)

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

  map-uninit-helper : ∀ {ψ₁ ψ₂ τs} →
                        [] ⊢ τs Valid →
                        AllZip (λ w τ → ψ₁ , ψ₂ ⊢ w of τ wval⁰) (replicate (length τs) uninit) (map (λ τ → τ , uninit) τs)
  map-uninit-helper [] = []
  map-uninit-helper (τ⋆ ∷ τs⋆) = of-uninit τ⋆ ∷ map-uninit-helper τs⋆

  map-uninit-helper₁ : ∀ τs →
                         AllZip {A = Type} {B = InitType} (λ { τ (τ' , φ) → τ ≡ τ' }) τs (map (λ τ → τ , uninit) τs)
  map-uninit-helper₁ [] = []
  map-uninit-helper₁ (τ ∷ τs) = refl ∷ map-uninit-helper₁ τs

malloc-step : ∀ {ψ₁ H ψ₂ τs τs⁻ sp regs Γ} ♯rd →
                {{_ : τs⁻ ≡ map (λ τ → τ , uninit) τs}} →
                ψ₁ ⊢ H of ψ₂ heap →
                [] ⊢ τs Valid →
                ψ₁ , ψ₂ ⊢ register sp regs of Γ register →
                ψ₁ ⊢ H ∷ʳ tuple τs (replicate (length τs) uninit) of ψ₂ ∷ʳ tuple τs⁻ heap ×
                ψ₁ , ψ₂ ∷ʳ tuple τs⁻ ⊢ register sp (update ♯rd (heapval (length H)) regs) of update-regs ♯rd (tuple τs⁻) Γ register
malloc-step {ψ₂ = ψ₂} {τs} ♯rd {{refl}} (of-heap hs⋆) τs⋆ (of-register sp⋆ regs⋆)
  with of-heapval (↓-length ψ₂ _) (≤-refl (valid-tuple (All-map' valid-τ⁻ τs⋆)))
... | h⋆
  with heap-push (of-heap hs⋆) (of-tuple (map-uninit-helper₁ τs) (map-uninit-helper τs⋆))
... | H'⋆
  rewrite sym (AllZip-length hs⋆)
  = H'⋆ , of-register (stack-++ sp⋆) (allzipᵥ-update ♯rd h⋆ (AllZipᵥ-map wval-++ regs⋆))
