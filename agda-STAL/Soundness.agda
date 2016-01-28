module Soundness where

open import Util
open import Judgments
open import Lemmas
open import TermSubtyping
open import HeapPush
open import WeakenRight

φ-init-≤ : ∀ {φ} → init ≤φ φ
φ-init-≤ {init} = φ-≤-init
φ-init-≤ {uninit} = φ-≤-uninit

eval-reduction : ∀ {ψ₁ ψ₂ regs σ τs} →
                   [] ⊢ ψ₁ Valid →
                   AllZipᵥ (λ w τ → ψ₁ , ψ₂ ⊢ w of τ wval) regs τs →
                   {v : SmallValue} {τ : Type} →
                   ψ₁ , [] , registerₐ σ τs ⊢ v of τ vval →
                   ψ₁ , ψ₂ ⊢ evalSmallValue regs v of τ wval
eval-reduction ψ₁⋆ regs⋆ {v = reg ♯r} of-reg = allzipᵥ-lookup ♯r regs⋆
eval-reduction ψ₁⋆ regs⋆ (of-globval l) = of-globval l (≤-refl (All-lookup l ψ₁⋆))
eval-reduction ψ₁⋆ regs⋆ of-int = of-int
eval-reduction ψ₁⋆ regs⋆ of-ns = of-ns
eval-reduction ψ₁⋆ regs⋆ {v = Λ Δ₂ ∙ w ⟦ is ⟧} {∀[ .Δ₂ ] Γ₃} (of-Λ {Δ₁ = Δ₁} {Γ₁ = Γ₁} v⋆ is⋆ subs-Γ)
  with eval-reduction ψ₁⋆ regs⋆ v⋆
... | w⋆
  with wval-valid-type w⋆
... | valid-∀ Γ₁⋆
  with valid-weaken Δ₁ Δ₂ [] Γ₁⋆
... | Γ₁'⋆
  rewrite List-++-right-identity Δ₁
        | List-++-right-identity Δ₂
        | weaken-outside-ctx-0 (length Δ₂) Γ₁⋆
        = of-Λ w⋆ is⋆ subs-Γ (≤-refl (valid-subst-many [] is⋆ Γ₁'⋆ subs-Γ))

instantiation-reduction' : ∀ {G ψ₁ ψ₂ w I Δ Γ} →
                             ⊢ G of ψ₁ globals →
                             ψ₁ , ψ₂ ⊢ w of ∀[ Δ ] Γ wval →
                             InstantiateGlobal G w I →
                               ψ₁ , Δ , Γ ⊢ I instructionsequence
instantiation-reduction' {Δ = Δ} (of-globals gs⋆) (of-globval l₁ (∀-≤ Γ≤Γ')) (instantiate-globval l₂)
  rewrite List-++-right-identity Δ
  with allzip-lookup l₂ l₁ gs⋆
... | of-gval Γ⋆' I⋆ = instructionsequence-subtype (globals-valid-type (of-globals gs⋆)) Γ≤Γ' I⋆
instantiation-reduction' {ψ₁ = ψ₁} {I = I} (of-globals gs⋆) (of-Λ {Δ₁ = Δ₁} {Δ₂ = Δ₂} {Γ₁ = Γ₁} w⋆ is⋆ subs-Γ Γ₃≤Γ₂) (instantiate-Λ {I = I'} ig subs-I)
  with instantiation-reduction' (of-globals gs⋆) w⋆ ig
... | I'⋆
  with instructionsequence-subst-many [] Δ₁ Δ₂ (gvals-valid-type gs⋆) is⋆ subs-Γ (instructionsequence-weaken-right Δ₁ Δ₂ I'⋆)
... | I'' , subs-I' , I''⋆
  rewrite subst-unique-many subs-I subs-I'
  = instructionsequence-subtype (gvals-valid-type gs⋆) Γ₃≤Γ₂ I''⋆


-- instantiation-reduction : ∀ {G ψ₁ ψ₂ w I Δ Γ} →
--                             ⊢ G of ψ₁ globals →
--                             ψ₁ , ψ₂ ⊢ w of ∀[ Δ ] Γ wval →
--                             InstantiateGlobal G w I →
--                             ψ₁ , Δ , Γ ⊢ I instructionsequence
-- instantiation-reduction G⋆ w⋆ ig = proj₁ (instantiation-reduction' G⋆ w⋆ ig)

-- update-helper : ∀ {τs⁻₁ τs⁻₂ : List InitType} {i τ φ} →
--                   [] ⊢ τ Valid →
--                   [] ⊢ τs⁻₁ Valid →
--                   τs⁻₁ ↓ i ⇒ (τ , φ) →
--                   τs⁻₁ ⟦ i ⟧← (τ , init) ⇒ τs⁻₂ →
--                   [] ⊢ τs⁻₂ ≤ τs⁻₁
-- update-helper τ⋆ (τ⁻₁⋆ ∷ τs⁻₁⋆) here here = τ⁻-≤ τ⋆ φ-init-≤ ∷ (≤-refl τs⁻₁⋆)
-- update-helper τ⋆ (τ⁻₁⋆ ∷ τs⁻₁⋆) (there l) (there up) = (≤-refl τ⁻₁⋆) ∷ update-helper τ⋆ τs⁻₁⋆ l up

-- wval-helper : ∀ {ψ₁ ψ₂ ψ₂' w τ} →
--                 [] ⊢ ψ₂' ≤ ψ₂ →
--                 ψ₁ , ψ₂ ⊢ w of τ wval →
--                 ψ₁ , ψ₂' ⊢ w of τ wval
-- wval-helper ψ₂'≤ψ₂ (of-globval l τ'≤τ) = of-globval l τ'≤τ
-- wval-helper ψ₂'≤ψ₂ (of-heapval l τ'≤τ)
--   with allzip-lookup₂ l ψ₂'≤ψ₂
-- ... | τ' , l' , τ''≤τ'  = of-heapval l' (≤-trans τ''≤τ' τ'≤τ)
-- wval-helper ψ₂'≤ψ₂ of-int = of-int
-- wval-helper ψ₂'≤ψ₂ of-ns = of-ns
-- wval-helper ψ₂'≤ψ₂ (of-Λ w⋆ is⋆ subs-Γ Γ₃≤Γ₂) = of-Λ (wval-helper ψ₂'≤ψ₂ w⋆) is⋆ subs-Γ Γ₃≤Γ₂

-- wval⁰-helper : ∀ {ψ₁ ψ₂ ψ₂' w τ⁻} →
--                  [] ⊢ ψ₂' ≤ ψ₂ →
--                  ψ₁ , ψ₂ ⊢ w of τ⁻ wval⁰ →
--                  ψ₁ , ψ₂' ⊢ w of τ⁻ wval⁰
-- wval⁰-helper ψ₂'≤ψ₂ (of-uninit τ⋆) = of-uninit τ⋆
-- wval⁰-helper ψ₂'≤ψ₂ (of-init w⋆) = of-init (wval-helper ψ₂'≤ψ₂ w⋆)

-- wvals⁰-helper : ∀ {ψ₁ ψ₂ ψ₂' ws τs⁻} →
--                   [] ⊢ ψ₂' ≤ ψ₂ →
--                   AllZip (λ w τ⁻ → ψ₁ , ψ₂  ⊢ w of τ⁻ wval⁰) ws τs⁻ →
--                   AllZip (λ w τ⁻ → ψ₁ , ψ₂' ⊢ w of τ⁻ wval⁰) ws τs⁻
-- wvals⁰-helper ψ₂'≤ψ₂ [] = []
-- wvals⁰-helper ψ₂'≤ψ₂ (w⋆ ∷ ws⋆) = wval⁰-helper ψ₂'≤ψ₂ w⋆ ∷ wvals⁰-helper ψ₂'≤ψ₂ ws⋆

-- hval-helper : ∀ {ψ₁ ψ₂' ψ₂ h τ} →
--                 [] ⊢ ψ₂' ≤ ψ₂ →
--                 ψ₁ , ψ₂  ⊢ h of τ hval →
--                 ψ₁ , ψ₂' ⊢ h of τ hval
-- hval-helper ψ₂'≤ψ₂ (of-tuple ws⋆) = of-tuple (wvals⁰-helper ψ₂'≤ψ₂ ws⋆)

-- heap-helper₁ : ∀ {ψ₁ ψ₂ hs hs' τs lₕ h τ τ'} →
--                  AllZip (λ h τ → ψ₁ , ψ₂ ⊢ h of τ hval) hs τs →
--                  τs ↓ lₕ ⇒ τ' →
--                  [] ⊢ τ ≤ τ' →
--                  hs  ⟦ lₕ ⟧← h ⇒ hs' →
--                  ∃ λ τs' →
--                      τs ⟦ lₕ ⟧← τ ⇒ τs' ×
--                      [] ⊢ τs' ≤ τs
-- heap-helper₁ (h⋆ ∷ hs⋆) here τ≤τ' here = _ , here , τ≤τ' ∷ ≤-refl (hvals-valid-type hs⋆)
-- heap-helper₁ (h⋆ ∷ hs⋆) (there l) τ≤τ' (there up)
--   with heap-helper₁ hs⋆ l τ≤τ' up
-- ... | ψ₂' , up' , ψ₂'≤ψ₂ = _ , there up' , ≤-refl (hval-valid-type h⋆) ∷ ψ₂'≤ψ₂

-- heap-helper₂ : ∀ {ψ₁ ψ₂' ψ₂ hs τs} →
--                  [] ⊢ ψ₂' ≤ ψ₂ →
--                  AllZip (λ h τ → ψ₁ , ψ₂  ⊢ h of τ hval) hs τs →
--                  AllZip (λ h τ → ψ₁ , ψ₂' ⊢ h of τ hval) hs τs
-- heap-helper₂ ψ₂'≤ψ₂ [] = []
-- heap-helper₂ ψ₂'≤ψ₂ (h⋆ ∷ hs⋆) = hval-helper ψ₂'≤ψ₂ h⋆ ∷ heap-helper₂ ψ₂'≤ψ₂ hs⋆

-- heap-helper : ∀ {ψ₁ H H' ψ₂ lₕ h τ τ'} →
--                 ψ₁ ⊢ H of ψ₂ heap →
--                 ψ₂ ↓ lₕ ⇒ τ' →
--                 [] ⊢ τ ≤ τ' →
--                 ψ₁ , ψ₂ ⊢ h of τ hval →
--                 H  ⟦ lₕ ⟧← h ⇒ H' →
--                 ∃ λ ψ₂' →
--                     ψ₂ ⟦ lₕ ⟧← τ ⇒ ψ₂' ×
--                     [] ⊢ ψ₂' ≤ ψ₂ ×
--                     ψ₁ ⊢ H' of ψ₂' heap
-- heap-helper (of-heap hs⋆) l τ≤τ' h⋆ up₁
--   with heap-helper₁ hs⋆ l τ≤τ' up₁
-- ... | ψ₂' , up₂ , ψ₂'≤ψ₂
--   with heap-helper₂ ψ₂'≤ψ₂ hs⋆
-- ... | hs⋆'
--   with allzip-update up₁ up₂ (hval-helper ψ₂'≤ψ₂ h⋆) hs⋆'
-- ... | hs⋆'' = ψ₂' , up₂ , ψ₂'≤ψ₂ , of-heap hs⋆''

-- stack-helper : ∀ {ψ₁ ψ₂ ψ₂' S σ} →
--                  [] ⊢ ψ₂' ≤ ψ₂ →
--                  ψ₁ , ψ₂ ⊢ S of σ stack →
--                  ψ₁ , ψ₂' ⊢ S of σ stack
-- stack-helper ψ₂'≤ψ₂ [] = []
-- stack-helper ψ₂'≤ψ₂ (w⋆ ∷ S⋆) = wval-helper ψ₂'≤ψ₂ w⋆ ∷ stack-helper ψ₂'≤ψ₂ S⋆

-- regs-helper₁ : ∀ {ψ₁ ψ₂ ψ₂' n} {regs : Vec WordValue n} {τs} →
--                  [] ⊢ ψ₂' ≤ ψ₂ →
--                  AllZipᵥ (λ w τ → ψ₁ , ψ₂  ⊢ w of τ wval) regs τs →
--                  AllZipᵥ (λ w τ → ψ₁ , ψ₂' ⊢ w of τ wval) regs τs
-- regs-helper₁ ψ₂'≤ψ₂ [] = []
-- regs-helper₁ ψ₂'≤ψ₂ (w⋆ ∷ S⋆) = wval-helper ψ₂'≤ψ₂ w⋆ ∷ regs-helper₁ ψ₂'≤ψ₂ S⋆

-- regs-helper₂ : ∀ {ψ₁ ψ₂ n} {regs : Vec WordValue n} {τs} ♯rd {lₕ τ} →
--                  [] ⊢ ψ₂ Valid →
--                  lookup ♯rd regs ≡ heapval lₕ →
--                  ψ₂ ↓ lₕ ⇒ τ →
--                  AllZipᵥ (λ w τ → ψ₁ , ψ₂ ⊢ w of τ wval) regs τs →
--                  AllZipᵥ (λ w τ → ψ₁ , ψ₂ ⊢ w of τ wval) regs (update ♯rd τ τs)
-- regs-helper₂ {regs = ._ ∷ regs} zero ψ₂⋆ refl l (w⋆ ∷ regs⋆) = of-heapval l (≤-refl (All-lookup l ψ₂⋆)) ∷ regs⋆
-- regs-helper₂ (suc ♯rd) ψ₂⋆ eq l (w⋆ ∷ regs⋆) = w⋆ ∷ regs-helper₂ ♯rd ψ₂⋆ eq l regs⋆

-- step-reduction' : ∀ {G ψ₁ H ψ₂ sp regs σ τs Γ₂ I H' R' I'} →
--                     ⊢ G of ψ₁ globals →
--                     ψ₁ ⊢ H of ψ₂ heap →
--                     ψ₁ , ψ₂ ⊢ sp of σ stack →
--                     AllZipᵥ (λ w τ → ψ₁ , ψ₂ ⊢ w of τ wval) regs τs →
--                     {ι : Instruction} →
--                     ψ₁ , [] , registerₐ σ τs ⊢ ι ⇒ Γ₂ instruction →
--                     ψ₁ , [] , Γ₂ ⊢ I instructionsequence →
--                     G ⊢ H , register sp regs , ι ~> I ⇒ H' , R' , I' →
--                     ψ₁ ⊢ (H' , R' , I') programstate
-- step-reduction' G⋆ H⋆ sp⋆ regs⋆ {add ♯rd ♯rs v} (of-add eq₁ v⋆) I⋆ (step-add eq₂ eq₃) = of-programstate H⋆ (of-register sp⋆ (allzipᵥ-update ♯rd of-int regs⋆ )) I⋆
-- step-reduction' G⋆ H⋆ sp⋆ regs⋆ {sub ♯rd ♯rs v} (of-sub eq₁ v⋆) I⋆ (step-sub eq₂ eq₃) = of-programstate H⋆ (of-register sp⋆ (allzipᵥ-update ♯rd of-int regs⋆ )) I⋆
-- step-reduction' G⋆ H⋆ sp⋆ regs⋆ {salloc n} of-salloc I⋆ step-salloc = of-programstate H⋆ (of-register (help n sp⋆) regs⋆) I⋆
--   where help : ∀ {ψ₁ ψ₂ sp σ} n →
--                  ψ₁ , ψ₂ ⊢ sp of σ stack →
--                  ψ₁ , ψ₂ ⊢ replicate n ns ++ sp of stack-append (replicate n ns) σ stack
--         help zero σ⋆ = σ⋆
--         help (suc n) σ⋆ = of-ns ∷ help n σ⋆
-- step-reduction' G⋆ H⋆ sp⋆ regs⋆ (of-sfree drop₁) I⋆ (step-sfree drop₂) = of-programstate H⋆ (of-register (help sp⋆ drop₁ drop₂) regs⋆) I⋆
--   where help : ∀ {ψ₁ ψ₂ sp sp' σ σ' n} →
--                  ψ₁ , ψ₂ ⊢ sp of σ stack →
--                  stack-drop n σ σ' →
--                  Drop n sp sp' →
--                  ψ₁ , ψ₂ ⊢ sp' of σ' stack
--         help sp⋆ here here = sp⋆
--         help (w⋆ ∷ sp⋆) (there drop₁) (there drop₂) = help sp⋆ drop₁ drop₂
-- step-reduction' G⋆ H⋆ sp⋆ regs⋆ {sld ♯rd i} (of-sld l₁) I⋆ (step-sld l₂) = of-programstate H⋆ (of-register sp⋆ (allzipᵥ-update ♯rd (help sp⋆ l₁ l₂) regs⋆ )) I⋆
--   where help : ∀ {ψ₁ ψ₂ sp σ i w τ} →
--                ψ₁ , ψ₂ ⊢ sp of σ stack →
--                stack-lookup i σ τ →
--                sp ↓ i ⇒ w →
--                ψ₁ , ψ₂ ⊢ w of τ wval
--         help (w⋆ ∷ sp⋆) here here = w⋆
--         help (w⋆ ∷ sp⋆) (there l₁) (there l₂) = help sp⋆ l₁ l₂
-- step-reduction' G⋆ H⋆ sp⋆ regs⋆ {sst i ♯rs} (of-sst up₁) I⋆ (step-sst up₂) = of-programstate H⋆ (of-register (help (allzipᵥ-lookup ♯rs regs⋆) sp⋆ up₁ up₂) regs⋆) I⋆
--   where help : ∀ {ψ₁ ψ₂ sp sp' σ σ' i w τ} →
--                  ψ₁ , ψ₂ ⊢ w of τ wval →
--                  ψ₁ , ψ₂ ⊢ sp of σ stack →
--                  stack-update i τ σ σ' →
--                  sp ⟦ i ⟧← w ⇒ sp' →
--                  ψ₁ , ψ₂ ⊢ sp' of σ' stack
--         help w⋆ (w'⋆ ∷ sp⋆) here here = w⋆ ∷ sp⋆
--         help w⋆ (w'⋆ ∷ sp⋆) (there up₁) (there up₂) = w'⋆ ∷ help w⋆ sp⋆ up₁ up₂
-- step-reduction' G⋆ (of-heap hs⋆) sp⋆ regs⋆ {ld ♯rd ♯rs i} (of-ld eq₁ l₁) I⋆ (step-ld eq₂ l₂ l₃)
--   with allzipᵥ-lookup ♯rs regs⋆
-- ... | w⋆
--   rewrite eq₁ | eq₂
--   with w⋆
-- ... | of-heapval l₄ τs≤τs'
--   with ≤tuple⇒≡tuple τs≤τs'
-- ... | τs⁻ , eq₃
--   rewrite eq₃
--   with τs≤τs'
-- ... | tuple-≤ τs≤τs''
--   with allzip-lookup₂ l₁ τs≤τs''
-- ... | (τ , init) , l₁' , τ⁻-≤ τ⋆ φ-≤-init
--   with allzip-lookup l₂ l₄ hs⋆
-- ... | of-tuple ws⋆
--   with allzip-lookup l₃ l₁' ws⋆
-- ... | of-init w⋆'
--   = of-programstate (of-heap hs⋆) (of-register sp⋆ (allzipᵥ-update ♯rd w⋆' regs⋆)) I⋆
-- step-reduction' G⋆ (of-heap hs⋆) sp⋆ regs⋆ {st ♯rd i ♯rs} (of-st eq₁ lookup≤τ l₁ up₁) I⋆ (step-st eq₂ l₂ up₂ up₃)
--   with allzipᵥ-lookup ♯rd regs⋆ | allzipᵥ-lookup ♯rs regs⋆
-- ... | wrd⋆ | wrs⋆
--   rewrite eq₁ | eq₂
--   with wrd⋆
-- ... | of-heapval l₃ τs≤τs'
--   with ≤tuple⇒≡tuple τs≤τs'
-- ... | τs⁻ , eq₃
--   rewrite eq₃
--   with τs≤τs'
-- ... | tuple-≤ τs≤τs''
--   with allzip-lookup₂ l₁ τs≤τs''
-- ... | (τ , φ) , l₁' , τ⁻-≤ τ⋆ φ₁≤φ₂
--   with allzip-lookup l₂ l₃ hs⋆
-- ... | of-tuple ws⋆
--   with allzip-update₂ up₁ (τ⁻-≤ τ⋆ φ-init-≤) τs≤τs''
-- ... | τs'' , up₁' , τswut
--   with allzip-update up₂ up₁' (of-init (wval-subtype wrs⋆ lookup≤τ)) ws⋆
-- ... | wut
--   with heap-helper (of-heap hs⋆) l₃ (tuple-≤ (update-helper τ⋆ (proj₁ (≤-valid τs≤τs'')) l₁' up₁')) (of-tuple wut) up₃
-- ... | ψ₂' , up₄ , ψ₂'≤ψ₂ , H'⋆
--   = {!!}
--   -- = of-programstate H'⋆ (of-register (stack-helper ψ₂'≤ψ₂ sp⋆) (regs-helper₂ ♯rd (proj₁ (≤-valid ψ₂'≤ψ₂)) eq₂ (←-to-↓ up₄) (regs-helper₁ ψ₂'≤ψ₂ regs⋆))) (instructionsequence-subtype (globals-valid-type G⋆) (Γ-≤ (≤-refl (stack-valid-type sp⋆)) (allzipᵥ-update ♯rd (tuple-≤ τswut) (≤-refl (regs-valid-type regs⋆)))) I⋆)
-- step-reduction' {ψ₂ = ψ₂} G⋆ H⋆ sp⋆ regs⋆ {malloc ♯rd τs} (of-malloc τs⋆) I⋆ step-malloc
--   with (of-heapval (↓-length ψ₂ (tuple (map (λ τ → τ , uninit) τs))) (≤-refl (valid-tuple (help τs⋆))))
--   where help : ∀ {τs : List Type} →
--                  All (λ τ → [] ⊢ τ Valid) τs →
--                  All (λ τ⁻ → [] ⊢ τ⁻ Valid) (map (λ τ → τ , uninit) τs)
--         help [] = []
--         help (τ⋆ ∷ τs⋆) = valid-τ⁻ τ⋆ ∷ help τs⋆
-- ... | foo
--   rewrite heap-length H⋆ = of-programstate (heap-push H⋆ (of-tuple (help τs⋆))) (of-register (stack-++ sp⋆) (allzipᵥ-update ♯rd foo (regs-++ regs⋆))) I⋆
--   where help : ∀ {ψ₁ ψ₂ τs} →
--                  All (λ τ → [] ⊢ τ Valid) τs →
--                  AllZip (λ w τ⁻ → ψ₁ , ψ₂ ⊢ w of τ⁻ wval⁰) (map uninit τs) (map (λ τ → τ , uninit) τs)
--         help [] = []
--         help (τ⋆ ∷ τs⋆) = of-uninit τ⋆ ∷ help τs⋆
-- step-reduction' G⋆ H⋆ sp⋆ regs⋆ {mov ♯rd v} (of-mov v⋆) I⋆ step-mov = of-programstate H⋆ (of-register sp⋆ (allzipᵥ-update ♯rd (eval-reduction (globals-valid-type G⋆) regs⋆ v⋆) regs⋆)) I⋆
-- step-reduction' G⋆ H⋆ sp⋆ regs⋆ (of-beq eq₁ v⋆ Γ≤Γ') I⋆ (step-beq₀ eq₂ ig)
--   with instantiation-reduction G⋆ (eval-reduction (globals-valid-type G⋆) regs⋆ v⋆) ig
-- ... | I⋆' = of-programstate H⋆ (of-register sp⋆ regs⋆) (instructionsequence-subtype (globals-valid-type G⋆) Γ≤Γ' I⋆')
-- step-reduction' G⋆ H⋆ sp⋆ regs⋆ (of-beq eq₁ v⋆ Γ≤Γ') I⋆ (step-beq₁ eq₂ eq₃) = of-programstate H⋆ (of-register sp⋆ regs⋆) I⋆

-- step-reduction : ∀ {G P P'} →
--                    ⊢ G , P program →
--                    G ⊢ P ⇒ P' →
--                    ⊢ G , P' program
-- step-reduction (of-program G⋆ (of-programstate H⋆ (of-register sp⋆ regs⋆) (of-~> ι⋆ I⋆))) step
--   = of-program G⋆ (step-reduction' G⋆ H⋆ sp⋆ regs⋆ ι⋆ I⋆ step)
-- step-reduction (of-program G⋆ (of-programstate H⋆ (of-register sp⋆ regs⋆) (of-jmp v⋆ Γ≤Γ'))) (step-jmp ig)
--   with instantiation-reduction G⋆ (eval-reduction (globals-valid-type G⋆) regs⋆ v⋆) ig
-- ... | I⋆' = of-program G⋆ (of-programstate H⋆ (of-register sp⋆ regs⋆) (instructionsequence-subtype (globals-valid-type G⋆) Γ≤Γ' I⋆'))
