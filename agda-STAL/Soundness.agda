module Soundness where

open import Util
open import Judgments
open import Lemmas
open import TermSubtyping
open import HeapPush
open import HeapUpdate
open import WeakenRight

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

instantiation-progress : ∀ {G ψ₁ H ψ₂ w Δ Γ} →
                             ⊢ G of ψ₁ globals →
                             ψ₁ ⊢ H of ψ₂ heap →
                             ψ₁ , ψ₂ ⊢ w of ∀[ Δ ] Γ wval →
                             ∃ λ I →
                               InstantiateGlobal G w I ×
                               ψ₁ , Δ , Γ ⊢ I instructionsequence
instantiation-progress (of-globals gs⋆) H⋆ (of-globval l τ≤τ')
  with allzip-lookup₂ l gs⋆
instantiation-progress (of-globals gs⋆) H⋆ (of-globval l (∀-≤ Γ≤Γ'))
  | code[ Δ ] Γ ∙ I , l' , of-gval Γ⋆ I⋆
  rewrite List-++-right-identity Δ
    = _ , instantiate-globval l' , instructionsequence-subtype (gvals-valid-type gs⋆) Γ≤Γ' I⋆
instantiation-progress G⋆ (of-heap hs⋆) (of-heapval l τ≤τ')
  with allzip-lookup₂ l hs⋆
... | tuple ws , l' , of-tuple ws⋆
  with τ≤τ'
... | ()
instantiation-progress G⋆ H⋆ (of-Λ {Δ₁ = Δ₁} {Δ₂} w⋆ is⋆ subs-Γ Γ≤Γ')
  with instantiation-progress G⋆ H⋆ w⋆
... | I , ig , I⋆
  with instructionsequence-subst-many [] Δ₁ Δ₂ (globals-valid-type G⋆) is⋆ subs-Γ (instructionsequence-weaken-right Δ₁ Δ₂ I⋆)
... | I' , subs-I , I'⋆
  = I' , instantiate-Λ ig subs-I , instructionsequence-subtype (globals-valid-type G⋆) Γ≤Γ' I'⋆

private
  wval-int-helper : ∀ {G ψ₁ H ψ₂ w} →
                      ⊢ G of ψ₁ globals →
                      ψ₁ ⊢ H of ψ₂ heap →
                      ψ₁ , ψ₂ ⊢ w of int wval →
                      ∃ λ n →
                        w ≡ int n
  wval-int-helper (of-globals gs⋆) H⋆ (of-globval l int-≤)
    with allzip-lookup₂ l gs⋆
  ... | g , l' , ()
  wval-int-helper G⋆ (of-heap hs⋆) (of-heapval l int-≤)
    with allzip-lookup₂ l hs⋆
  ... | h , l' , ()
  wval-int-helper G⋆ H⋆ of-int = _ , refl

  wval-tuple-helper : ∀ {G ψ₁ H ψ₂ w τs⁻} →
                        ⊢ G of ψ₁ globals →
                        ψ₁ ⊢ H of ψ₂ heap →
                        ψ₁ , ψ₂ ⊢ w of tuple τs⁻ wval →
                        ∃₂ λ lₕ ws → ∃ λ τs⁻' →
                          w ≡ heapval lₕ ×
                          H ↓ lₕ ⇒ tuple ws ×
                          ψ₂ ↓ lₕ ⇒ tuple τs⁻' ×
                          AllZip (λ τ⁻' τ⁻ → [] ⊢ τ⁻' ≤ τ⁻) τs⁻' τs⁻ ×
                          AllZip (λ w τ⁻ → ψ₁ , ψ₂ ⊢ w of τ⁻ wval⁰) ws τs⁻'
  wval-tuple-helper (of-globals gs⋆) H⋆ (of-globval l τ≤tuple) with allzip-lookup₂ l gs⋆
  wval-tuple-helper (of-globals gs⋆) H⋆ (of-globval l ()) | _ , l' , of-gval Γ⋆ I⋆
  wval-tuple-helper G⋆ (of-heap hs⋆) (of-heapval l τ≤tuple)
    with allzip-lookup₂ l hs⋆
  wval-tuple-helper G⋆ (of-heap hs⋆) (of-heapval l (tuple-≤ τs'≤τs))
      | tuple ws , l' , of-tuple ws⋆
    = _ , _ , _ , refl , l' , l , τs'≤τs , ws⋆

  vval-helper' : ∀ {♯r ψ₁ τ σ τs} →
                   ψ₁ , [] , registerₐ σ τs ⊢ reg ♯r of τ vval →
                   lookup ♯r τs ≡ τ
  vval-helper' of-reg = refl

  vval-int-helper : ∀ {G ψ₁ H ψ₂ regs σ τs v} →
                      ⊢ G of ψ₁ globals →
                      ψ₁ ⊢ H of ψ₂ heap →
                      AllZipᵥ (λ w τ → ψ₁ , ψ₂ ⊢ w of τ wval) regs τs →
                      ψ₁ , [] , registerₐ σ τs ⊢ v of int vval →
                      ∃ λ n →
                        evalSmallValue regs v ≡ int n
  vval-int-helper {v = reg ♯r} G⋆ H⋆ regs⋆ v⋆
    with allzipᵥ-lookup ♯r regs⋆
  ... | lookup⋆
    rewrite vval-helper' v⋆
    = wval-int-helper G⋆ H⋆ lookup⋆
  vval-int-helper {v = globval _} (of-globals gs⋆) H⋆ regs⋆ (of-globval l)
    with allzip-lookup₂ l gs⋆
  ... | g , l' , ()
  vval-int-helper {v = int n} G⋆ H⋆ regs⋆ v⋆ = n , refl
  vval-int-helper {v = ns} G⋆ H⋆ regs⋆ ()
  vval-int-helper {v = uninit x} G⋆ H⋆ regs⋆ ()
  vval-int-helper {v = Λ Δ ∙ v ⟦ is ⟧} G⋆ H⋆ regs⋆ ()

  replicate-helper : ∀ {ψ₁ ψ₂ sp σ} n →
                       ψ₁ , ψ₂ ⊢ sp of σ stack →
                       ψ₁ , ψ₂ ⊢ replicate n ns ++ sp of stack-append (replicate n ns) σ stack
  replicate-helper zero sp⋆ = sp⋆
  replicate-helper (suc n) sp⋆ = of-ns ∷ replicate-helper n sp⋆

  drop-helper : ∀ {ψ₁ ψ₂ sp σ σ' n} →
                       ψ₁ , ψ₂ ⊢ sp of σ stack →
                       stack-drop n σ σ' →
                       ∃ λ sp' →
                         ψ₁ , ψ₂ ⊢ sp' of σ' stack ×
                         Drop n sp sp'
  drop-helper σ⋆ here = _ , σ⋆ , here
  drop-helper (τ⋆ ∷ σ⋆) (there drop)
    with drop-helper σ⋆ drop
  ... | sp' , sp'⋆ , drop'
    = sp' , sp'⋆ , there drop'

  map-uninit-helper : ∀ {ψ₁ ψ₂ τs} →
                        [] ⊢ τs Valid →
                        AllZip (λ w τ → ψ₁ , ψ₂ ⊢ w of τ wval⁰) (map uninit τs) (map (λ τ → τ , uninit) τs)
  map-uninit-helper [] = []
  map-uninit-helper (τ⋆ ∷ τs⋆) = of-uninit τ⋆ ∷ map-uninit-helper τs⋆

  map-uninit-helper₂ : ∀ {τs} →
                         [] ⊢ τs Valid →
                         [] ⊢ map (λ τ → τ , uninit) τs Valid
  map-uninit-helper₂ [] = []
  map-uninit-helper₂ (τ⋆ ∷ τs⋆) = valid-τ⁻ τ⋆ ∷ map-uninit-helper₂ τs⋆

  stack-lookup-helper : ∀ {ψ₁ ψ₂ sp σ i τ} →
                          ψ₁ , ψ₂ ⊢ sp of σ stack →
                          stack-lookup i σ τ →
                          ∃ λ w →
                            sp ↓ i ⇒ w ×
                            ψ₁ , ψ₂ ⊢ w of τ wval
  stack-lookup-helper (w⋆ ∷ sp⋆) here = _ , here , w⋆
  stack-lookup-helper (w⋆ ∷ sp⋆) (there l)
    with stack-lookup-helper sp⋆ l
  ... | w' , l' , w'⋆
    = _ , there l' , w'⋆

  stack-update-helper : ∀ {ψ₁ ψ₂ sp σ σ' i w τ} →
                          ψ₁ , ψ₂ ⊢ w of τ wval →
                          ψ₁ , ψ₂ ⊢ sp of σ stack →
                          stack-update i τ σ σ' →
                          ∃ λ sp' →
                            sp ⟦ i ⟧← w ⇒ sp' ×
                            ψ₁ , ψ₂ ⊢ sp' of σ' stack
  stack-update-helper w⋆ (w'⋆ ∷ sp⋆) here = _ , here , w⋆ ∷ sp⋆
  stack-update-helper w⋆ (w'⋆ ∷ sp⋆) (there l)
    with stack-update-helper w⋆ sp⋆ l
  ... | sp' , up' , sp'⋆
    = _ , there up' , w'⋆ ∷ sp'⋆


step-progress' : ∀ {G ψ₁ H ψ₂ R Γ I} →
                   ⊢ G of ψ₁ globals →
                   ψ₁ ⊢ H of ψ₂ heap →
                   ψ₁ , ψ₂ ⊢ R of Γ register →
                   ψ₁ , [] , Γ ⊢ I instructionsequence →
                   ∃₂ λ H' ψ₂' → ∃₂ λ R' Γ' → ∃ λ I' →
                      ψ₁ ⊢ H' of ψ₂' heap ×
                      ψ₁ , ψ₂' ⊢ R' of Γ' register ×
                      ψ₁ , [] , Γ' ⊢ I' instructionsequence ×
                      G ⊢ (H , R , I) ⇒ (H' , R' , I')
step-progress' {I = add ♯rd ♯rs v ~> I} G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> (of-add eq v⋆) I⋆)
  with allzipᵥ-lookup ♯rs regs⋆
... | lookup⋆
  rewrite eq
  with vval-int-helper G⋆ H⋆ regs⋆ v⋆
... | n' , eq₁
  with wval-int-helper G⋆ H⋆ lookup⋆
... | n , eq₂
  = _ , _ , _ , _ , I , H⋆ , of-register sp⋆ (allzipᵥ-update ♯rd of-int regs⋆) , I⋆ , step-add eq₁ eq₂
step-progress' {I = sub ♯rd ♯rs v ~> I} G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> (of-sub eq v⋆) I⋆)
  with allzipᵥ-lookup ♯rs regs⋆
... | lookup⋆
  rewrite eq
  with vval-int-helper G⋆ H⋆ regs⋆ v⋆
... | n' , eq₁
  with wval-int-helper G⋆ H⋆ lookup⋆
... | n , eq₂
  = _ , _ , _ , _ , I , H⋆ , of-register sp⋆ (allzipᵥ-update ♯rd of-int regs⋆) , I⋆ , step-sub eq₁ eq₂
step-progress' {I = salloc n ~> I} G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> of-salloc I⋆)
  = _ , _ , _ , _ , _ , H⋆ , of-register (replicate-helper n sp⋆) regs⋆ , I⋆ , step-salloc
step-progress' {I = sfree n ~> I} G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> (of-sfree drop) I⋆)
  with drop-helper sp⋆ drop
... | sp' , sp'⋆ , drop'
  = _ , _ , _ , _ , _ , H⋆ , of-register sp'⋆ regs⋆ , I⋆ , step-sfree drop'
step-progress' {I = sld ♯rd i ~> I} G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> (of-sld l) I⋆)
  with stack-lookup-helper sp⋆ l
... | w' , l' , w'⋆
  = _ , _ , _ , _ , _ , H⋆ , of-register sp⋆ (allzipᵥ-update ♯rd w'⋆ regs⋆ ) , I⋆ , step-sld l'
step-progress' {I = sst i ♯rs ~> I} G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> (of-sst up) I⋆)
  with stack-update-helper (allzipᵥ-lookup ♯rs regs⋆) sp⋆ up
... | sp' , up' , sp'⋆
  = _ , _ , _ , _ , _ , H⋆ , of-register sp'⋆ regs⋆ , I⋆ , step-sst up'
step-progress' {I = ld ♯rd ♯rs i ~> I} G⋆ (of-heap hs⋆) (of-register sp⋆ regs⋆) (of-~> (of-ld eq l) I⋆)
  with allzipᵥ-lookup ♯rs regs⋆
... | lookup⋆
  rewrite eq
  with wval-tuple-helper G⋆ (of-heap hs⋆) lookup⋆
... | lₕ , ws , τs⁻ , eq₁ , l₁ , l₂ , τs'≤τs , ws⋆
  with allzip-lookup₂ l τs'≤τs
... | (τ , init) , l₃ , (τ⁻-≤ τ⋆ φ-≤-init)
  with allzip-lookup₂ l₃ ws⋆
... | w , l₄ , of-init w⋆
  = _ , _ , _ , _ , _ , of-heap hs⋆ , of-register sp⋆ (allzipᵥ-update ♯rd w⋆ regs⋆) , I⋆ , step-ld eq₁ l₁ l₄
step-progress' {I = st ♯rd i ♯rs ~> I} G⋆ (of-heap hs⋆) (of-register sp⋆ regs⋆) (of-~> (of-st eq lookup≤τ l up) I⋆)
  with allzipᵥ-lookup ♯rd regs⋆ | allzipᵥ-lookup ♯rs regs⋆
... | ♯rd⋆ | ♯rs⋆
  rewrite eq
  with wval-tuple-helper G⋆ (of-heap hs⋆) ♯rd⋆
... | lₕ , ws , τs⁻ , eq₁ , l₁ , l₂ , τs'≤τs , ws⋆
  with allzip-lookup₂ l τs'≤τs
... | τ' , l' , τ'≤τ
  with heap-helper (of-heap hs⋆) l₂ (tuple-≤ (update-helper {!!} {!!} {!!} {!!})) {!!} {!!}
... | ψ₂' , up'' , ψ₂'≤ψ₂ , H''⋆
  = ?
  -- = _ , _ , _ , _ , _ , {!!} , of-register (stack-helper {!!} sp⋆) {!!} , I⋆ , step-st eq₁ l₁ {!!} {!!}
step-progress' {H = H} {ψ₂ = ψ₂} {I = malloc ♯rd τs ~> I} G⋆ (of-heap hs⋆) (of-register sp⋆ regs⋆) (of-~> (of-malloc τs⋆) I⋆)
  = _ , _ , _ , _ , _ , heap-push (of-heap hs⋆) (of-tuple (map-uninit-helper τs⋆)) , of-register (stack-++ sp⋆) (allzipᵥ-update ♯rd (of-heapval (subst₂ (λ h i → ψ₂ ∷ʳ h ↓ i ⇒ h) refl (sym (AllZip-length hs⋆)) (↓-length ψ₂ (tuple (map (λ τ → τ , uninit) τs)))) (≤-refl (valid-tuple (map-uninit-helper₂ τs⋆)))) (regs-++ regs⋆)) , I⋆ , step-malloc
step-progress' {I = mov ♯rd v ~> I} G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> (of-mov v⋆) I⋆)
  = _ , _ , _ , _ , _ , H⋆ , of-register sp⋆ (allzipᵥ-update ♯rd (eval-reduction (globals-valid-type G⋆) regs⋆ v⋆) regs⋆) , I⋆ , step-mov
step-progress' {I = beq ♯r v ~> I} G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> (of-beq eq v⋆ Γ≤Γ') I⋆)
  with allzipᵥ-lookup ♯r regs⋆
... | lookup⋆
  rewrite eq
  with wval-int-helper G⋆ H⋆ lookup⋆
step-progress' {I = beq ♯r v ~> I} G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> (of-beq eq v⋆ Γ≤Γ') I⋆)
    | lookup⋆ | zero , eq₁
  with instantiation-progress G⋆ H⋆ (eval-reduction (globals-valid-type G⋆) regs⋆ v⋆ )
... | I' , ig , I'⋆
  = _ , _ , _ , _ , _ , H⋆ , of-register sp⋆ regs⋆ , instructionsequence-subtype (globals-valid-type G⋆) Γ≤Γ' I'⋆ , step-beq₀ eq₁ ig
step-progress' {I = beq ♯r v ~> I} G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> (of-beq eq v⋆ Γ≤Γ') I⋆)
    | lookup⋆ | suc n , eq₁
  = _ , _ , _ , _ , _ , H⋆ , of-register sp⋆ regs⋆ , I⋆ , step-beq₁ eq₁ (λ ())
step-progress' G⋆ H⋆ (of-register sp⋆ regs⋆) (of-jmp v⋆ Γ≤Γ')
  with instantiation-progress G⋆ H⋆ (eval-reduction (globals-valid-type G⋆) regs⋆ v⋆ )
... | I' , ig , I'⋆
  = _ , _ , _ , _ , _ , H⋆ , of-register sp⋆ regs⋆ , instructionsequence-subtype (globals-valid-type G⋆) Γ≤Γ' I'⋆ , step-jmp ig

step-progress : ∀ {G P} →
                   ⊢ G , P program →
                   ∃ λ P' →
                     ⊢ G , P' program ×
                     G ⊢ P ⇒ P'
step-progress (of-program G⋆ (of-programstate H⋆ R⋆ I⋆))
  with step-progress' G⋆ H⋆ R⋆ I⋆
... | _ , _ , _ , _ , _ , H'⋆ , R'⋆ , I'⋆ , step
  = _ , of-program G⋆ (of-programstate H'⋆ R'⋆ I'⋆) , step

step-reduction : ∀ {G P P'} →
                   ⊢ G , P program →
                   G ⊢ P ⇒ P' →
                   ⊢ G , P' program
step-reduction P⋆ step
  with step-progress P⋆
... | _ , P'⋆ , step'
  rewrite step-unique step step'
  = P'⋆

steps-reduction : ∀ {n G P₁ P₂} →
                    ⊢ G , P₁ program →
                    G ⊢ P₁ ⇒ₙ n / P₂ →
                    ⊢ G , P₂ program
steps-reduction P₁⋆ [] = P₁⋆
steps-reduction P₁⋆ (step ∷ steps)
  = steps-reduction (step-reduction P₁⋆ step) steps

steps-soundness : ∀ {n G P₁ P₂} →
                    ⊢ G , P₁ program →
                    G ⊢ P₁ ⇒ₙ n / P₂ →
                    ∃ λ P₃ →
                      ⊢ G , P₃ program ×
                      G ⊢ P₂ ⇒ P₃
steps-soundness P⋆ steps = step-progress (steps-reduction P⋆ steps)



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

-- step-progress : ∀ {G ψ₁ H ψ₂ sp regs σ τs Γ₂ I H' R' I'} →
--                     ⊢ G of ψ₁ globals →
--                     ψ₁ ⊢ H of ψ₂ heap →
--                     ψ₁ , ψ₂ ⊢ sp of σ stack →
--                     AllZipᵥ (λ w τ → ψ₁ , ψ₂ ⊢ w of τ wval) regs τs →
--                     {ι : Instruction} →
--                     ψ₁ , [] , registerₐ σ τs ⊢ ι ⇒ Γ₂ instruction →
--                     ψ₁ , [] , Γ₂ ⊢ I instructionsequence →
--                     G ⊢ H , register sp regs , ι ~> I ⇒ H' , R' , I' →
--                     ψ₁ ⊢ (H' , R' , I') programstate
-- step-progress G⋆ H⋆ sp⋆ regs⋆ {add ♯rd ♯rs v} (of-add eq₁ v⋆) I⋆ (step-add eq₂ eq₃) = of-programstate H⋆ (of-register sp⋆ (allzipᵥ-update ♯rd of-int regs⋆ )) I⋆
-- step-progress G⋆ H⋆ sp⋆ regs⋆ {sub ♯rd ♯rs v} (of-sub eq₁ v⋆) I⋆ (step-sub eq₂ eq₃) = of-programstate H⋆ (of-register sp⋆ (allzipᵥ-update ♯rd of-int regs⋆ )) I⋆
-- step-progress G⋆ H⋆ sp⋆ regs⋆ {salloc n} of-salloc I⋆ step-salloc = of-programstate H⋆ (of-register (help n sp⋆) regs⋆) I⋆
--   where help : ∀ {ψ₁ ψ₂ sp σ} n →
--                  ψ₁ , ψ₂ ⊢ sp of σ stack →
--                  ψ₁ , ψ₂ ⊢ replicate n ns ++ sp of stack-append (replicate n ns) σ stack
--         help zero σ⋆ = σ⋆
--         help (suc n) σ⋆ = of-ns ∷ help n σ⋆
-- step-progress G⋆ H⋆ sp⋆ regs⋆ (of-sfree drop₁) I⋆ (step-sfree drop₂) = of-programstate H⋆ (of-register (help sp⋆ drop₁ drop₂) regs⋆) I⋆
--   where help : ∀ {ψ₁ ψ₂ sp sp' σ σ' n} →
--                  ψ₁ , ψ₂ ⊢ sp of σ stack →
--                  stack-drop n σ σ' →
--                  Drop n sp sp' →
--                  ψ₁ , ψ₂ ⊢ sp' of σ' stack
--         help sp⋆ here here = sp⋆
--         help (w⋆ ∷ sp⋆) (there drop₁) (there drop₂) = help sp⋆ drop₁ drop₂
-- step-progress G⋆ H⋆ sp⋆ regs⋆ {sld ♯rd i} (of-sld l₁) I⋆ (step-sld l₂) = of-programstate H⋆ (of-register sp⋆ (allzipᵥ-update ♯rd (help sp⋆ l₁ l₂) regs⋆ )) I⋆
--   where help : ∀ {ψ₁ ψ₂ sp σ i w τ} →
--                ψ₁ , ψ₂ ⊢ sp of σ stack →
--                stack-lookup i σ τ →
--                sp ↓ i ⇒ w →
--                ψ₁ , ψ₂ ⊢ w of τ wval
--         help (w⋆ ∷ sp⋆) here here = w⋆
--         help (w⋆ ∷ sp⋆) (there l₁) (there l₂) = help sp⋆ l₁ l₂
-- step-progress G⋆ H⋆ sp⋆ regs⋆ {sst i ♯rs} (of-sst up₁) I⋆ (step-sst up₂) = of-programstate H⋆ (of-register (help (allzipᵥ-lookup ♯rs regs⋆) sp⋆ up₁ up₂) regs⋆) I⋆
--   where help : ∀ {ψ₁ ψ₂ sp sp' σ σ' i w τ} →
--                  ψ₁ , ψ₂ ⊢ w of τ wval →
--                  ψ₁ , ψ₂ ⊢ sp of σ stack →
--                  stack-update i τ σ σ' →
--                  sp ⟦ i ⟧← w ⇒ sp' →
--                  ψ₁ , ψ₂ ⊢ sp' of σ' stack
--         help w⋆ (w'⋆ ∷ sp⋆) here here = w⋆ ∷ sp⋆
--         help w⋆ (w'⋆ ∷ sp⋆) (there up₁) (there up₂) = w'⋆ ∷ help w⋆ sp⋆ up₁ up₂
-- step-progress G⋆ (of-heap hs⋆) sp⋆ regs⋆ {ld ♯rd ♯rs i} (of-ld eq₁ l₁) I⋆ (step-ld eq₂ l₂ l₃)
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
-- step-progress G⋆ (of-heap hs⋆) sp⋆ regs⋆ {st ♯rd i ♯rs} (of-st eq₁ lookup≤τ l₁ up₁) I⋆ (step-st eq₂ l₂ up₂ up₃)
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
--   = of-programstate H'⋆ (of-register (stack-helper ψ₂'≤ψ₂ sp⋆) (regs-helper₂ ♯rd (proj₁ (≤-valid ψ₂'≤ψ₂)) {!!} (←-to-↓ up₄) (regs-helper₁ ψ₂'≤ψ₂ regs⋆))) (instructionsequence-subtype (globals-valid-type G⋆) (Γ-≤ (≤-refl (stack-valid-type sp⋆)) (allzipᵥ-update ♯rd (tuple-≤ τswut) (≤-refl (regs-valid-type regs⋆)))) I⋆)
-- step-progress {ψ₂ = ψ₂} G⋆ H⋆ sp⋆ regs⋆ {malloc ♯rd τs} (of-malloc τs⋆) I⋆ step-malloc
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
-- step-progress G⋆ H⋆ sp⋆ regs⋆ {mov ♯rd v} (of-mov v⋆) I⋆ step-mov = of-programstate H⋆ (of-register sp⋆ (allzipᵥ-update ♯rd (eval-reduction (globals-valid-type G⋆) regs⋆ v⋆) regs⋆)) I⋆
-- step-progress G⋆ H⋆ sp⋆ regs⋆ (of-beq eq₁ v⋆ Γ≤Γ') I⋆ (step-beq₀ eq₂ ig)
--   = {!!}
--   -- with instantiation-progress G⋆ -- (eval-reduction (globals-valid-type G⋆) regs⋆ v⋆) ig
-- -- ... | I⋆' = of-programstate H⋆ (of-register sp⋆ regs⋆) (instructionsequence-subtype (globals-valid-type G⋆) Γ≤Γ' I⋆')
-- step-progress G⋆ H⋆ sp⋆ regs⋆ (of-beq eq₁ v⋆ Γ≤Γ') I⋆ (step-beq₁ eq₂ eq₃) = of-programstate H⋆ (of-register sp⋆ regs⋆) I⋆

-- -- step-progress : ∀ {G P P'} →
-- --                    ⊢ G , P program →
-- --                    G ⊢ P ⇒ P' →
-- --                    ⊢ G , P' program
-- -- step-progress (of-program G⋆ (of-programstate H⋆ (of-register sp⋆ regs⋆) (of-~> ι⋆ I⋆))) step
-- --   = of-program G⋆ (step-progress G⋆ H⋆ sp⋆ regs⋆ ι⋆ I⋆ step)
-- -- step-progress (of-program G⋆ (of-programstate H⋆ (of-register sp⋆ regs⋆) (of-jmp v⋆ Γ≤Γ'))) (step-jmp ig)
-- --   with instantiation-progress G⋆ (eval-reduction (globals-valid-type G⋆) regs⋆ v⋆) ig
-- -- ... | I⋆' = of-program G⋆ (of-programstate H⋆ (of-register sp⋆ regs⋆) (instructionsequence-subtype (globals-valid-type G⋆) Γ≤Γ' I⋆'))
