module Soundness where

open import Util
open import Judgments
open import Lemmas
open HighGrammar
open HighSemantics

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
    = _ , _ , _ , refl , l' , l , τs'≤τs , ws⋆

  vval-helper' : ∀ {♯r ψ₁ τ σ τs} →
                   ψ₁ , [] ⊢ reg ♯r of registerₐ σ τs ⇒ τ vval →
                   lookup ♯r τs ≡ τ
  vval-helper' of-reg = refl

  vval-int-helper : ∀ {G ψ₁ H ψ₂ regs σ τs v} →
                      ⊢ G of ψ₁ globals →
                      ψ₁ ⊢ H of ψ₂ heap →
                      AllZipᵥ (λ w τ → ψ₁ , ψ₂ ⊢ w of τ wval) regs τs →
                      ψ₁ , [] ⊢ v of registerₐ σ τs ⇒ int vval →
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
  vval-int-helper {v = Λ Δ ∙ v ⟦ θs ⟧} G⋆ H⋆ regs⋆ ()

  replicate-helper : ∀ {ψ₁ ψ₂ sp σ} n →
                       ψ₁ , ψ₂ ⊢ sp of σ stack →
                       ψ₁ , ψ₂ ⊢ replicate n uninit ++ sp of stack-append (replicate n ns) σ stack
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
                        AllZip (λ w τ → ψ₁ , ψ₂ ⊢ w of τ wval⁰) (replicate (length τs) uninit) (map (λ τ → τ , uninit) τs)
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



eval-reduction : ∀ {ψ₁ ψ₂ regs σ τs} →
                   [] ⊢ ψ₁ Valid →
                   AllZipᵥ (λ w τ → ψ₁ , ψ₂ ⊢ w of τ wval) regs τs →
                   {v : SmallValue} {τ : Type} →
                   ψ₁ , [] ⊢ v of registerₐ σ τs ⇒ τ vval →
                   ψ₁ , ψ₂ ⊢ evalSmallValue regs v of τ wval
eval-reduction ψ₁⋆ regs⋆ {v = reg ♯r} of-reg = allzipᵥ-lookup ♯r regs⋆
eval-reduction ψ₁⋆ regs⋆ (of-globval l) = of-globval l (≤-refl (All-lookup l ψ₁⋆))
eval-reduction ψ₁⋆ regs⋆ of-int = of-int
eval-reduction ψ₁⋆ regs⋆ {v = Λ Δ₂ ∙ w ⟦ θs ⟧} {∀[ .Δ₂ ] Γ₃} (of-Λ {Δ₁ = Δ₁} {Γ₁ = Γ₁} v⋆ θs⋆ subs-Γ)
  with eval-reduction ψ₁⋆ regs⋆ v⋆
... | w⋆
  with wval-valid-type w⋆
... | valid-∀ Γ₁⋆
  with valid-weaken Δ₁ Δ₂ [] Γ₁⋆
... | Γ₁'⋆
  rewrite List-++-right-identity Δ₁
        | List-++-right-identity Δ₂
        | weaken-outside-ctx-0 (length Δ₂) Γ₁⋆
        = of-Λ w⋆ θs⋆ subs-Γ (≤-refl (valid-subst-many [] θs⋆ Γ₁'⋆ subs-Γ))

instantiation-progress : ∀ {G ψ₁ H ψ₂ w Δ Γ} →
                             ⊢ G of ψ₁ globals →
                             ψ₁ ⊢ H of ψ₂ heap →
                             ψ₁ , ψ₂ ⊢ w of ∀[ Δ ] Γ wval →
                             ∃ λ I →
                               InstantiateGlobal G w I ×
                               ψ₁ , Δ ⊢ I of Γ instructionsequence
instantiation-progress (of-globals gs⋆) H⋆ (of-globval l τ≤τ')
  with allzip-lookup₂ l gs⋆
instantiation-progress (of-globals gs⋆) H⋆ (of-globval l (∀-≤ Γ≤Γ'))
  | code[ Δ ] Γ ∙ I , l' , of-gval Γ⋆ I⋆
  rewrite List-++-right-identity Δ
    = _ , instantiate-globval l' , instructionsequence-subtype (gvals-valid-type gs⋆) I⋆ Γ≤Γ'
instantiation-progress G⋆ (of-heap hs⋆) (of-heapval l τ≤τ')
  with allzip-lookup₂ l hs⋆
... | tuple ws , l' , of-tuple ws⋆
  with τ≤τ'
... | ()
instantiation-progress G⋆ H⋆ (of-Λ {Δ₁ = Δ₁} {Δ₂} w⋆ θs⋆ subs-Γ Γ≤Γ')
  with instantiation-progress G⋆ H⋆ w⋆
... | I , ig , I⋆
  with instructionsequence-subst-many [] Δ₁ Δ₂ (globals-valid-type G⋆) θs⋆ subs-Γ (instructionsequence-weaken-right Δ₁ Δ₂ I⋆)
... | I' , subs-I , I'⋆
  = I' , instantiate-Λ ig subs-I , instructionsequence-subtype (globals-valid-type G⋆) I'⋆ Γ≤Γ'

step-progress' : ∀ {G ψ₁ H ψ₂ R Γ I} →
                   I ≢ halt →
                   ⊢ G of ψ₁ globals →
                   ψ₁ ⊢ H of ψ₂ heap →
                   ψ₁ , ψ₂ ⊢ R of Γ register →
                   ψ₁ , [] ⊢ I of Γ instructionsequence →
                   ∃₂ λ H' ψ₂' → ∃₂ λ R' Γ' → ∃ λ I' →
                      ψ₁ ⊢ H' of ψ₂' heap ×
                      ψ₁ , ψ₂' ⊢ R' of Γ' register ×
                      ψ₁ , [] ⊢ I' of Γ' instructionsequence ×
                      G ⊢ (H , R , I) ⇒ (H' , R' , I')
step-progress' {I = add ♯rd ♯rs v ~> I} I≢halt G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> (of-add eq v⋆) I⋆)
  with allzipᵥ-lookup ♯rs regs⋆
... | lookup⋆
  rewrite eq
  with wval-int-helper G⋆ H⋆ lookup⋆
... | i₁ , eq₁
  with vval-int-helper G⋆ H⋆ regs⋆ v⋆
... | i₂ , eq₂
  = _ , _ , _ , _ , I , H⋆ , of-register sp⋆ (allzipᵥ-update ♯rd of-int regs⋆) , I⋆ , step-add eq₁ eq₂
step-progress' {I = sub ♯rd ♯rs v ~> I} I≢halt G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> (of-sub eq v⋆) I⋆)
  with allzipᵥ-lookup ♯rs regs⋆
... | lookup⋆
  rewrite eq
  with wval-int-helper G⋆ H⋆ lookup⋆
... | i₁ , eq₁
  with vval-int-helper G⋆ H⋆ regs⋆ v⋆
... | i₂ , eq₂
  = _ , _ , _ , _ , I , H⋆ , of-register sp⋆ (allzipᵥ-update ♯rd of-int regs⋆) , I⋆ , step-sub eq₁ eq₂
step-progress' {I = salloc n ~> I} I≢halt G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> of-salloc I⋆)
  = _ , _ , _ , _ , _ , H⋆ , of-register (replicate-helper n sp⋆) regs⋆ , I⋆ , step-salloc
step-progress' {I = sfree n ~> I} I≢halt G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> (of-sfree drop) I⋆)
  with drop-helper sp⋆ drop
... | sp' , sp'⋆ , drop'
  = _ , _ , _ , _ , _ , H⋆ , of-register sp'⋆ regs⋆ , I⋆ , step-sfree drop'
step-progress' {I = sld ♯rd i ~> I} I≢halt G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> (of-sld l) I⋆)
  with stack-lookup-helper sp⋆ l
... | w' , l' , w'⋆
  = _ , _ , _ , _ , _ , H⋆ , of-register sp⋆ (allzipᵥ-update ♯rd w'⋆ regs⋆) , I⋆ , step-sld l'
step-progress' {I = sst i ♯rs ~> I} I≢halt G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> (of-sst up) I⋆)
  with stack-update-helper (allzipᵥ-lookup ♯rs regs⋆) sp⋆ up
... | sp' , up' , sp'⋆
  = _ , _ , _ , _ , _ , H⋆ , of-register sp'⋆ regs⋆ , I⋆ , step-sst up'
step-progress' {I = ld ♯rd ♯rs i ~> I} I≢halt G⋆ (of-heap hs⋆) (of-register sp⋆ regs⋆) (of-~> (of-ld eq l) I⋆)
  with allzipᵥ-lookup ♯rs regs⋆
... | lookup⋆
  rewrite eq
  with wval-tuple-helper G⋆ (of-heap hs⋆) lookup⋆
... | labₕ , ws , τs⁻ , eq₁ , l₁ , l₂ , τs'≤τs , ws⋆
  with allzip-lookup₂ l τs'≤τs
... | (τ , init) , l₃ , (τ⁻-≤ τ⋆ φ-≤-init)
  with allzip-lookup₂ l₃ ws⋆
... | w , l₄ , of-init w⋆
  = _ , _ , _ , _ , _ , of-heap hs⋆ , of-register sp⋆ (allzipᵥ-update ♯rd w⋆ regs⋆) , I⋆ , step-ld eq₁ l₁ l₄
step-progress' {I = st ♯rd i ♯rs ~> I} I≢halt G⋆ (of-heap hs⋆) (of-register sp⋆ regs⋆) (of-~> (of-st eq lookup≤τ l up) I⋆)
  with allzipᵥ-lookup ♯rd regs⋆ | wval-subtype (allzipᵥ-lookup ♯rs regs⋆) lookup≤τ
... | ♯rd⋆ | ♯rs⋆
  rewrite eq
  with wval-tuple-helper G⋆ (of-heap hs⋆) ♯rd⋆
... | labₕ , ws , τs⁻₂ , eq₁ , l₁ , l₂ , τs⁻₂≤τs⁻₁ , ws⋆
  with update-helper₂ l τs⁻₂≤τs⁻₁ ♯rs⋆ ws⋆
... | ws' , τs⁻₃ , up₁ , up₂ , ws'⋆ , τs⁻₃≤τs⁻₂
  with heap-helper (of-tuple ws'⋆) (of-heap hs⋆) l₂ (tuple-≤ τs⁻₃≤τs⁻₂)
... | H' , ψ₂' , up₃ , up₄ , H'⋆ , ψ₂'≤ψ₂
  with (regs-helper₂ ♯rd (≤-valid₁ ψ₂'≤ψ₂) eq₁ (←-to-↓ up₄) (AllZipᵥ-map (wval-helper ψ₂'≤ψ₂) regs⋆))
... | regs'⋆
  with allzip-update up₂ up (≤-refl (valid-τ⁻ (≤-valid₂ lookup≤τ))) τs⁻₂≤τs⁻₁
... | τs⁻₃≤τs⁻₁'
  = H' , ψ₂' , _ , _ , I , H'⋆ , of-register (stack-helper ψ₂'≤ψ₂ sp⋆) (AllZipᵥ-trans wval-subtype regs'⋆ (allzipᵥ-update ♯rd (tuple-≤ τs⁻₃≤τs⁻₁') (≤-refl (regs-valid-type regs⋆)))) , I⋆ , step-st eq₁ l₁ up₁ up₃
step-progress' {H = H} {ψ₂ = ψ₂} {I = malloc ♯rd τs ~> I} I≢halt G⋆ (of-heap hs⋆) (of-register sp⋆ regs⋆) (of-~> (of-malloc τs⋆) I⋆)
  = _ , _ , _ , _ , _ , heap-push (of-heap hs⋆) (of-tuple (map-uninit-helper τs⋆)) , of-register (stack-++ sp⋆) (allzipᵥ-update ♯rd (of-heapval (subst₂ (λ h i → ψ₂ ∷ʳ h ↓ i ⇒ h) refl (sym (AllZip-length hs⋆)) (↓-length ψ₂ (tuple (map (λ τ → τ , uninit) τs)))) (≤-refl (valid-tuple (map-uninit-helper₂ τs⋆)))) (AllZipᵥ-map wval-++ regs⋆)) , I⋆ , step-malloc
step-progress' {I = mov ♯rd v ~> I} I≢halt G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> (of-mov v⋆) I⋆)
  = _ , _ , _ , _ , _ , H⋆ , of-register sp⋆ (allzipᵥ-update ♯rd (eval-reduction (globals-valid-type G⋆) regs⋆ v⋆) regs⋆) , I⋆ , step-mov
step-progress' {I = beq ♯r v ~> I} I≢halt G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> (of-beq eq v⋆ Γ≤Γ') I⋆)
  with allzipᵥ-lookup ♯r regs⋆
... | lookup⋆
  rewrite eq
  with wval-int-helper G⋆ H⋆ lookup⋆
step-progress' {I = beq ♯r v ~> I} I≢halt G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> (of-beq eq v⋆ Γ≤Γ') I⋆)
    | lookup⋆ | zero , eq₁
  with instantiation-progress G⋆ H⋆ (eval-reduction (globals-valid-type G⋆) regs⋆ v⋆)
... | I' , ig , I'⋆
  = _ , _ , _ , _ , _ , H⋆ , of-register sp⋆ regs⋆ , instructionsequence-subtype (globals-valid-type G⋆) I'⋆ Γ≤Γ' , step-beq₀ eq₁ ig
step-progress' {I = beq ♯r v ~> I} I≢halt G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> (of-beq eq v⋆ Γ≤Γ') I⋆)
    | lookup⋆ | suc n , eq₁
  = _ , _ , _ , _ , _ , H⋆ , of-register sp⋆ regs⋆ , I⋆ , step-beq₁ eq₁ (λ ())
step-progress' I≢halt G⋆ H⋆ (of-register sp⋆ regs⋆) (of-jmp v⋆ Γ≤Γ')
  with instantiation-progress G⋆ H⋆ (eval-reduction (globals-valid-type G⋆) regs⋆ v⋆)
... | I' , ig , I'⋆
  = _ , _ , _ , _ , _ , H⋆ , of-register sp⋆ regs⋆ , instructionsequence-subtype (globals-valid-type G⋆) I'⋆ Γ≤Γ' , step-jmp ig
step-progress' I≢halt G⋆ H⋆ R⋆ of-halt
  with I≢halt refl
... | ()

step-progress : ∀ {ℒ} →
                   ⊢ ℒ program →
                   ∃ λ ℒ' →
                     ⊢ ℒ' program ×
                     ⊢ ℒ ⇒ ℒ'
step-progress {ℒ = running G (H , R , I)} (of-running G⋆ (of-programstate H⋆ R⋆ I⋆))
  with I ≟ halt
step-progress {ℒ = running G (H , R , .halt)} (of-running G⋆ (of-programstate H⋆ R⋆ I⋆))
    | yes refl = halted , of-halted , step-halting
... | no I≢halt
  with step-progress' I≢halt G⋆ H⋆ R⋆ I⋆
... | _ , _ , _ , _ , _ , H'⋆ , R'⋆ , I'⋆ , step
  = _ , of-running G⋆ (of-programstate H'⋆ R'⋆ I'⋆) , step-running step
step-progress of-halted = halted , of-halted , step-halted

step-reduction : ∀ {ℒ ℒ'} →
                   ⊢ ℒ program →
                   ⊢ ℒ ⇒ ℒ' →
                   ⊢ ℒ' program
step-reduction ℒ⋆ step
  with step-progress ℒ⋆
... | _ , ℒ'⋆ , step'
  rewrite step-prg-uniqueₕ step step'
  = ℒ'⋆

steps-reduction : ∀ {n ℒ₁ ℒ₂} →
                    ⊢ ℒ₁ program →
                    ⊢ ℒ₁ ⇒ₙ n / ℒ₂ →
                    ⊢ ℒ₂ program
steps-reduction ℒ₁⋆ [] = ℒ₁⋆
steps-reduction ℒ₁⋆ (step ∷ steps)
  = steps-reduction (step-reduction ℒ₁⋆ step) steps

steps-soundness : ∀ {n ℒ₁ ℒ₂} →
                    ⊢ ℒ₁ program →
                    ⊢ ℒ₁ ⇒ₙ n / ℒ₂ →
                    ∃ λ ℒ₃ →
                      ⊢ ℒ₃ program ×
                      ⊢ ℒ₂ ⇒ ℒ₃
steps-soundness ℒ⋆ steps = step-progress (steps-reduction ℒ⋆ steps)
