module Lemmas.Soundness where

open import Util
open import Judgments
open import Lemmas.Types using (≤-refl)
open import Lemmas.TypeSubstitution using (valid-weaken ; weaken-outside-ctx-0 ; valid-subst-many)
open import Lemmas.TermWeaken using (instructionsequence-weaken)
open import Lemmas.TermSubstitution using (instructionsequence-subst-many)
open import Lemmas.TermCasting using (instructionsequence-cast)
open import Lemmas.HighSemantics using (step-prg-uniqueₕ)
open import Lemmas.TermValidType using (wval-valid-type ; globals-valid-type)
open import Lemmas.HeapSteps using (store-step ; load-step)
open import Lemmas.MallocStep using (malloc-step)
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
  wval-int-helper G⋆ H⋆ of-int = , refl

  reg-eq : ∀ {♯r ψ₁ Δ τ σ τs} →
             ψ₁ , Δ ⊢ reg ♯r of registerₐ σ τs ⇒ τ vval →
             lookup ♯r τs ≡ τ
  reg-eq of-reg = refl

  vval-int-helper : ∀ {ψ₁ G H ψ₂ regs σ τs v} →
                      ⊢ G of ψ₁ globals →
                      ψ₁ ⊢ H of ψ₂ heap →
                      AllZipᵥ (λ w τ → ψ₁ , ψ₂ ⊢ w of τ wval) regs τs →
                      ψ₁ , [] ⊢ v of registerₐ σ τs ⇒ int vval →
                      ∃ λ n →
                        evalSmallValue regs v ≡ int n
  vval-int-helper {ψ₁} {v = reg ♯r} G⋆ H⋆ regs⋆ v⋆
    with allzipᵥ-lookup ♯r regs⋆
  ... | lookup⋆
    rewrite reg-eq v⋆
    = wval-int-helper G⋆ H⋆ lookup⋆
  vval-int-helper {v = globval _} (of-globals gs⋆) H⋆ regs⋆ (of-globval l)
    with allzip-lookup₂ l gs⋆
  ... | g , l' , ()
  vval-int-helper {v = int n} G⋆ H⋆ regs⋆ v⋆ = n , refl
  vval-int-helper {v = Λ Δ ∙ v ⟦ θs ⟧} G⋆ H⋆ regs⋆ ()

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
    = , instantiate-globval l' , instructionsequence-cast (globals-valid-type (of-globals gs⋆)) I⋆ Γ≤Γ'
instantiation-progress G⋆ (of-heap hs⋆) (of-heapval l τ≤τ')
  with allzip-lookup₂ l hs⋆
instantiation-progress G⋆ (of-heap hs⋆) (of-heapval l ())
    | tuple ws , l' , of-tuple ws⋆
instantiation-progress G⋆ H⋆ (of-Λ {Δ₁ = Δ₁} {Δ₂} w⋆ θs⋆ subs-Γ Γ≤Γ')
  with instantiation-progress G⋆ H⋆ w⋆
... | I , ig , I⋆
  with instructionsequence-subst-many [] Δ₁ Δ₂ (globals-valid-type G⋆) θs⋆ subs-Γ (instructionsequence-weaken Δ₁ Δ₂ I⋆)
... | I' , subs-I , I'⋆
  = I' , instantiate-Λ ig subs-I , instructionsequence-cast (globals-valid-type G⋆) I'⋆ Γ≤Γ'

private
  _/_/_/_ : ∀ {ψ₁ G H R I H' ψ₂' R' Γ' I'} →
              ψ₁ ⊢ H' of ψ₂' heap →
              ψ₁ , ψ₂' ⊢ R' of Γ' register →
              ψ₁ , [] ⊢ I' of Γ' instructionsequence →
              G ⊢ (H , R , I) ⇒ (H' , R' , I') →
              ∃₂ λ H'' ψ₂'' → ∃₂ λ R'' Γ'' → ∃ λ I'' →
                 ψ₁ ⊢ H'' of ψ₂'' heap ×
                 ψ₁ , ψ₂'' ⊢ R'' of Γ'' register ×
                 ψ₁ , [] ⊢ I'' of Γ'' instructionsequence ×
                 G ⊢ (H , R , I) ⇒ (H'' , R'' , I'')
  H'⋆ / R'⋆ / I'⋆ / step = , , , , , H'⋆ , R'⋆ , I'⋆ , step

step-progress' : ∀ {ψ₁ ψ₂ sp regs Γ I G H} →
                   I ≢ halt →
                   ⊢ G of ψ₁ globals →
                   ψ₁ ⊢ H of ψ₂ heap →
                   ψ₁ , ψ₂ ⊢ register sp regs of Γ register →
                   ψ₁ , [] ⊢ I of Γ instructionsequence →
                   ∃₂ λ H' ψ₂' → ∃₂ λ R' Γ' → ∃ λ I' →
                      ψ₁ ⊢ H' of ψ₂' heap ×
                      ψ₁ , ψ₂' ⊢ R' of Γ' register ×
                      ψ₁ , [] ⊢ I' of Γ' instructionsequence ×
                      G ⊢ (H , register sp regs , I) ⇒ (H' , R' , I')

step-progress' {I = add ♯rd ♯rs v ~> I} I≢halt G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> (of-add eq v⋆) I⋆)
  with allzipᵥ-lookup ♯rs regs⋆
... | lookup⋆
  rewrite eq
  with wval-int-helper G⋆ H⋆ lookup⋆
... | i₁ , eq₁
  with vval-int-helper G⋆ H⋆ regs⋆ v⋆
... | i₂ , eq₂
  = H⋆ / of-register sp⋆ (allzipᵥ-update ♯rd of-int regs⋆) / I⋆ / step-add eq₁ eq₂

step-progress' {I = sub ♯rd ♯rs v ~> I} I≢halt G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> (of-sub eq v⋆) I⋆)
  with allzipᵥ-lookup ♯rs regs⋆
... | lookup⋆
  rewrite eq
  with wval-int-helper G⋆ H⋆ lookup⋆
... | i₁ , eq₁
  with vval-int-helper G⋆ H⋆ regs⋆ v⋆
... | i₂ , eq₂
  = H⋆ / of-register sp⋆ (allzipᵥ-update ♯rd of-int regs⋆) / I⋆ / step-sub eq₁ eq₂

step-progress' {ψ₁} {ψ₂} {sp} {Γ = registerₐ σ τs} {I = salloc n ~> I} I≢halt G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> of-salloc I⋆)
  = H⋆ / of-register (help n) regs⋆ / I⋆ / step-salloc
    where help : ∀ n → ψ₁ , ψ₂ ⊢ replicate n uninit ++ sp of stack-append (replicate n ns) σ stack
          help 0 = sp⋆
          help (suc n) = of-ns ∷ help n

step-progress' {I = sfree n ~> I} I≢halt G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> (of-sfree drop) I⋆)
  with help sp⋆ drop
  where help : ∀ {ψ₁ ψ₂ n sp σ σ'} →
                 ψ₁ , ψ₂ ⊢ sp of σ stack →
                 stack-drop n σ σ' →
                 ∃ λ sp' →
                     ψ₁ , ψ₂ ⊢ sp' of σ' stack ×
                     Drop n sp sp'
        help σ⋆ here = , σ⋆ , here
        help (τ⋆ ∷ σ⋆) (there drop) = ⟨ id , ⟨ id , there ⟩ ⟩ (help σ⋆ drop)
... | sp' , sp'⋆ , drop'
  = H⋆ / of-register sp'⋆ regs⋆ / I⋆ / step-sfree drop'

step-progress' {I = sld ♯rd i ~> I} I≢halt G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> (of-sld l) I⋆)
  with help sp⋆ l
  where help : ∀ {ψ₁ ψ₂ sp σ i τ} →
                 ψ₁ , ψ₂ ⊢ sp of σ stack →
                 stack-lookup i σ τ →
                 ∃ λ w →
                   sp ↓ i ⇒ w ×
                   ψ₁ , ψ₂ ⊢ w of τ wval
        help (w⋆ ∷ sp⋆) here = , here , w⋆
        help (w⋆ ∷ sp⋆) (there l) = ⟨ _ , ⟨ there , id ⟩ ⟩ (help sp⋆ l)
... | w' , l' , w'⋆
  = H⋆ / of-register sp⋆ (allzipᵥ-update ♯rd w'⋆ regs⋆) / I⋆ / step-sld l'

step-progress' {ψ₁} {ψ₂} {sp} {regs} {registerₐ σ τs} {I = sst i ♯rs ~> I} I≢halt G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> (of-sst up) I⋆)
  with help sp⋆ up
  where help : ∀ {sp σ σ' i} →
                 ψ₁ , ψ₂ ⊢ sp of σ stack →
                 stack-update i (lookup ♯rs τs) σ σ' →
                 ∃ λ sp' →
                   sp ⟦ i ⟧← lookup ♯rs regs ⇒ sp' ×
                   ψ₁ , ψ₂ ⊢ sp' of σ' stack
        help (w⋆ ∷ sp⋆) here = , here , allzipᵥ-lookup ♯rs regs⋆ ∷ sp⋆
        help {sp = w ∷ sp} (w⋆ ∷ sp⋆) (there l)
          = ⟨ _ , ⟨ there , _∷_ w⋆ ⟩ ⟩ (help sp⋆ l)
... | sp' , up' , sp'⋆
  = H⋆ / of-register sp'⋆ regs⋆ / I⋆ / step-sst up'

step-progress' {I = ld ♯rd ♯rs i ~> I} I≢halt G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> (of-ld eq l) I⋆)
  with load-step G⋆ H⋆ sp⋆ regs⋆ eq l
... | _ , R'⋆ , step
  = H⋆ / R'⋆ / I⋆ / step

step-progress' {I = st ♯rd i ♯rs ~> I} I≢halt G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> (of-st eq lookup≤τ l up) I⋆)
  with store-step G⋆ H⋆ sp⋆ regs⋆ eq lookup≤τ l up
... | _ , _ , H'⋆ , R'⋆ , step
  = H'⋆ / R'⋆ / I⋆ / step

step-progress' {I = malloc ♯rd τs ~> I} I≢halt G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> (of-malloc τs⋆) I⋆)
  with malloc-step ♯rd H⋆ τs⋆ (of-register sp⋆ regs⋆)
... | H'⋆ , Γ'⋆
  = H'⋆ / Γ'⋆ / I⋆ / step-malloc

step-progress' {I = mov ♯rd v ~> I} I≢halt G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> (of-mov v⋆) I⋆)
  = H⋆ / of-register sp⋆ (allzipᵥ-update ♯rd (eval-reduction (globals-valid-type G⋆) regs⋆ v⋆) regs⋆) / I⋆ / step-mov

step-progress' {I = beq ♯r v ~> I} I≢halt G⋆ H⋆ (of-register sp⋆ regs⋆) (of-~> (of-beq eq v⋆ Γ≤Γ') I⋆)
  with allzipᵥ-lookup ♯r regs⋆
... | lookup⋆
  rewrite eq
  with wval-int-helper G⋆ H⋆ lookup⋆
... | suc n , eq₁
  = H⋆ / of-register sp⋆ regs⋆ / I⋆ / step-beq₁ eq₁ (λ ())
... | zero , eq₁
  with instantiation-progress G⋆ H⋆ (eval-reduction (globals-valid-type G⋆) regs⋆ v⋆)
... | I' , ig , I'⋆
  = H⋆ / of-register sp⋆ regs⋆ / instructionsequence-cast (globals-valid-type G⋆) I'⋆ Γ≤Γ' / step-beq₀ eq₁ ig

step-progress' I≢halt G⋆ H⋆ (of-register sp⋆ regs⋆) (of-jmp v⋆ Γ≤Γ')
  with instantiation-progress G⋆ H⋆ (eval-reduction (globals-valid-type G⋆) regs⋆ v⋆)
... | I' , ig , I'⋆
  = H⋆ / of-register sp⋆ regs⋆ / instructionsequence-cast (globals-valid-type G⋆) I'⋆ Γ≤Γ' / step-jmp ig

step-progress' I≢halt G⋆ H⋆ R⋆ of-halt
  with I≢halt refl
... | ()

step-progress⁺ : ∀ {ℒ} →
                   ⊢ ℒ program →
                   ∃ λ ℒ' →
                     ⊢ ℒ' program ×
                     ⊢ ℒ ⇒ ℒ'
step-progress⁺ {ℒ = running G (H , register sp regs , I)} (of-running G⋆ (of-programstate H⋆ R⋆ I⋆))
  with I ≟ halt
step-progress⁺ {ℒ = running G (H , register sp regs , .halt)} (of-running G⋆ (of-programstate H⋆ R⋆ I⋆))
    | yes refl = halted , of-halted , step-halting
... | no I≢halt
  with step-progress' I≢halt G⋆ H⋆ R⋆ I⋆
... | _ , _ , _ , _ , _ , H'⋆ , R'⋆ , I'⋆ , step
  = , of-running G⋆ (of-programstate H'⋆ R'⋆ I'⋆) , step-running step
step-progress⁺ of-halted = halted , of-halted , step-halted


step-progress : ∀  {ℒ} → ⊢ ℒ program →
                ∃ λ ℒ' → ⊢ ℒ ⇒ ℒ'
step-progress ℒ⋆ = ⟨ id , proj₂ ⟩ (step-progress⁺ ℒ⋆)

step-reduction : ∀ {ℒ}  → ⊢ ℒ program →
                 ∀ {ℒ'} → ⊢ ℒ ⇒ ℒ' →
                 ⊢ ℒ' program
step-reduction ℒ⋆ step
  with step-progress⁺ ℒ⋆
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
                    ∃ λ ℒ₃ → ⊢ ℒ₂ ⇒ ℒ₃
steps-soundness ℒ⋆ steps = step-progress (steps-reduction ℒ⋆ steps)
