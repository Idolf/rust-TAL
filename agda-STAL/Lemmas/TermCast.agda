module Lemmas.TermCast where

open import Util
open import Judgments
open import Lemmas.Types using (≤-refl ; ≤-trans)
open import Lemmas.Substitution using (subst-unique-many)
open import Lemmas.TypeSubstitution using (≤-++ ; subtype-weaken ; subtype-subst-exists-many)
open HighGrammar

-- The purpose of this file is to prove two theorems:
-- * That WordValues can be casted to more general types.
-- * That InstructionSequences can be casted to a more specific type.

private
  ≤int⇒≡int : ∀ {Δ} {τ : Type} →
            Δ ⊢ τ ≤ int →
            τ ≡ int
  ≤int⇒≡int int-≤ = refl

  ≤tuple⇒≡tuple : ∀ {Δ} {τ : Type} {τs⁻} →
                    Δ ⊢ τ ≤ tuple τs⁻ →
                    ∃ λ τs⁻' →
                      τ ≡ tuple τs⁻'
  ≤tuple⇒≡tuple (tuple-≤ τs⁻≤τs⁻') = _ , refl

  stack-lookup-subtype : ∀ {Δ sp₁ sp₂ i τ₂} →
                           Δ ⊢ sp₁ ≤ sp₂ →
                           stack-lookup i sp₂ τ₂ →
                           ∃ λ τ₁ →
                               Δ ⊢ τ₁ ≤ τ₂ ×
                               stack-lookup i sp₁ τ₁
  stack-lookup-subtype (τ₁≤τ₂ ∷ sp₁≤sp₂) here = _ , τ₁≤τ₂ , here
  stack-lookup-subtype (τ₁≤τ₂ ∷ sp₁≤sp₂) (there l)
    with stack-lookup-subtype sp₁≤sp₂ l
  ... | τ₂' , τ₁≤τ₂' , l' = τ₂' , τ₁≤τ₂' , there l'

  stack-update-subtype : ∀ {Δ sp₁ sp₂ sp₂' i τ₁ τ₂} →
                           Δ ⊢ sp₁ ≤ sp₂ →
                           Δ ⊢ τ₁ ≤ τ₂ →
                           stack-update i τ₂ sp₂ sp₂' →
                           ∃ λ sp₁' →
                               stack-update i τ₁ sp₁ sp₁' ×
                               Δ ⊢ sp₁' ≤ sp₂'
  stack-update-subtype (τ₁≤τ₂' ∷ sp₁≤sp₂) τ₁≤τ₂ here = _ , here , τ₁≤τ₂ ∷ sp₁≤sp₂
  stack-update-subtype (τ₁≤τ₂' ∷ sp₁≤sp₂) τ₁≤τ₂ (there up)
    with stack-update-subtype sp₁≤sp₂ τ₁≤τ₂ up
  ... | sp₁' , up' , sp₁'≤sp₂' = _ , there up' , τ₁≤τ₂' ∷ sp₁'≤sp₂'

  stack-append-subtype : ∀ {Δ τs₁ τs₂ σ₁ σ₂} →
                           Δ ⊢ τs₁ ≤ τs₂ →
                           Δ ⊢ σ₁ ≤ σ₂ →
                           Δ ⊢ stack-append τs₁ σ₁ ≤ stack-append τs₂ σ₂
  stack-append-subtype [] σ₁≤σ₂ = σ₁≤σ₂
  stack-append-subtype (τ₁≤τ₂ ∷ τs₁≤τs₂) σ₁≤σ₂ = τ₁≤τ₂ ∷ stack-append-subtype τs₁≤τs₂ σ₁≤σ₂

  stack-drop-subtype : ∀ {Δ i σ₁ σ₂ σ₂'} →
                       Δ ⊢ σ₁ ≤ σ₂ →
                       stack-drop i σ₂ σ₂' →
                       ∃ λ σ₁' →
                         stack-drop i σ₁ σ₁' ×
                         Δ ⊢ σ₁' ≤ σ₂'
  stack-drop-subtype (ρ⁼-≤ l) here = _ , here , ρ⁼-≤ l
  stack-drop-subtype [] here = _ , here , []
  stack-drop-subtype σ₁≤σ₂ here = _ , here , σ₁≤σ₂
  stack-drop-subtype (τ₁≤τ₂ ∷ σ₁≤σ₂) (there drop₁) =
    Σ-map _ (Σ-map there id) (stack-drop-subtype σ₁≤σ₂ drop₁)

  vval-cast : ∀ {ψ₁ Δ Γ₁ Γ₂} →
                [] ⊢ ψ₁ Valid →
                {v : SmallValue} {τ₂ : Type} →
                ψ₁ , Δ  ⊢ v of Γ₂ ⇒ τ₂ vval →
                Δ ⊢ Γ₁ ≤ Γ₂ →
                ∃ λ τ₁ →
                  Δ ⊢ τ₁ ≤ τ₂ ×
                  ψ₁ , Δ ⊢ v of Γ₁ ⇒ τ₁ vval
  vval-cast ψ₁⋆ {reg ♯r} of-reg  (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
    with allzipᵥ-lookup ♯r regs₁≤regs₂
  ... | lookup₁≤lookup₂ = _ , lookup₁≤lookup₂ , of-reg
  vval-cast ψ₁⋆ (of-globval l) Γ₁≤Γ₂ = _ , ≤-++ (≤-refl (All-lookup l ψ₁⋆)) , of-globval l
  vval-cast ψ₁⋆ of-int Γ₁≤Γ₂ = int , int-≤ , of-int
  vval-cast {Δ = Δ} ψ₁⋆ {Λ Δₒ ∙ v ⟦ θs ⟧} {∀[ .Δₒ ] Γₒ₁} (of-Λ {Δ₁ = Δᵢ} .{Δₒ} {Γᵢ₁} .{Γₒ₁} v⋆ θs⋆ subs-Γ₁)  Γ₁≤Γ₂
    with vval-cast ψ₁⋆ v⋆  Γ₁≤Γ₂
  ... | ∀[ .Δᵢ ] Γᵢ₂ , ∀-≤ Γᵢ₁≤Γᵢ₂ , v⋆'
    with subtype-subst-exists-many {A = RegisterAssignment} [] θs⋆ (subtype-weaken Δᵢ Δₒ Δ Γᵢ₁≤Γᵢ₂)
  ... | Γₒ₁' , Γₒ₂ , subs-Γ₁' , subs-Γ₂ , Γₒ₁'≤Γₒ₂
    rewrite subst-unique-many subs-Γ₁ subs-Γ₁' = ∀[ Δₒ ] Γₒ₂ , ∀-≤ Γₒ₁'≤Γₒ₂ , of-Λ v⋆' θs⋆ subs-Γ₂

  instruction-cast : ∀ {ψ₁ Δ Γ₁ Γ₂ Γ₂'} →
                       [] ⊢ ψ₁ Valid →
                       {ι : Instruction} →
                       ψ₁ , Δ ⊢ ι of Γ₂ ⇒ Γ₂' instruction →
                       Δ ⊢ Γ₁ ≤ Γ₂ →
                       ∃ λ Γ₁' →
                         ψ₁ , Δ ⊢ ι of Γ₁ ⇒ Γ₁' instruction ×
                         Δ ⊢ Γ₁' ≤ Γ₂'
  instruction-cast ψ₁⋆ {ι = add ♯rd ♯rs v} (of-add eq v⋆)
                      (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
    with vval-cast ψ₁⋆ v⋆ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂) | allzipᵥ-lookup ♯rs regs₁≤regs₂
  ... | τ , int≤τ , v⋆' | int≤lookup
    rewrite eq
          | ≤int⇒≡int int≤τ
    = _ , of-add (≤int⇒≡int int≤lookup) v⋆' ,
          Γ-≤ sp₁≤sp₂ (allzipᵥ-update ♯rd int-≤ regs₁≤regs₂)
  instruction-cast ψ₁⋆ {ι = sub ♯rd ♯rs v} (of-sub eq v⋆)
                      (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
    with vval-cast ψ₁⋆ v⋆ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂) | allzipᵥ-lookup ♯rs regs₁≤regs₂
  ... | τ , int≤τ , v⋆' | int≤lookup
    rewrite eq
          | ≤int⇒≡int int≤τ
    = _ , of-sub (≤int⇒≡int int≤lookup) v⋆' ,
          Γ-≤ sp₁≤sp₂ (allzipᵥ-update ♯rd int-≤ regs₁≤regs₂)
  instruction-cast ψ₁⋆ {ι = salloc n} of-salloc
                      (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
    = _ , of-salloc , Γ-≤ (stack-append-subtype (replicate-subtype n) sp₁≤sp₂) regs₁≤regs₂
    where replicate-subtype : ∀ {Δ} n →
                                Δ ⊢ replicate n ns ≤ replicate n ns
          replicate-subtype zero = []
          replicate-subtype (suc n) = ns-≤ ∷ replicate-subtype n
  instruction-cast ψ₁⋆ {ι = sfree n} (of-sfree drop₁)
                      (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
    with stack-drop-subtype sp₁≤sp₂ drop₁
  ... | sp₂' , drop₂ , sp₂'≤sp₁'
    = _ , of-sfree drop₂ , Γ-≤ sp₂'≤sp₁' regs₁≤regs₂
  instruction-cast ψ₁⋆ {ι = sld ♯rd i} (of-sld l)
                      (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
    with stack-lookup-subtype sp₁≤sp₂ l
  ... | τ₂ , τ₂≤τ₁ , l'
    = _ , of-sld l' , Γ-≤ sp₁≤sp₂ (allzipᵥ-update ♯rd τ₂≤τ₁ regs₁≤regs₂)
  instruction-cast ψ₁⋆ {ι = sst i ♯rs} (of-sst up)
                      (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
    with stack-update-subtype sp₁≤sp₂ (allzipᵥ-lookup ♯rs regs₁≤regs₂) up
  ... | sp₂' , up' , sp₂'≤sp₁'
    = _ , of-sst up' , Γ-≤ sp₂'≤sp₁' regs₁≤regs₂
  instruction-cast {Δ = Δ} ψ₁⋆ {ι = ld ♯rd ♯rs i} (of-ld eq l)
                      (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
    with allzipᵥ-lookup ♯rs regs₁≤regs₂
  ... | lookup₁≤lookup₂
    with ≤tuple⇒≡tuple (subst₂ (_⊢_≤_ Δ) refl eq lookup₁≤lookup₂)
  ... | τs⁻ , eq₁
    with subst₂ (_⊢_≤_ Δ) eq₁ eq lookup₁≤lookup₂
  ... | tuple-≤ τs₁≤τs₂
    with allzip-lookup₂ l τs₁≤τs₂
  ... | (τ , init) , l' , τ⁻-≤ τ⋆ φ-≤-init
    = _ , of-ld eq₁ l' , Γ-≤ sp₁≤sp₂ (allzipᵥ-update ♯rd (≤-refl τ⋆) regs₁≤regs₂)
  instruction-cast {Δ = Δ} ψ₁⋆ {ι = st ♯rd i ♯rs} (of-st eq lookup≤τ l₁ up₁)
                      (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
    with allzipᵥ-lookup ♯rd regs₁≤regs₂ | allzipᵥ-lookup ♯rs regs₁≤regs₂
  ... | lookup-rd₁≤lookup-rd₂ | lookup-rs₁≤lookup-rs₁
    with ≤tuple⇒≡tuple (subst₂ (_⊢_≤_ Δ) refl eq lookup-rd₁≤lookup-rd₂)
  ... | τs⁻₂ , eq₁
    with subst₂ (_⊢_≤_ Δ) eq₁ eq lookup-rd₁≤lookup-rd₂
  ... | tuple-≤ τs⁻₁≤τs⁻₂
    with allzip-lookup₂ l₁ τs⁻₁≤τs⁻₂
  ... | (τ , φ) , l₂ , τ⁻-≤ τ⋆ φ₁≤φ₂
    with <-to-← τs⁻₂ (τ , init) {i} (subst (λ len → i < len) (sym (AllZip-length τs⁻₁≤τs⁻₂)) (←-to-< up₁))
  ... | τs⁻₂' , up₂
    = _ , of-st eq₁ (≤-trans lookup-rs₁≤lookup-rs₁ lookup≤τ) l₂ up₂ , Γ-≤ sp₁≤sp₂ (allzipᵥ-update ♯rd (tuple-≤ (allzip-update up₂ up₁ (τ⁻-≤ τ⋆ φ-≤-init) τs⁻₁≤τs⁻₂)) regs₁≤regs₂)
  instruction-cast ψ₁⋆ {ι = malloc ♯rd τs} (of-malloc τs⋆)
                      (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
    = _ , of-malloc τs⋆ , Γ-≤ sp₁≤sp₂ (allzipᵥ-update ♯rd (≤-refl (valid-tuple (All-map' valid-τ⁻ τs⋆))) regs₁≤regs₂)
  instruction-cast ψ₁⋆ {ι = mov ♯rd v} (of-mov v⋆)
                      (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
    with vval-cast ψ₁⋆ v⋆ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
  ... | τ' , τ≤τ' , v⋆'
    = _ , of-mov v⋆' , Γ-≤ sp₁≤sp₂ (allzipᵥ-update ♯rd τ≤τ' regs₁≤regs₂)
  instruction-cast ψ₁⋆ {ι = beq ♯r v} (of-beq eq v⋆ Γ₁≤Γ')
                      (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
    with allzipᵥ-lookup ♯r regs₁≤regs₂
       | vval-cast ψ₁⋆ v⋆ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
  ... | ♯r⋆ | ∀[ [] ] Γ'' , ∀-≤ Γ'≤Γ'' , v⋆'
    rewrite eq
    = _ , of-beq (≤int⇒≡int ♯r⋆) v⋆' (≤-trans (Γ-≤ sp₁≤sp₂ regs₁≤regs₂) (≤-trans Γ₁≤Γ' Γ'≤Γ'')) , Γ-≤ sp₁≤sp₂ regs₁≤regs₂

instructionsequence-cast : ∀ {ψ₁ Δ Γ₁ Γ₂ I} →
                             [] ⊢ ψ₁ Valid →
                             ψ₁ , Δ ⊢ I of Γ₂ instructionsequence →
                             Δ ⊢ Γ₁ ≤ Γ₂ →
                             ψ₁ , Δ ⊢ I of Γ₁ instructionsequence
instructionsequence-cast ψ₁⋆ (of-~> ι⋆ I⋆)  Γ₁≤Γ₂
  with instruction-cast ψ₁⋆ ι⋆ Γ₁≤Γ₂
... | Γ₂' , ι⋆' , Γ₂'≤Γ₁'
  with instructionsequence-cast ψ₁⋆ I⋆ Γ₂'≤Γ₁'
... | I⋆' = of-~> ι⋆' I⋆'
instructionsequence-cast ψ₁⋆ (of-jmp v⋆ Γ₁≤Γ')  Γ₁≤Γ₂
  with vval-cast ψ₁⋆ v⋆ Γ₁≤Γ₂
... | ∀[ [] ] Γ'' , ∀-≤ Γ'≤Γ'' , v⋆' = of-jmp v⋆' (≤-trans Γ₁≤Γ₂ (≤-trans Γ₁≤Γ' Γ'≤Γ''))
instructionsequence-cast ψ₁⋆ of-halt Γ₁≤Γ₂ = of-halt

wval-cast : ∀ {ψ₁ ψ₂ w τ₁ τ₂} →
              ψ₁ , ψ₂ ⊢ w of τ₁ wval →
              [] ⊢ τ₁ ≤ τ₂ →
              ψ₁ , ψ₂ ⊢ w of τ₂ wval
wval-cast (of-globval l τ≤τ₁) τ₁≤τ₂ = of-globval l (≤-trans τ≤τ₁ τ₁≤τ₂)
wval-cast (of-heapval l τ≤τ₁) τ₁≤τ₂ = of-heapval l (≤-trans τ≤τ₁ τ₁≤τ₂)
wval-cast of-int int-≤ = of-int
wval-cast of-ns ns-≤ = of-ns
wval-cast (of-Λ {Δ₂ = Δ₂} w⋆ θs⋆ subs-Γ Γ₃≤Γ₂) (∀-≤ Γ₄≤Γ₃)
  rewrite List-++-right-identity Δ₂ = of-Λ w⋆ θs⋆ subs-Γ (≤-trans Γ₄≤Γ₃ Γ₃≤Γ₂)
