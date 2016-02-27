module Lemmas.TermDec where

open import Util
open import Judgments
open import Lemmas.Equality using ()
open import Lemmas.Substitution using (subst-unique-many ; _⟦_/_⟧many?)
open import Lemmas.Types using (_⊢?_Valid ; _⊢_≤?_ ; ≤-valid₁ ; ≤-refl ; ≤-valid₂ ; ≤-trans)
open import Lemmas.TypeSubstitution
open import Lemmas.TermCast
open import Lemmas.TermValidType
open import Lemmas.TermHeapCast using (register-heapcast ; hvals-heapcast)
open HighSyntax

-- The purpose of this file is to prove that type-checking
-- is decidable.

private
  stack-lookup-unique : ∀ {n σ τ₁ τ₂} →
                        stack-lookup n σ τ₁ →
                        stack-lookup n σ τ₂ →
                        τ₁ ≡ τ₂
  stack-lookup-unique here here = refl
  stack-lookup-unique (there l₁) (there l₂) = stack-lookup-unique l₁ l₂

  stack-lookup-dec : ∀ n σ → Dec (∃ λ τ → stack-lookup n σ τ)
  stack-lookup-dec n (ρ⁼ ι) = no (λ { (_ , ()) })
  stack-lookup-dec n [] = no (λ { (_ , ()) })
  stack-lookup-dec zero (τ ∷ σ) = yes (τ , here)
  stack-lookup-dec (suc n) (τ' ∷ σ)
    with stack-lookup-dec n σ
  ... | yes (τ , lookup) = yes (τ , there lookup)
  ... | no ¬lookup = no (λ { (τ , there lookup) → ¬lookup (τ , lookup)})

  stack-update-unique : ∀ {n σ τ σ₁ σ₂} →
                        stack-update n τ σ σ₁ →
                        stack-update n τ σ σ₂ →
                        σ₁ ≡ σ₂
  stack-update-unique here here = refl
  stack-update-unique (there up₁) (there up₂) = cong₂ _∷_ refl (stack-update-unique up₁ up₂)

  stack-update-dec : ∀ n τ σ → Dec (∃ λ σ' → stack-update n τ σ σ')
  stack-update-dec n τ (ρ⁼ ι) = no (λ { (_ , ()) })
  stack-update-dec n τ [] = no (λ { (_ , ()) })
  stack-update-dec zero τ (τ' ∷ σ) = yes (τ ∷ σ , here)
  stack-update-dec (suc n) τ (τ' ∷ σ)
    with stack-update-dec n τ σ
  ... | yes (σ' , update) = yes (τ' ∷ σ' , there update)
  ... | no ¬update = no (λ { (_ , there update) → ¬update (_ , update)})

  stack-drop-unique : ∀ {n σ σ₁ σ₂} →
                        stack-drop n σ σ₁ →
                        stack-drop n σ σ₂ →
                        σ₁ ≡ σ₂
  stack-drop-unique here here = refl
  stack-drop-unique (there drop₁) (there drop₂) = stack-drop-unique drop₁ drop₂

  stack-drop-dec : ∀ n σ → Dec (∃ λ σ' → stack-drop n σ σ')
  stack-drop-dec zero σ = yes (σ , here)
  stack-drop-dec (suc n) (ρ⁼ ι) = no (λ { (_ , ()) })
  stack-drop-dec (suc n) [] = no (λ { (_ , ()) })
  stack-drop-dec (suc n) (τ ∷ σ)
    with stack-drop-dec n σ
  ... | yes (σ' , drop) = yes (σ' , there drop)
  ... | no ¬drop = no (λ { (σ' , there drop) → ¬drop (σ' , drop)})

  is-tuple : ∀ (τ : Type) → Dec (∃ λ τs⁻ → τ ≡ tuple τs⁻)
  is-tuple (α⁼ ι) = no (λ { (_ , ()) })
  is-tuple int = no (λ { (_ , ()) })
  is-tuple uninit = no (λ { (_ , ()) })
  is-tuple (∀[ Δ ] Γ) = no (λ { (_ , ()) })
  is-tuple (tuple τs⁻) = yes (τs⁻ , refl)

  is-∀ : ∀ τ → Dec (∃₂ λ Δ Γ → τ ≡ ∀[ Δ ] Γ)
  is-∀ (α⁼ ι) = no (λ { (_ , _ , ()) })
  is-∀ int = no (λ { (_ , _ , ()) })
  is-∀ uninit = no (λ { (_ , _ , ()) })
  is-∀ (∀[ Δ ] Γ) = yes (Δ , Γ , refl)
  is-∀ (tuple τs) = no (λ { (_ , _ , ()) })

  instantiation-dec : ∀ {Δ} θ a →
                        Dec (Δ ⊢ θ of a instantiation)
  instantiation-dec {Δ} (α τ) α
    = dec-inj of-α (λ { (of-α τ⋆) → τ⋆ }) (Δ ⊢? τ Valid)
  instantiation-dec (α τ) ρ = no (λ ())
  instantiation-dec (ρ σ) α = no (λ ())
  instantiation-dec {Δ} (ρ σ) ρ
    = dec-inj of-ρ (λ { (of-ρ σ⋆) → σ⋆ }) (Δ ⊢? σ Valid)

  instantiations-dec : ∀ {Δ₁} θs Δ₂ →
                         Dec (Δ₁ ⊢ θs of Δ₂ instantiations)
  instantiations-dec [] [] = yes []
  instantiations-dec [] (a ∷ Δ₂) = no (λ ())
  instantiations-dec (θ ∷ θs) [] = no (λ ())
  instantiations-dec (θ ∷ θs) (a ∷ Δ₂)
    with instantiation-dec θ a | instantiations-dec θs Δ₂
  ... | yes θ⋆ | yes θs⋆ = yes (θ⋆ ∷ θs⋆)
  ... | no ¬θ⋆ | _ = no (λ { (θ⋆ ∷ θs⋆) → ¬θ⋆ θ⋆})
  ... | _ | no ¬θs⋆ = no (λ { (θ⋆ ∷ θs⋆) → ¬θs⋆ θs⋆})

  vval-unique : ∀ {ψ₁ Δ Γ v τ₁ τ₂} →
                  ψ₁ , Δ ⊢ v of Γ ⇒ τ₁ vval →
                  ψ₁ , Δ ⊢ v of Γ ⇒ τ₂ vval →
                  τ₁ ≡ τ₂
  vval-unique of-reg of-reg = refl
  vval-unique (of-globval l₁) (of-globval l₂) = ↓-unique l₁ l₂
  vval-unique of-int of-int = refl
  vval-unique (of-Λ v⋆₁ θs⋆₁ subs-Γ₁) (of-Λ v⋆₂ θs⋆₂ subs-Γ₂)
    with vval-unique v⋆₁ v⋆₂
  vval-unique (of-Λ v⋆₁ θs⋆₁ subs-Γ₁) (of-Λ v⋆₂ θs⋆₂ subs-Γ₂)
      | refl with subst-unique-many subs-Γ₁ subs-Γ₂
  vval-unique (of-Λ v⋆₁ θs⋆₁ subs-Γ₁) (of-Λ v⋆₂ θs⋆₂ subs-Γ₂)
      | refl | refl
      = refl

  vval-helper : ∀ {ψ₁ Δ Γ v τ₁ τ₂} →
                  ψ₁ , Δ ⊢ v of Γ ⇒ τ₁ vval →
                  ψ₁ , Δ ⊢ v of Γ ⇒ τ₂ vval →
                  τ₁ ≢ τ₂ →
                  ⊥
  vval-helper v⋆₁ v⋆₂ τ₁≢τ₂
    with τ₁≢τ₂ (vval-unique v⋆₁ v⋆₂)
  ... | ()

  vval-dec : ∀ {ψ₁ Δ Γ} v →
               Dec (∃ λ τ → ψ₁ , Δ ⊢ v of Γ ⇒ τ vval)
  vval-dec (reg ♯r) = yes (_ , of-reg)
  vval-dec {ψ₁} (globval lab)
    with ↓-dec ψ₁ lab
  ... | yes (τ , l) = yes (τ , of-globval l)
  ... | no ¬l = no (λ { (_ , of-globval l) → ¬l (_ , l)})
  vval-dec (int n) = yes (int , of-int)
  vval-dec {ψ₁} {Δ} {Γ} (Λ Δₒ ∙ v ⟦ θs ⟧)
    with vval-dec {ψ₁} {Δ} {Γ} v
  ... | no ¬v⋆ = no (λ { (_ , of-Λ v⋆ θs⋆ subs-Γ) → ¬v⋆ (_ , v⋆) })
  ... | yes (α⁼ ι , v⋆) = no (λ { (_ , of-Λ v⋆' θs⋆ subs-Γ) → vval-helper v⋆ v⋆' (λ ())})
  ... | yes (int , v⋆) = no (λ { (_ , of-Λ v⋆' θs⋆ subs-Γ) → vval-helper v⋆ v⋆' (λ ())})
  ... | yes (uninit , v⋆) = no (λ { (_ , of-Λ v⋆' θs⋆ subs-Γ) → vval-helper v⋆ v⋆' (λ ())})
  ... | yes (tuple τs , v⋆) = no (λ { (_ , of-Λ v⋆' θs⋆ subs-Γ) → vval-helper v⋆ v⋆' (λ ())})
  ... | yes (∀[ Δᵢ ] Γᵢ , v⋆)
    with instantiations-dec {Δₒ ++ Δ} θs Δᵢ
  ... | no ¬θs⋆ = no (help v⋆ ¬θs⋆)
    where help : ∀ {v θs Δᵢ Γᵢ} →
                   ψ₁ , Δ ⊢ v of Γ ⇒ ∀[ Δᵢ ] Γᵢ vval →
                   ¬ Δₒ ++ Δ ⊢ θs of Δᵢ instantiations →
                   ¬ ∃ λ τ → (ψ₁ , Δ ⊢ Λ Δₒ ∙ v ⟦ θs ⟧ of Γ ⇒ τ vval)
          help v⋆ ¬θs⋆ (._ , of-Λ v⋆' θs⋆ subs-Γ)
            with vval-unique v⋆ v⋆'
          help v⋆ ¬θs⋆ (._ , of-Λ v⋆' θs⋆ subs-Γ)
              | refl
            = ¬θs⋆ θs⋆
  ... | yes θs⋆
    with weaken (length Δᵢ) (length Δₒ) Γᵢ ⟦ θs / 0 ⟧many?
  ... | yes (Γₒ , subs-Γ) = yes (_ , of-Λ v⋆ θs⋆ subs-Γ)
  ... | no ¬subs-Γ = no (help v⋆ ¬subs-Γ)
    where help : ∀ {v θs Δᵢ Γᵢ} →
                   ψ₁ , Δ ⊢ v of Γ ⇒ ∀[ Δᵢ ] Γᵢ vval →
                   ¬ (∃ λ Γₒ → weaken (length Δᵢ) (length Δₒ) Γᵢ ⟦ θs / 0 ⟧many≡ Γₒ) →
                   ¬ ∃ λ τ → (ψ₁ , Δ ⊢ Λ Δₒ ∙ v ⟦ θs ⟧ of Γ ⇒ τ vval)
          help v⋆ ¬subs-Γ (._ , of-Λ v⋆' θs⋆ subs-Γ)
            with vval-unique v⋆ v⋆'
          help v⋆ ¬subs-Γ (._ , of-Λ v⋆' θs⋆ subs-Γ)
              | refl
            = ¬subs-Γ (_ , subs-Γ)

  instruction-unique : ∀ {ψ₁ Δ Γ ι Γ₁ Γ₂} →
                         ψ₁ , Δ ⊢ ι of Γ ⇒ Γ₁ instruction →
                         ψ₁ , Δ ⊢ ι of Γ ⇒ Γ₂ instruction →
                         Γ₁ ≡ Γ₂
  instruction-unique (of-add eq₁ v⋆₁) (of-add eq₂ v⋆₂) = refl
  instruction-unique (of-sub eq₁ v⋆₁) (of-sub eq₂ v⋆₂) = refl
  instruction-unique of-salloc of-salloc = refl
  instruction-unique (of-sfree drop₁) (of-sfree drop₂)
    rewrite stack-drop-unique drop₁ drop₂ = refl
  instruction-unique (of-sld l₁) (of-sld l₂)
    rewrite stack-lookup-unique l₁ l₂ = refl
  instruction-unique (of-sst up₁) (of-sst up₂)
    rewrite stack-update-unique up₁ up₂ = refl
  instruction-unique (of-ld eq₁ l₁) (of-ld eq₂ l₂)
    with trans (sym eq₁) eq₂
  instruction-unique (of-ld eq₁ l₁) (of-ld eq₂ l₂)
      | refl with ↓-unique l₁ l₂
  instruction-unique (of-ld eq₁ l₁) (of-ld eq₂ l₂)
      | refl | refl = refl
  instruction-unique (of-st eq₁ lookup≤₁τ l₁ up₁) (of-st eq₂ lookup≤₂τ l₂ up₂)
    with trans (sym eq₁) eq₂
  instruction-unique (of-st eq₁ lookup≤₁τ l₁ up₁) (of-st eq₂ lookup≤₂τ l₂ up₂)
      | refl with ↓-unique l₁ l₂
  instruction-unique (of-st eq₁ lookup≤₁τ l₁ up₁) (of-st eq₂ lookup≤₂τ l₂ up₂)
      | refl | refl with ←-unique up₁ up₂
  instruction-unique (of-st eq₁ lookup≤₁τ l₁ up₁) (of-st eq₂ lookup≤₂τ l₂ up₂)
      | refl | refl | refl = refl
  instruction-unique (of-malloc τs⋆₁) (of-malloc τs⋆₂) = refl
  instruction-unique (of-mov v⋆₁) (of-mov v⋆₂)
    with vval-unique v⋆₁ v⋆₂
  instruction-unique (of-mov v⋆₁) (of-mov v⋆₂)
      | refl = refl
  instruction-unique (of-beq eq₁ v⋆₁ Γ≤₁Γ') (of-beq eq₂ v⋆₂ Γ≤₂Γ') = refl

  instruction-dec : ∀ {ψ₁ Δ} Γ ι →
                      Dec (∃ λ Γ' → ψ₁ , Δ ⊢ ι of Γ ⇒ Γ' instruction)
  instruction-dec {ψ₁} {Δ} Γ (add ♯rd ♯rs v)
    with vval-dec v
  ... | no ¬v⋆ = no (λ { (._ , of-add lookup≡int v⋆) → ¬v⋆ (_ , v⋆) })
  ... | yes (τ , v⋆)
    with lookup-regs ♯rs Γ ≟ int | τ ≟ int
  ... | no lookup≢int | _ = no (λ { (._ , of-add lookup≡int v⋆') → lookup≢int lookup≡int })
  ... | _ | no τ≢int = no (λ { (._ , of-add lookup≡int v⋆') → τ≢int (vval-unique v⋆ v⋆') })

  instruction-dec Γ (add ♯rd ♯rs v)
      | yes (int , v⋆) | yes lookup≡eq | yes refl
        = yes (_ , of-add lookup≡eq v⋆)

  instruction-dec {ψ₁} {Δ} Γ (sub ♯rd ♯rs v)
    with vval-dec v
  ... | no ¬v⋆ = no (λ { (._ , of-sub lookup≡int v⋆) → ¬v⋆ (_ , v⋆) })
  ... | yes (τ , v⋆)
    with lookup-regs ♯rs Γ ≟ int | τ ≟ int
  ... | no lookup≢int | _ = no (λ { (._ , of-sub lookup≡int v⋆') → lookup≢int lookup≡int })
  ... | _ | no τ≢int = no (λ { (._ , of-sub lookup≡int v⋆') → τ≢int (vval-unique v⋆ v⋆') })

  instruction-dec Γ (sub ♯rd ♯rs v)
      | yes (int , v⋆) | yes lookup≡eq | yes refl
        = yes (_ , of-sub lookup≡eq v⋆)

  instruction-dec (registerₐ σ τs) (salloc n) = yes (_ , of-salloc)

  instruction-dec (registerₐ σ τs) (sfree n)
    with stack-drop-dec n σ
  ... | yes (σ' , drop) = yes (registerₐ σ' τs , of-sfree drop)
  ... | no ¬drop = no (λ { (_ , of-sfree drop) → ¬drop (_ , drop)})

  instruction-dec (registerₐ σ τs) (sld ♯rd i)
    with stack-lookup-dec i σ
  ... | no ¬lookup = no (λ { (_ , of-sld lookup) → ¬lookup (_ , lookup)})
  ... | yes (τ , lookup) = yes (_ , of-sld lookup)

  instruction-dec (registerₐ σ τs) (sst i ♯rs)
    with stack-update-dec i (lookup ♯rs τs) σ
  ... | no ¬update = no (λ { (_ , of-sst update) → ¬update (_ , update)})
  ... | yes (σ' , update) = yes (_ , of-sst update)

  instruction-dec {ψ₁} {Δ} (registerₐ σ τs) (ld ♯rd ♯rs i)
    with is-tuple (lookup ♯rs τs)
  ... | no lookup≢tuple = no (λ { (_ , of-ld lookup≡tuple lookup) → lookup≢tuple (_ , lookup≡tuple)})
  ... | yes (τs⁻ , lookup≡tuple)
    with ↓-dec τs⁻ i
  ... | yes ((τ , init) , lookup) = yes (_ , of-ld lookup≡tuple lookup)
  ... | yes ((τ , uninit) , lookup) = no help
    where help : ¬ (∃ λ Γ → ψ₁ , Δ ⊢ ld ♯rd ♯rs i of registerₐ σ τs ⇒ Γ instruction)
          help (_ , of-ld lookup≡tuple' lookup')
            with trans (sym lookup≡tuple') lookup≡tuple
          help (_ , of-ld lookup≡tuple' lookup')
              | refl with ↓-unique lookup lookup'
          ... | ()
  ... | no ¬lookup = no help
    where help : ¬ (∃ λ Γ → ψ₁ , Δ ⊢ ld ♯rd ♯rs i of registerₐ σ τs ⇒ Γ instruction)
          help (_ , of-ld lookup≡tuple' lookup)
            with trans (sym lookup≡tuple') lookup≡tuple
          help (_ , of-ld lookup≡tuple' lookup)
              | refl = ¬lookup (_ , lookup)

  instruction-dec {ψ₁} {Δ} (registerₐ σ τs) (st ♯rd i ♯rs)
    with is-tuple (lookup ♯rd τs)
  ... | no lookup≢tuple = no (λ { (_ , of-st lookup≡tuple lookup≤τ l up) → lookup≢tuple (_ , lookup≡tuple)})
  ... | yes (τs⁻ , lookup≡tuple)
    with ↓-dec τs⁻ i
  ... | no ¬l = no help
    where help : ¬ (∃ λ Γ → ψ₁ , Δ ⊢ st ♯rd i ♯rs of registerₐ σ τs ⇒ Γ instruction)
          help (_ , of-st lookup≡tuple' lookup≤τ l up)
            with trans (sym lookup≡tuple') lookup≡tuple
          help (_ , of-st lookup≡tuple' lookup≤τ l up)
              | refl = ¬l (_ , l)
  ... | yes ((τ , φ) , l)
    with Δ ⊢ lookup ♯rs τs ≤? τ
  ... | no lookup≰τ = no help
    where help : ¬ (∃ λ Γ → ψ₁ , Δ ⊢ st ♯rd i ♯rs of registerₐ σ τs ⇒ Γ instruction)
          help (_ , of-st lookup≡tuple' lookup≤τ l up)
            with trans (sym lookup≡tuple') lookup≡tuple
          help (_ , of-st lookup≡tuple' lookup≤τ l' up)
              | refl with ↓-unique l' l
          help (_ , of-st lookup≡tuple' lookup≤τ l' up)
              | refl | refl
              = lookup≰τ lookup≤τ
  ... | yes lookup≤τ
    with <-to-← τs⁻ (τ , init) (↓-to-< l)
  ... | τs⁻' , up
    = yes (_ , of-st lookup≡tuple lookup≤τ l up)

  instruction-dec {Δ = Δ} Γ (malloc ♯r τs)
    with Δ ⊢? τs Valid
  ... | yes τs⋆ = yes (_ , of-malloc τs⋆)
  ... | no ¬τs⋆ = no (λ { (_ , of-malloc τs⋆) → ¬τs⋆ τs⋆})

  instruction-dec Γ (mov ♯rd v)
    with vval-dec v
  ... | yes (τ , v⋆) = yes (_ , of-mov v⋆)
  ... | no ¬v⋆ = no (λ { (_ , of-mov v⋆) → ¬v⋆ (_ , v⋆)})

  instruction-dec Γ (beq ♯r v)
    with lookup-regs ♯r Γ ≟ int | vval-dec v
  ... | no lookup≢int | _ = no (λ { (_ , of-beq lookup≡int v⋆ Γ≤Γ') → lookup≢int lookup≡int})
  ... | _ | no ¬v⋆ = no (λ { (_ , of-beq lookup≡int v⋆ Γ≤Γ') → ¬v⋆ (_ , v⋆)})
  ... | yes lookup≡int | yes (τ , v⋆)
    with is-∀ τ
  ... | no τ≢∀ = no (λ { (_ , of-beq lookup≡int v⋆' Γ≤Γ') → τ≢∀ (_ , _ , vval-unique v⋆ v⋆') })
  instruction-dec {ψ₁} {Δ} Γ (beq ♯r v)
      | yes lookup≡int | yes (∀[ a ∷ Δ' ] Γ' , v⋆) | yes (.(a ∷ Δ') , .Γ' , refl)
        = no help
    where help : ¬ (∃ λ Γ' → ψ₁ , Δ ⊢ beq ♯r v of Γ ⇒ Γ' instruction)
          help (_ , of-beq lookup≡int v⋆' Γ≤Γ')
            with vval-unique v⋆ v⋆'
          ... | ()
  instruction-dec {ψ₁} {Δ} Γ (beq ♯r v)
      | yes lookup≡int | yes (∀[ [] ] Γ' , v⋆) | yes (.[] , .Γ' , refl)
    with Δ ⊢ Γ ≤? Γ'
  ... | yes Γ≤Γ' = yes (Γ , of-beq lookup≡int v⋆ Γ≤Γ')
  ... | no Γ≰Γ' = no help
    where help : ¬ (∃ λ Γ' → ψ₁ , Δ ⊢ beq ♯r v of Γ ⇒ Γ' instruction)
          help (_ , of-beq lookup≡int v⋆' Γ≤Γ')
            with vval-unique v⋆ v⋆'
          help (_ , of-beq lookup≡int v⋆' Γ≤Γ')
              | refl = Γ≰Γ' Γ≤Γ'

  instructionsequence-dec : ∀ {ψ₁ Δ} I Γ →
                              Dec (ψ₁ , Δ ⊢ I of Γ instructionsequence)
  instructionsequence-dec {ψ₁} {Δ} (ι ~> I) Γ
    with instruction-dec Γ ι
  ... | no ¬ι⋆ = no (λ { (of-~> ι⋆ I⋆) → ¬ι⋆ (_ , ι⋆)})
  ... | yes (Γ' , ι⋆)
    with instructionsequence-dec I Γ'
  ... | yes I⋆ = yes (of-~> ι⋆ I⋆)
  ... | no ¬I⋆ = no help
    where help : ¬ (ψ₁ , Δ ⊢ ι ~> I of Γ instructionsequence)
          help (of-~> ι⋆' I⋆)
            rewrite instruction-unique ι⋆' ι⋆
            = ¬I⋆ I⋆
  instructionsequence-dec {ψ₁} {Δ} (jmp v) Γ
    with vval-dec {ψ₁} {Δ} {Γ} v
  ... | no ¬v⋆ = no (λ { (of-jmp v⋆ Γ≤Γ') → ¬v⋆ (_ , v⋆)})
  ... | yes (α⁼ ι , v⋆) = no (λ { (of-jmp v⋆' Γ≤Γ') → vval-helper v⋆ v⋆' (λ ()) })
  ... | yes (int , v⋆) = no (λ { (of-jmp v⋆' Γ≤Γ') → vval-helper v⋆ v⋆' (λ ()) })
  ... | yes (uninit , v⋆) = no (λ { (of-jmp v⋆' Γ≤Γ') → vval-helper v⋆ v⋆' (λ ()) })
  ... | yes (tuple x , v⋆) = no (λ { (of-jmp v⋆' Γ≤Γ') → vval-helper v⋆ v⋆' (λ ()) })
  ... | yes (∀[ a ∷ Δ' ] Γ' , v⋆) = no (λ { (of-jmp v⋆' Γ≤Γ') → vval-helper v⋆ v⋆' (λ ()) })
  ... | yes (∀[ [] ] Γ' , v⋆)
    with Δ ⊢ Γ ≤? Γ'
  ... | yes Γ≤Γ' = yes (of-jmp v⋆ Γ≤Γ')
  ... | no Γ≰Γ' = no (help v⋆ Γ≰Γ')
    where help : ψ₁ , Δ ⊢ v of Γ ⇒ ∀[ [] ] Γ' vval →
                 ¬ (Δ ⊢ Γ ≤ Γ') →
                 ¬ (ψ₁ , Δ ⊢ jmp v of Γ instructionsequence)
          help v⋆ Γ≰Γ' (of-jmp v⋆' Γ≤Γ')
            with vval-unique v⋆ v⋆'
          help v⋆ Γ≰Γ' (of-jmp v⋆' Γ≤Γ')
              | refl = Γ≰Γ' Γ≤Γ'
  instructionsequence-dec halt Γ = yes of-halt

  gval-dec : ∀ {ψ₁} g τ → Dec (ψ₁ ⊢ g of τ gval)
  gval-dec (code[ Δ ] Γ ∙ I) (α⁼ ι) = no (λ ())
  gval-dec (code[ Δ ] Γ ∙ I) int = no (λ ())
  gval-dec (code[ Δ ] Γ ∙ I) uninit = no (λ ())
  gval-dec (code[ Δ₁ ] Γ₁ ∙ I) (∀[ Δ₂ ] Γ₂)
    with Δ₁ ≟ Δ₂ | Γ₁ ≟ Γ₂
  ... | no Δ₁≢Δ₂ | _ = no (help Δ₁≢Δ₂)
    where help : ∀ {ψ₁ Δ₁ Γ₁ I Δ₂ Γ₂} →
                   Δ₁ ≢ Δ₂ →
                   ¬ (ψ₁ ⊢ code[ Δ₁ ] Γ₁ ∙ I of ∀[ Δ₂ ] Γ₂ gval)
          help neq (of-gval Γ⋆ I⋆) = neq refl
  ... | _ | no Γ₁≢Γ₂ = no (help Γ₁≢Γ₂)
    where help : ∀ {ψ₁ Δ₁ Γ₁ I Δ₂ Γ₂} →
                   Γ₁ ≢ Γ₂ →
                   ¬ (ψ₁ ⊢ code[ Δ₁ ] Γ₁ ∙ I of ∀[ Δ₂ ] Γ₂ gval)
          help neq (of-gval Γ⋆ I⋆) = neq refl
  gval-dec {ψ₁} (code[ Δ ] Γ ∙ I) (∀[ .Δ ] .Γ)
      | yes refl | yes refl
      with Δ ⊢? Γ Valid | instructionsequence-dec I Γ
  ... | yes Γ⋆ | yes I⋆ = yes (of-gval Γ⋆ I⋆)
  ... | no ¬Γ⋆ | _ = no (λ { (of-gval Γ⋆ I⋆) → ¬Γ⋆ Γ⋆})
  ... | _ | no ¬I⋆ = no (λ { (of-gval Γ⋆ I⋆) → ¬I⋆ I⋆})
  gval-dec (code[ Δ ] Γ ∙ I) (tuple τs) = no (λ ())

  gvals-dec : ∀ {ψ₁} gs τs → Dec (AllZip (λ g τ → ψ₁ ⊢ g of τ gval) gs τs)
  gvals-dec [] [] = yes []
  gvals-dec [] (τ ∷ τs) = no (λ ())
  gvals-dec (g ∷ gs) [] = no (λ ())
  gvals-dec (g ∷ gs) (τ ∷ τs)
    with gval-dec g τ | gvals-dec gs τs
  ... | yes g⋆ | yes gs⋆ = yes (g⋆ ∷ gs⋆)
  ... | no ¬g⋆ | _ = no (λ { (g⋆ ∷ gs⋆) → ¬g⋆ g⋆ })
  ... | _ | no ¬gs⋆ = no (λ { (g⋆ ∷ gs⋆) → ¬gs⋆ gs⋆ })

  gval-unique : ∀ g →
                ∃ λ τ →
                  (∀ {ψ₁ τ'} → ψ₁ ⊢ g of τ' gval → τ' ≡ τ)
  gval-unique (code[ Δ ] Γ ∙ I)
    = ∀[ Δ ] Γ , λ { {ψ₁} {._} (of-gval Γ⋆ I⋆) → refl}

  gvals-unique : ∀ gs →
                   ∃ λ τs →
                       (∀ {ψ₁ τs'} → AllZip (λ g τ → ψ₁ ⊢ g of τ gval) gs τs' → τs' ≡ τs)
  gvals-unique []
    = [] , (λ { {ψ₁} {[]} [] → refl ; {ψ₁} {τ' ∷ τs'} () })
  gvals-unique (g ∷ gs)
    with gval-unique g | gvals-unique gs
  ... | τ , τ-eq | τs , τs-eq
    = τ ∷ τs , λ { {ψ₁} {._} (g⋆ ∷ gs⋆) → cong₂ _∷_ (τ-eq g⋆) (τs-eq gs⋆) }

  globals-dec : ∀ G →
                  ¬ (∃ λ τs  → ⊢ G of τs globals) ∨
                    (∃ λ τs  → ⊢ G of τs globals ×
                       ∀ τs' → ⊢ G of τs' globals → τs' ≡ τs)
  globals-dec gs
    with gvals-unique gs
  ... | τs , τs-eq
    with gvals-dec {τs} gs τs
  ... | yes gs⋆ = inj₂ (τs , of-globals gs⋆ , (λ { τs' (of-globals gs⋆') → τs-eq gs⋆' }))
  ... | no ¬gs⋆ = inj₁ (help τs-eq ¬gs⋆)
    where help : ∀ {gs τs} →
                   (∀ {ψ₁ τs'} → AllZip (λ g τ → ψ₁ ⊢ g of τ gval) gs τs' → τs' ≡ τs) →
                   ¬ AllZip (λ g τ → τs ⊢ g of τ gval) gs τs →
                   ¬ ∃ λ τs → ⊢ gs of τs globals
          help τs-eq ¬gs⋆ (τs , of-globals gs⋆)
            rewrite τs-eq gs⋆
              = ¬gs⋆ gs⋆

  wval⁰-best : ∀ w τ →
                 ∃ λ φ →
                   (∀ {ψ₁ ψ₂ φ'} → ψ₁ , ψ₂ ⊢ w of τ , φ' wval⁰ → φ ≤φ φ' × ψ₁ , ψ₂ ⊢ w of τ , φ wval⁰)
  wval⁰-best w τ
    with w ≟ uninit | τ ≟ uninit
  wval⁰-best .uninit .uninit
      | yes refl | yes refl = init , (λ _ → φ-≤-init , of-init of-uninit)
  wval⁰-best .uninit τ
      | yes refl | no τ≢uninit = uninit , help τ≢uninit
      where help : ∀ {ψ₁ ψ₂ φ' τ} →
                     τ ≢ uninit →
                     ψ₁ , ψ₂ ⊢ uninit of τ , φ' wval⁰ →
                     uninit ≤φ φ' × ψ₁ , ψ₂ ⊢ uninit of τ , uninit wval⁰
            help τ≢uninit (of-uninit τ⋆) = φ-≤-uninit , of-uninit τ⋆
            help τ≢uninit (of-init of-uninit)
              with τ≢uninit refl
            ... | ()
  wval⁰-best w τ
      | no w≢uninit | _ = init , help w≢uninit
      where help : ∀ {ψ₁ ψ₂ φ' w} → w ≢ uninit →
                     ψ₁ , ψ₂ ⊢ w of τ , φ' wval⁰ →
                     init ≤φ φ' × ψ₁ , ψ₂ ⊢ w of τ , init wval⁰
            help w≢uninit (of-uninit τ⋆)
              with w≢uninit refl
            ... | ()
            help w≢uninit (of-init w⋆) = φ-≤-init , of-init w⋆

  wvals⁰-best : ∀ ws τs →
                  ∃ λ τs⁻ →
                    AllZip (λ { τ (τ' , φ) → τ ≡ τ' }) τs τs⁻ ×
                    (∀ {ψ₁ ψ₂ τs⁻'} →
                       [] ⊢ τs⁻' Valid →
                       AllZip (λ { τ (τ' , φ) → τ ≡ τ' }) τs τs⁻' →
                       AllZip (λ w τ⁻ → ψ₁ , ψ₂ ⊢ w of τ⁻ wval⁰) ws τs⁻' →
                       [] ⊢ τs⁻ ≤ τs⁻' ×
                       AllZip (λ w τ⁻ → ψ₁ , ψ₂ ⊢ w of τ⁻ wval⁰) ws τs⁻)
  wvals⁰-best [] [] = [] , [] , (λ { {τs⁻' = []} [] [] [] → [] , []})
  wvals⁰-best [] (τ ∷ τs)
    with wvals⁰-best [] τs
  ... | τs⁻ , eqs , τs⁻-best
    = (τ , uninit) ∷ τs⁻ , refl ∷ eqs , (λ { {τs⁻' = []} [] () [] })
  wvals⁰-best (w ∷ ws) [] = [] , [] , (λ { {τs⁻' = []} [] [] () })
  wvals⁰-best (w ∷ ws) (τ ∷ τs)
    with wval⁰-best w τ | wvals⁰-best ws τs
  ... | φ , φ-best | τs⁻ , eqs , τs⁻-best
    = (τ , φ) ∷ τs⁻ , refl ∷ eqs , help
      where help : ∀ {ψ₁ ψ₂ τs⁻'} →
                     [] ⊢ τs⁻' Valid →
                     AllZip (λ { τ (τ' , φ) → τ ≡ τ'}) (τ ∷ τs) τs⁻' →
                     AllZip (λ w τ⁻ → ψ₁ , ψ₂ ⊢ w of τ⁻ wval⁰) (w ∷ ws) τs⁻' →
                     [] ⊢ (τ , φ) ∷ τs⁻ ≤ τs⁻' ×
                     AllZip (λ w τ⁻ → ψ₁ , ψ₂ ⊢ w of τ⁻ wval⁰) (w ∷ ws) ((τ , φ) ∷ τs⁻)
            help (valid-τ⁻ τ⋆ ∷ τs⁻⋆) (refl ∷ eqs) (w⋆ ∷ ws⋆)
              with φ-best w⋆ | τs⁻-best τs⁻⋆ eqs ws⋆
            ... | φ≤φ' , w⋆' | τs⁻≤τs⁻' , ws⋆'
              = ((τ⁻-≤ τ⋆ φ≤φ') ∷ τs⁻≤τs⁻') , w⋆' ∷ ws⋆'

  hval-best : ∀ h →
                ∃ λ τ →
                  (∀ {ψ₁ ψ₂ τ'} →
                     [] ⊢ τ' Valid →
                     ψ₁ , ψ₂ ⊢ h of τ' hval → [] ⊢ τ ≤ τ' × ψ₁ , ψ₂ ⊢ h of τ hval)
  hval-best (tuple τs ws)
    with wvals⁰-best ws τs
  ... | τs⁻ , eqs , τs⁻-best
    = tuple τs⁻ , λ { {τ' = ._} (valid-tuple τs⁻⋆) (of-tuple eqs' ws⋆) →
                    Σ-map tuple-≤ (of-tuple eqs) (τs⁻-best τs⁻⋆ eqs' ws⋆) }

  hvals-best : ∀ hs →
                 ∃ λ τs →
                   (∀ {ψ₁ ψ₂ τs'} →
                      All (λ τ' → [] ⊢ τ' Valid) τs' →
                      AllZip (λ h τ' → ψ₁ , ψ₂ ⊢ h of τ' hval) hs τs' →
                      AllZip (λ τ τ' → [] ⊢ τ ≤ τ') τs τs' ×
                      AllZip (λ h τ → ψ₁ , ψ₂ ⊢ h of τ hval) hs τs)
  hvals-best [] = [] , (λ { {τs' = []} [] [] → [] , []})
  hvals-best (h ∷ hs)
    = Σ-zip _∷_ (λ τ-best τs-best →
        λ { {τs' = ._} (τ'⋆ ∷ τs'⋆) (h⋆ ∷ hs⋆) → Σ-zip _∷_ _∷_ (τ-best τ'⋆ h⋆) (τs-best τs'⋆ hs⋆)}
      ) (hval-best h) (hvals-best hs)

  wval-best : ∀ {ψ₁} {ψ₂} w →
                ¬ (∃ λ τ → ψ₁ , ψ₂ ⊢ w of τ wval) ∨
                  (∃ λ τ → ψ₁ , ψ₂ ⊢ w of τ wval ×
                           ∀ τ' → ψ₁ , ψ₂ ⊢ w of τ' wval → [] ⊢ τ ≤ τ')
  wval-best {ψ₁} {ψ₂} (globval lab)
    with ↓-dec ψ₁ lab
  ... | no ¬l = inj₁ (λ { (_ , of-globval l τ≤τ') → ¬l (_ , l)})
  ... | yes (τ , l)
    with [] ⊢? τ Valid
  ... | no ¬τ⋆ = inj₁ help
    where help : ¬ (∃ λ τ' → ψ₁ , ψ₂ ⊢ globval lab of τ' wval)
          help (τ' , of-globval l' τ≤τ')
            rewrite ↓-unique l' l = ¬τ⋆ (≤-valid₁ τ≤τ')
  ... | yes τ⋆ = inj₂ (τ , of-globval l (≤-refl τ⋆) , help)
    where help : ∀ τ' → ψ₁ , ψ₂ ⊢ globval lab of τ' wval → [] ⊢ τ ≤ τ'
          help τ' (of-globval l' τ≤τ')
            rewrite ↓-unique l' l = τ≤τ'
  wval-best {ψ₁} {ψ₂} (heapval labₕ)
    with ↓-dec ψ₂ labₕ
  ... | no ¬l = inj₁ (λ { (_ , of-heapval l τ≤τ') → ¬l (_ , l)})
  ... | yes (τ , l)
    with [] ⊢? τ Valid
  ... | no ¬τ⋆ = inj₁ help
    where help : ¬ (∃ λ τ' → ψ₁ , ψ₂ ⊢ heapval labₕ of τ' wval)
          help (τ' , of-heapval l' τ≤τ')
            rewrite ↓-unique l' l = ¬τ⋆ (≤-valid₁ τ≤τ')
  ... | yes τ⋆ = inj₂ (τ , of-heapval l (≤-refl τ⋆) , help)
    where help : ∀ τ' → ψ₁ , ψ₂ ⊢ heapval labₕ of τ' wval → [] ⊢ τ ≤ τ'
          help τ' (of-heapval l' τ≤τ')
            rewrite ↓-unique l' l = τ≤τ'
  wval-best (int n) = inj₂ (_ , of-int , (λ { .int of-int → int-≤ }))
  wval-best uninit = inj₂ (_ , of-uninit , (λ { .uninit of-uninit → uninit-≤ }))
  wval-best {ψ₁} {ψ₂} (Λ Δ₂ ∙ w ⟦ θs ⟧)
    with wval-best w
  ... | inj₁ ¬w⋆ = inj₁ (λ { (_ , of-Λ w⋆ θs⋆ subs-Γ Γ₃≤Γ₂) → ¬w⋆ (_ , w⋆) })
  ... | inj₂ (τ , w⋆ , w⋆-best)
    with is-∀ τ
  ... | no τ≢∀ = inj₁ (help w⋆-best τ≢∀)
    where help : ∀ {τ} →
                   (∀ τ' → ψ₁ , ψ₂ ⊢ w of τ' wval → [] ⊢ τ ≤ τ') →
                   ¬ (∃₂ λ Δ₁ Γ₁ → τ ≡ ∀[ Δ₁ ] Γ₁) →
                   ¬ (∃ λ τ' → ψ₁ , ψ₂ ⊢ Λ Δ₂ ∙ w ⟦ θs ⟧ of τ' wval)
          help w⋆-best τ≢∀ (_ , of-Λ w⋆' θs⋆ subs-Γ Γ₃≤Γ₂)
            with w⋆-best _ w⋆'
          help w⋆-best τ≢∀ (_ , of-Λ w⋆' θs⋆ subs-Γ Γ₃≤Γ₂)
              | ∀-≤ Γ≤Γ' = τ≢∀ (_ , _ , refl)
  wval-best {ψ₁} {ψ₂} (Λ Δ₂ ∙ w ⟦ θs ⟧)
      | inj₂ (∀[ Δ₁ ] Γ₁ , w⋆ , w⋆-best) | yes (.Δ₁ , .Γ₁ , refl)
      with instantiations-dec {Δ₂} θs Δ₁
  ... | no ¬θs⋆ = inj₁ help
    where help : ¬ (∃ λ τ → ψ₁ , ψ₂ ⊢ Λ Δ₂ ∙ w ⟦ θs ⟧ of τ wval)
          help (_ , of-Λ w⋆' θs⋆ subs-Γ Γ₃≤Γ₂)
            with w⋆-best _ w⋆'
          help (_ , of-Λ w⋆' θs⋆ subs-Γ Γ₃≤Γ₂)
              | ∀-≤ Γ≤Γ' = ¬θs⋆ θs⋆
  ... | yes θs⋆
    with Γ₁ ⟦ θs / 0 ⟧many?
  ... | no ¬subs-Γ = inj₁ help
    where help : ¬ (∃ λ τ → ψ₁ , ψ₂ ⊢ Λ Δ₂ ∙ w ⟦ θs ⟧ of τ wval)
          help (_ , of-Λ w⋆' θs⋆ subs-Γ Γ₃≤Γ₂)
            with w⋆-best _ w⋆'
          help (_ , of-Λ w⋆' θs⋆ subs-Γ Γ₃≤Γ₂)
              | ∀-≤ Γ₁ᵣ≤Γ₁
            rewrite List-++-right-identity Δ₁
            with subtype-subst-exists-many {{RegisterAssignment-TypeSubstitution}} [] θs⋆ (≤-++ Γ₁ᵣ≤Γ₁)
          ... | Γ₂ᵣ , Γ₂' , subs-Γᵣ' , subs-Γ' , Γ₂ᵣ≤Γ₂'
            = ¬subs-Γ (Γ₂' , subs-Γ')
  ... | yes (Γ₂ , subs-Γ)
    with Δ₂ ⊢? Γ₂ Valid
  ... | no ¬Γ₂⋆ = inj₁ help
    where help : ¬ (∃ λ τ → ψ₁ , ψ₂ ⊢ Λ Δ₂ ∙ w ⟦ θs ⟧ of τ wval)
          help (_ , of-Λ w⋆' θs⋆ subs-Γᵣ Γ₃≤Γ₂)
            with w⋆-best _ w⋆'
          help (_ , of-Λ w⋆' θs⋆ subs-Γᵣ Γ₃≤Γ₂)
              | ∀-≤ Γ₁ᵣ≤Γ₁
            rewrite List-++-right-identity Δ₁
            = ¬Γ₂⋆ (valid-subst-many [] θs⋆ (≤-valid₂ (≤-++ Γ₁ᵣ≤Γ₁)) subs-Γ)
  ... | yes Γ₂⋆
    = inj₂ (_ , of-Λ w⋆ θs⋆ subs-Γ (≤-refl Γ₂⋆) , help)
      where help : ∀ τ' →
                     ψ₁ , ψ₂ ⊢ Λ Δ₂ ∙ w ⟦ θs ⟧ of τ' wval →
                     [] ⊢ ∀[ Δ₂ ] Γ₂ ≤ τ'
            help _ (of-Λ w⋆ θs⋆ subs-Γ' Γ₃≤Γ₂)
              with w⋆-best _ w⋆
            help _ (of-Λ w⋆ θs⋆ subs-Γᵣ Γᵣ₃≤Γᵣ₂)
                | ∀-≤ Γ₁ᵣ≤Γ₁
              rewrite List-++-right-identity Δ₁
              with subtype-subst-exists-many {{RegisterAssignment-TypeSubstitution}} [] θs⋆ (≤-++ Γ₁ᵣ≤Γ₁)
            ... | Γ₂ᵣ , Γ₂' , subs-Γᵣ' , subs-Γ' , Γ₂ᵣ≤Γ₂'
              rewrite subst-unique-many subs-Γᵣ' subs-Γᵣ
                    | subst-unique-many subs-Γ' subs-Γ
              = ∀-≤ (≤-++ (≤-trans Γᵣ₃≤Γᵣ₂ Γ₂ᵣ≤Γ₂'))

  wval-dec : ∀ {ψ₁} {ψ₂} w τ → Dec (ψ₁ , ψ₂ ⊢ w of τ wval)
  wval-dec w τ
    with wval-best w
  ... | inj₁ ¬w⋆ = no (λ w⋆ → ¬w⋆ (_ , w⋆))
  ... | inj₂ (τ' , w⋆ , w⋆-best)
    with [] ⊢ τ' ≤? τ
  ... | yes τ'≤τ = yes (wval-cast w⋆ τ'≤τ)
  ... | no τ'≰τ = no (λ w⋆' → τ'≰τ (w⋆-best τ w⋆'))

  wval⁰-dec : ∀ {ψ₁} {ψ₂} w τ⁻ → Dec (ψ₁ , ψ₂ ⊢ w of τ⁻ wval⁰)
  wval⁰-dec {ψ₁} {ψ₂} w (τ , φ)
    with wval-dec w τ
  ... | yes w⋆ = yes (of-init w⋆)
  ... | no ¬w⋆
    with w ≟ uninit
  ... | no w≢uninit = no (help w≢uninit ¬w⋆)
    where help : ∀ {w τ φ} → w ≢ uninit →
                   ¬ (ψ₁ , ψ₂ ⊢ w of τ wval) →
                   ¬ (ψ₁ , ψ₂ ⊢ w of τ , φ wval⁰)
          help w≢uninit ¬w⋆ (of-uninit τ⋆) = w≢uninit refl
          help w≢uninit ¬w⋆ (of-init w⋆) = ¬w⋆ w⋆
  wval⁰-dec uninit (τ , init)
      | no ¬w⋆ | yes refl = no (λ { (of-init w⋆) → ¬w⋆ w⋆ })
  wval⁰-dec uninit (τ , uninit)
      | no ¬w⋆ | yes refl
    with [] ⊢? τ Valid
  ... | yes τ⋆ = yes (of-uninit τ⋆)
  ... | no ¬τ⋆ = no (λ { (of-uninit τ⋆) → ¬τ⋆ τ⋆ ; (of-init w⋆) → ¬w⋆ w⋆ })

  hval-dec : ∀ {ψ₁} {ψ₂} h τ → Dec (ψ₁ , ψ₂ ⊢ h of τ hval)
  hval-dec (tuple τs ws) (α⁼ ι) = no (λ ())
  hval-dec (tuple τs ws) int = no (λ ())
  hval-dec (tuple τs ws) uninit = no (λ ())
  hval-dec (tuple τs ws) (∀[ Δ ] Γ) = no (λ ())
  hval-dec (tuple τs ws) (tuple τs⁻)
    with AllZip-dec (λ { τ (τ' , φ) → τ ≟ τ' }) τs τs⁻
       | AllZip-dec wval⁰-dec ws τs⁻
  ... | yes eqs | yes ws⋆ = yes (of-tuple eqs ws⋆)
  ... | no ¬eqs | _ = no (λ { (of-tuple eqs ws⋆) → ¬eqs eqs})
  ... | _ | no ¬ws⋆ = no (λ { (of-tuple eqs ws⋆) → ¬ws⋆ ws⋆})

  heap-dec : ∀ {ψ₁} H ψ₂ → Dec (ψ₁ ⊢ H of ψ₂ heap)
  heap-dec H ψ₂ = dec-inj of-heap (λ { (of-heap hs⋆) → hs⋆ }) (AllZip-dec hval-dec H ψ₂)

  heap-best : ∀ {ψ₁} H →
                ¬ (∃ λ ψ₂ → ψ₁ ⊢ H of ψ₂ heap) ∨
                  (∃ λ ψ₂ → ψ₁ ⊢ H of ψ₂ heap ×
                            ∀ ψ₂' → ψ₁ ⊢ H of ψ₂' heap → [] ⊢ ψ₂ ≤ ψ₂')
  heap-best {ψ₁} H
    with hvals-best H
  ... | τs , τs-best
    with heap-dec H τs
  ... | no ¬H⋆ = inj₁ help
    where help : ¬ (∃ λ ψ₂ → ψ₁ ⊢ H of ψ₂ heap)
          help (ψ₂ , of-heap hs⋆)
            with τs-best (AllZip-extract→ hval-valid-type hs⋆) hs⋆
          ... | τs≤ψ₂ , hs⋆' = ¬H⋆ (of-heap (hvals-heapcast τs≤ψ₂ hs⋆'))
  ... | yes H⋆
    = inj₂ (τs , H⋆ , λ { ψ₂' (of-heap hs⋆) → proj₁ (τs-best (AllZip-extract→ hval-valid-type hs⋆) hs⋆)})

  stack-best : ∀ {ψ₁} {ψ₂} sp →
                  ¬ (∃ λ σ → ψ₁ , ψ₂ ⊢ sp of σ stack) ∨
                    (∃ λ σ → ψ₁ , ψ₂ ⊢ sp of σ stack ×
                             ∀ σ' → ψ₁ , ψ₂ ⊢ sp of σ' stack → [] ⊢ σ ≤ σ')
  stack-best [] = inj₂ ([] , [] , (λ { [] [] → []}))
  stack-best (w ∷ sp)
    with wval-best w | stack-best sp
  ... | inj₁ ¬w⋆ | _ = inj₁ (λ { (w ∷ sp , w⋆ ∷ sp⋆) → ¬w⋆ (w , w⋆) })
  ... | _ | inj₁ ¬sp⋆ = inj₁ (λ { (w ∷ sp , w⋆ ∷ sp⋆) → ¬sp⋆ (sp , sp⋆) })
  ... | inj₂ (τ , w⋆ , w⋆-best) | inj₂ (σ , sp⋆ , sp⋆-best)
    = inj₂ (τ ∷ σ , w⋆ ∷ sp⋆ , (λ { ._ (w⋆' ∷ sp⋆') → w⋆-best _ w⋆' ∷ sp⋆-best _ sp⋆' }))

  regs-best : ∀ {ψ₁} {ψ₂} {n} (regs : Vec WordValue n) →
                 ¬ (∃ λ τs → AllZipᵥ (λ w τ → ψ₁ , ψ₂ ⊢ w of τ wval) regs τs) ∨
                   (∃ λ τs → AllZipᵥ (λ w τ → ψ₁ , ψ₂ ⊢ w of τ wval) regs τs ×
                             ∀ τs' → AllZipᵥ (λ w τ → ψ₁ , ψ₂ ⊢ w of τ wval) regs τs' → [] ⊢ τs ≤ τs')
  regs-best [] = inj₂ ([] , [] , (λ { [] [] → []}))
  regs-best (w ∷ regs)
    with wval-best w | regs-best regs
  ... | inj₁ ¬w⋆ | _ = inj₁ (λ { (w ∷ regs , w⋆ ∷ regs⋆) → ¬w⋆ (w , w⋆) })
  ... | _ | inj₁ ¬regs⋆ = inj₁ (λ { (w ∷ regs , w⋆ ∷ regs⋆) → ¬regs⋆ (regs , regs⋆) })
  ... | inj₂ (τ , w⋆ , w⋆-best) | inj₂ (σ , regs⋆ , regs⋆-best)
    = inj₂ (τ ∷ σ , w⋆ ∷ regs⋆ , (λ { ._ (w⋆' ∷ regs⋆') → w⋆-best _ w⋆' ∷ regs⋆-best _ regs⋆' }))

  register-best : ∀ {ψ₁} {ψ₂} R →
                    ¬ (∃ λ Γ → ψ₁ , ψ₂ ⊢ R of Γ register) ∨
                      (∃ λ Γ → ψ₁ , ψ₂ ⊢ R of Γ register ×
                               ∀ Γ' → ψ₁ , ψ₂ ⊢ R of Γ' register → [] ⊢ Γ ≤ Γ')
  register-best (register sp regs)
    with stack-best sp | regs-best regs
  ... | inj₁ ¬sp⋆ | _ = inj₁ (λ { (_ , of-register sp⋆ regs⋆) → ¬sp⋆ (_ , sp⋆) })
  ... | _ | inj₁ ¬regs⋆ = inj₁ (λ { (_ , of-register sp⋆ regs⋆) → ¬regs⋆ (_ , regs⋆) })
  ... | inj₂ (σ , sp⋆ , sp⋆-best) | inj₂ (τs , regs⋆ , regs⋆-best)
    = inj₂ (_ , of-register sp⋆ regs⋆ , (λ { ._ (of-register sp⋆' regs⋆') → Γ-≤ (sp⋆-best _ sp⋆') (regs⋆-best _ regs⋆') }))

  mutprogramstate-dec : ∀ {ψ₁} →
                          [] ⊢ ψ₁ Valid →
                          ∀ Pₘ → Dec (∃₂ λ ψ₂ Γ → ψ₁ ⊢ Pₘ of ψ₂ , Γ mutprogramstate)
  mutprogramstate-dec {ψ₁} ψ₁⋆ (H , R , I)
    with heap-best H
  ... | inj₁ ¬H⋆ = no (λ { (ψ₂ , Γ , of-mutprogramstate H⋆ R⋆ I⋆) → ¬H⋆ (_ , H⋆)})
  ... | inj₂ (ψ₂ , H⋆ , ψ₂-best)
    with register-best R
  ... | inj₁ ¬R⋆ = no (λ { (ψ₂' , Γ , of-mutprogramstate H⋆ R⋆ I⋆) → ¬R⋆ (_ , register-heapcast (ψ₂-best _ H⋆) R⋆)})
  ... | inj₂ (Γ , R⋆ , Γ-best)
    with instructionsequence-dec I Γ
  ... | yes I⋆ = yes (ψ₂ , Γ , of-mutprogramstate H⋆ R⋆ I⋆)
  ... | no ¬I⋆ = no (λ { (ψ₂' , Γ' , of-mutprogramstate H⋆ R⋆ I⋆) → ¬I⋆ (instructionsequence-cast ψ₁⋆ I⋆ (Γ-best _ (register-heapcast (ψ₂-best _ H⋆) R⋆)))})

programstate-dec : ∀ P → Dec (⊢ P programstate)
programstate-dec (G , Pₘ)
  with globals-dec G
... | inj₁ ¬G⋆ = no (λ { (of-programstate G⋆ Pₘ⋆) → ¬G⋆ (_ , G⋆) })
... | inj₂ (ψ₁ , G⋆ , ψ₁-unique)
  with mutprogramstate-dec (globals-valid-type G⋆) Pₘ
... | yes (ψ₂ , Γ , Pₘ⋆) = yes (of-programstate G⋆ Pₘ⋆)
... | no ¬Pₘ⋆ = no help
  where help : ¬ ⊢ G , Pₘ programstate
        help (of-programstate G⋆' Pₘ⋆)
          rewrite ψ₁-unique _ G⋆' = ¬Pₘ⋆ (_ , _ , Pₘ⋆)
