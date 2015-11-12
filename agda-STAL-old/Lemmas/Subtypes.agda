module Lemmas.Subtypes where

open import Util
open import Judgments
open import Lemmas.Types

-- The purpose of this file is to create instance
-- of the following record:
record Subtype⁺ (A : Set) {{T : TypeLike A}} {{S : Subtype A}} : Set1 where
  constructor subtype⁺
  infix 3 _⊢_≤?_
  field
    _⊢_≤?_ : ∀ Δ (v₁ v₂ : A) → Dec (Δ ⊢ v₁ ≤ v₂)
    ≤-refl : ∀ {Δ} {v : A} → Δ ⊢ v Valid → Δ ⊢ v ≤ v
    ≤-trans : ∀ {Δ} {v₁ v₂ v₃ : A} → Δ ⊢ v₁ ≤ v₂ → Δ ⊢ v₂ ≤ v₃ → Δ ⊢ v₁ ≤ v₃
    ≤-valid : ∀ {Δ} {v₁ v₂ : A} → Δ ⊢ v₁ ≤ v₂ → Δ ⊢ v₁ Valid × Δ ⊢ v₂ Valid
    ≤-++ : ∀ {Δ Δ'} {v₁ v₂ : A} → Δ ⊢ v₁ ≤ v₂ → Δ ++ Δ' ⊢ v₁ ≤ v₂
    ≤-change₁ : ∀ {Δ₁ Δ₂} {v₁ v₂ : A} →
                  Δ₁ ⊢ v₁ ≤ v₂ →
                  Δ₂ ⊢ v₁ Valid →
                  Δ₂ ⊢ v₁ ≤ v₂
    ≤-change₂ : ∀ {Δ₁ Δ₂} {v₁ v₂ : A} →
                  Δ₁ ⊢ v₁ ≤ v₂ →
                  Δ₂ ⊢ v₂ Valid →
                  Δ₂ ⊢ v₁ ≤ v₂
open Subtype⁺ {{...}} public

private
  infix 3 _≤φ?_
  _≤φ?_ : ∀ φ₁ φ₂ → Dec (φ₁ ≤φ φ₂)
  init ≤φ? init = yes φ-≤-init
  uninit ≤φ? init = no (λ ())
  _ ≤φ? uninit = yes φ-≤-uninit

  mutual
    infix 3 _⊢_≤τ?_
    _⊢_≤τ?_ : ∀ Δ τ₁ τ₂ → Dec (Δ ⊢ τ₁ ≤τ τ₂)
    Δ ⊢ α⁼ ι₁ ≤τ? α⁼ ι₂ with ι₁ ≟ ι₂ | ↓-decᵥ Δ ι₁ α
    Δ ⊢ α⁼ ι ≤τ? α⁼ .ι | yes refl | yes l = yes (α⁼-≤ l)
    Δ ⊢ α⁼ ι  ≤τ? α⁼ .ι | yes refl | no ¬l =
      no (λ { (α⁼-≤ l) → ¬l l })
    Δ ⊢ α⁼ ι₁ ≤τ? α⁼ ι₂ | no ι₁≢ι₂ | _ = no (ι₁≢ι₂ ∘ help)
      where help : ∀ {Δ ι₁ ι₂} → Δ ⊢ α⁼ ι₁ ≤τ α⁼ ι₂ → ι₁ ≡ ι₂
            help (α⁼-≤ l) = refl
    Δ ⊢ α⁼ ι₁ ≤τ? int = no (λ ())
    Δ ⊢ α⁼ ι₁ ≤τ? ns = no (λ ())
    Δ ⊢ α⁼ ι₁ ≤τ? (∀[ Δ₂ ] Γ₂) = no (λ ())
    Δ ⊢ α⁼ ι₁ ≤τ? tuple τs₂ = no (λ ())
    Δ ⊢ int ≤τ? α⁼ ι₂ = no (λ ())
    Δ ⊢ int ≤τ? int = yes int-≤
    Δ ⊢ int ≤τ? ns = no (λ ())
    Δ ⊢ int ≤τ? (∀[ Δ₂ ] Γ₂) = no (λ ())
    Δ ⊢ int ≤τ? tuple τs₂ = no (λ ())
    Δ ⊢ ns ≤τ? α⁼ ι₂ = no (λ ())
    Δ ⊢ ns ≤τ? int = no (λ ())
    Δ ⊢ ns ≤τ? ns = yes ns-≤
    Δ ⊢ ns ≤τ? (∀[ Δ₂ ] Γ₂) = no (λ ())
    Δ ⊢ ns ≤τ? tuple τs₂ = no (λ ())
    Δ ⊢ ∀[ Δ₁ ] Γ₁ ≤τ? α⁼ ι₂ = no (λ ())
    Δ ⊢ ∀[ Δ₁ ] Γ₁ ≤τ? int = no (λ ())
    Δ ⊢ ∀[ Δ₁ ] Γ₁ ≤τ? ns = no (λ ())
    Δ ⊢ ∀[ Δ₁ ] Γ₁ ≤τ? (∀[ Δ₂ ] Γ₂)
      with Δ₁ ≟ Δ₂ | Δ ⊢? Δ₁ Valid | Δ₁ ++ Δ ⊢ Γ₁ ≤Γ? Γ₂
    Δ ⊢ ∀[ Δ' ] Γ₁ ≤τ? (∀[ .Δ' ] Γ₂)
      | yes refl | yes Δ'⋆ | yes Γ₁≤Γ₂ = yes (∀-≤ Δ'⋆ Γ₁≤Γ₂)
    Δ ⊢ ∀[ Δ' ] Γ₁ ≤τ? (∀[ .Δ' ] Γ₂)
      | yes refl | no ¬Δ'* | _ = no (λ { (∀-≤ Δ'⋆ Γ₁≤Γ₂) → ¬Δ'* Δ'⋆ })
    Δ ⊢ ∀[ Δ' ] Γ₁ ≤τ? (∀[ .Δ' ] Γ₂)
      | yes refl | _ | no Γ₁≰Γ₂  = no (λ { (∀-≤ Δ'⋆ Γ₁≤Γ₂) → Γ₁≰Γ₂ Γ₁≤Γ₂ })
    Δ ⊢ ∀[ Δ₁ ] Γ₁ ≤τ? (∀[ Δ₂ ] Γ₂) | no Δ₁≢Δ₂ | _ | _ = no (Δ₁≢Δ₂ ∘ help)
      where help : ∀ {Δ Δ₁ Δ₂ Γ₁ Γ₂} → Δ ⊢ ∀[ Δ₁ ] Γ₁ ≤τ ∀[ Δ₂ ] Γ₂ → Δ₁ ≡ Δ₂
            help (∀-≤ Δ'⋆ Γ₁≤Γ₂) = refl
    Δ ⊢ ∀[ Δ₁ ] Γ₁ ≤τ? tuple τs₂ = no (λ ())
    Δ ⊢ tuple τs₁ ≤τ? α⁼ ι₂ = no (λ ())
    Δ ⊢ tuple τs₁ ≤τ? int = no (λ ())
    Δ ⊢ tuple τs₁ ≤τ? ns = no (λ ())
    Δ ⊢ tuple τs₁ ≤τ? ∀[ Δ₂ ] Γ₂ = no (λ ())
    Δ ⊢ tuple τs₁ ≤τ? tuple τs₂ with Δ ⊢ τs₁ ≤τs⁻? τs₂
    ... | yes τs₁≤τs₂ = yes (tuple-≤ τs₁≤τs₂)
    ... | no τs₁≰τs₂ = no (λ { (tuple-≤ τs₁≤τs₂) → τs₁≰τs₂ τs₁≤τs₂ })

    infix 3 _⊢_≤τ⁻?_
    _⊢_≤τ⁻?_ : ∀ Δ τ⁻₁ τ⁻₂ → Dec (Δ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂)
    Δ ⊢ τ₁ , φ₁ ≤τ⁻? τ₂ , φ₂ with τ₁ ≟ τ₂
    ... | no τ₁≢τ₂ = no (help τ₁≢τ₂)
      where help : ∀ {τ₁ τ₂} →
                     τ₁ ≢ τ₂ →
                     ¬ (Δ ⊢ τ₁ , φ₁ ≤τ⁻ τ₂ , φ₂)
            help τ₁≢τ₂ (τ⁻-≤ τ⋆ φ₁≤φ₂) = τ₁≢τ₂ refl
    Δ ⊢ τ  , φ₁ ≤τ⁻? .τ , φ₂
        | yes refl with Δ ⊢? τ Valid | φ₁ ≤φ? φ₂
    ... | yes τ⋆ | yes φ₁≤φ₂ = yes (τ⁻-≤ τ⋆ φ₁≤φ₂)
    ... | no ¬τ⋆ | _ = no (λ { (τ⁻-≤ τ⋆ φ₁≤φ₂) → ¬τ⋆ τ⋆})
    ... | _ | no φ₁≰φ₂ = no (λ { (τ⁻-≤ τ⋆ φ₁≤φ₂) → φ₁≰φ₂ φ₁≤φ₂})

    infix 3 _⊢_≤τs⁻?_
    _⊢_≤τs⁻?_ : ∀ Δ τs⁻₁ τs⁻₂ →
                    Dec (AllZip (λ τ⁻₁ τ⁻₂ → Δ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂) τs⁻₁ τs⁻₂)
    Δ ⊢ [] ≤τs⁻? [] = yes []
    Δ ⊢ [] ≤τs⁻? τ⁻₂ ∷ τs⁻₂ = no (λ ())
    Δ ⊢ τ₁⁻ ∷ τs⁻₁ ≤τs⁻? [] = no (λ ())
    Δ ⊢ τ⁻₁ ∷ τs⁻₁ ≤τs⁻? τ⁻₂ ∷ τs⁻₂
      with Δ ⊢ τ⁻₁ ≤τ⁻? τ⁻₂ | Δ ⊢ τs⁻₁ ≤τs⁻? τs⁻₂
    ... | yes τ⁻₁≤τ⁻₂ | yes τs⁻₁≤τs⁻₂ = yes (τ⁻₁≤τ⁻₂ ∷ τs⁻₁≤τs⁻₂)
    ... | no τ⁻₁≰τ⁻₂ | _ = no (λ { (τ⁻₁≤τ⁻₂ ∷ τs⁻₁≤τs⁻₂) → τ⁻₁≰τ⁻₂ τ⁻₁≤τ⁻₂ })
    ... | _ | no τs⁻₁≰τs⁻₂ =
      no (λ { (τ⁻₁≤τ⁻₂ ∷ τs⁻₁≤τs⁻₂) → τs⁻₁≰τs⁻₂ τs⁻₁≤τs⁻₂ })

    infix 3 _⊢_≤σ?_
    _⊢_≤σ?_ : ∀ Δ σ₁ σ₂ → Dec (Δ ⊢ σ₁ ≤σ σ₂)
    Δ ⊢ ρ⁼ ι₁ ≤σ? ρ⁼ ι₂ with ι₁ ≟ ι₂ | ↓-decᵥ Δ ι₁ ρ
    Δ ⊢ ρ⁼ ι ≤σ? ρ⁼ .ι | yes refl | yes l = yes (ρ⁼-≤ l)
    Δ ⊢ ρ⁼ ι  ≤σ? ρ⁼ .ι | yes refl | no ¬l =
      no (λ { (ρ⁼-≤ l) → ¬l l })
    Δ ⊢ ρ⁼ ι₁ ≤σ? ρ⁼ ι₂ | no ι₁≢ι₂ | _ = no (ι₁≢ι₂ ∘ help)
      where help : ∀ {Δ ι₁ ι₂} → Δ ⊢ ρ⁼ ι₁ ≤σ ρ⁼ ι₂ → ι₁ ≡ ι₂
            help (ρ⁼-≤ l) = refl
    Δ ⊢ ρ⁼ ι₁ ≤σ? [] = no (λ ())
    Δ ⊢ ρ⁼ ι₁ ≤σ? τ₂ ∷ σ₂ = no (λ ())
    Δ ⊢ [] ≤σ? ρ⁼ ι₂ = no (λ ())
    Δ ⊢ [] ≤σ? [] = yes []
    Δ ⊢ [] ≤σ? τ₂ ∷ σ₂ = no (λ ())
    Δ ⊢ τ₁ ∷ σ₁ ≤σ? ρ⁼ ι₂ = no (λ ())
    Δ ⊢ τ₁ ∷ σ₁ ≤σ? [] = no (λ ())
    Δ ⊢ τ₁ ∷ σ₁ ≤σ? τ₂ ∷ σ₂
      with Δ ⊢ τ₁ ≤τ? τ₂ | Δ ⊢ σ₁ ≤σ? σ₂
    ... | yes τ₁≤τ₂ | yes σ₁≤σ₂ = yes (τ₁≤τ₂ ∷ σ₁≤σ₂)
    ... | no τ₁≰τ₂ | _ = no (λ { (τ₁≤τ₂ ∷ σ₁≤σ₂) → τ₁≰τ₂ τ₁≤τ₂ })
    ... | _ | no σ₁≰σ₂ = no (λ { (τ₁≤τ₂ ∷ σ₁≤σ₂) → σ₁≰σ₂ σ₁≤σ₂ })

    infix 3 _⊢_≤Γ?_
    _⊢_≤Γ?_ : ∀ Δ Γ₁ Γ₂ → Dec (Δ ⊢ Γ₁ ≤Γ Γ₂)
    Δ ⊢ registerₐ sp₁ regs₁ ≤Γ? registerₐ sp₂ regs₂
      with Δ ⊢ sp₁ ≤σ? sp₂ | Δ ⊢ regs₁ ≤regs? regs₂
    ... | yes sp₁≤sp₂ | yes regs₁≤regs₂ = yes (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
    ... | no sp₁≰sp₂  | _ =
      no (λ { (Γ-≤ sp₁≤sp₂ regs₁≤regs₂) → sp₁≰sp₂ sp₁≤sp₂ })
    ... | _ | no regs₁≰regs₂ =
      no (λ { (Γ-≤ sp₁≤sp₂ regs₁≤regs₂) → regs₁≰regs₂ regs₁≤regs₂ })

    infix 3 _⊢_≤regs?_
    _⊢_≤regs?_ : ∀ Δ {m} (regs₁ regs₂ : Vec Type m) →
                   Dec (AllZipᵥ (λ τ₁ τ₂ → Δ ⊢ τ₁ ≤τ τ₂) regs₁ regs₂)
    Δ ⊢ [] ≤regs? [] = yes []
    Δ ⊢ τ₁ ∷ regs₁ ≤regs? τ₂ ∷ regs₂ with
      Δ ⊢ τ₁ ≤τ? τ₂ | Δ ⊢ regs₁ ≤regs? regs₂
    ... | yes τ₁≤τ₂ | yes regs₁≤regs₂ = yes (τ₁≤τ₂ ∷ regs₁≤regs₂)
    ... | no τ₁≰τ₂ | _ = no (λ { (τ₁≤τ₂ ∷ regs₁≤regs₂) → τ₁≰τ₂ τ₁≤τ₂ })
    ... | _ | no regs₁≰regs₂ =
      no (λ { (τ₁≤τ₂ ∷ regs₁≤regs₂) → regs₁≰regs₂ regs₁≤regs₂ })

  φ-refl : ∀ {φ} → φ ≤φ φ
  φ-refl {init} = φ-≤-init
  φ-refl {uninit} = φ-≤-uninit

  mutual
    τ-refl : ∀ {Δ τ} → Δ ⊢ τ Type → Δ ⊢ τ ≤τ τ
    τ-refl (valid-α⁼ l) = α⁼-≤ l
    τ-refl valid-int = int-≤
    τ-refl valid-ns = ns-≤
    τ-refl (valid-∀ Δ⋆ Γ⋆) = ∀-≤ Δ⋆ (Γ-refl Γ⋆)
    τ-refl (valid-tuple τs⋆) = tuple-≤ (τs⁻-refl τs⋆)

    τ⁻-refl : ∀ {Δ τ⁻} → Δ ⊢ τ⁻ InitType → Δ ⊢ τ⁻ ≤τ⁻ τ⁻
    τ⁻-refl (valid-τ⁻ τ⋆) = τ⁻-≤ τ⋆ φ-refl

    τs⁻-refl : ∀ {Δ τs} →
                 All (λ τ⁻ → Δ  ⊢ τ⁻ InitType) τs →
                 AllZip (λ τ⁻₁ τ⁻₂ → Δ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂) τs τs
    τs⁻-refl [] = []
    τs⁻-refl (τ⁻⋆ ∷ τs⁻⋆) = τ⁻-refl τ⁻⋆ ∷ τs⁻-refl τs⁻⋆

    σ-refl : ∀ {Δ σ} → Δ ⊢ σ StackType → Δ ⊢ σ ≤σ σ
    σ-refl (valid-ρ⁼ l) = ρ⁼-≤ l
    σ-refl valid-[] = []
    σ-refl (τ⋆ ∷ σ⋆) = τ-refl τ⋆ ∷ σ-refl σ⋆

    Γ-refl : ∀ {Δ Γ} → Δ ⊢ Γ RegisterAssignment → Δ ⊢ Γ ≤Γ Γ
    Γ-refl (valid-registerₐ sp⋆ regs⋆) =
      Γ-≤ (σ-refl sp⋆) (regs-refl regs⋆)

    regs-refl : ∀ {Δ m} {regs : Vec Type m} →
                  Allᵥ (λ τ → Δ ⊢ τ Type) regs →
                  AllZipᵥ (λ τ₁ τ₂ → Δ ⊢ τ₁ ≤τ τ₂) regs regs
    regs-refl [] = []
    regs-refl (τ⋆ ∷ regs⋆) = τ-refl τ⋆ ∷ regs-refl regs⋆

  φ-trans : ∀ {φ₁ φ₂ φ₃} → φ₁ ≤φ φ₂ → φ₂ ≤φ φ₃ → φ₁ ≤φ φ₃
  φ-trans φ-≤-init φ-≤-init = φ-≤-init
  φ-trans _ φ-≤-uninit = φ-≤-uninit

  mutual
    τ-trans : ∀ {Δ τ₁ τ₂ τ₃} → Δ ⊢ τ₁ ≤τ τ₂ → Δ ⊢ τ₂ ≤τ τ₃ → Δ ⊢ τ₁ ≤τ τ₃
    τ-trans (α⁼-≤ l) (α⁼-≤ l') = α⁼-≤ l
    τ-trans int-≤ int-≤ = int-≤
    τ-trans ns-≤ ns-≤ = ns-≤
    τ-trans (∀-≤ Δ'⋆ Γ₁₂≤) (∀-≤ _ Γ₂₃≤) = ∀-≤ Δ'⋆ (Γ-trans Γ₁₂≤ Γ₂₃≤)
    τ-trans (tuple-≤ τs₁₂≤) (tuple-≤ τs₂₃≤) = tuple-≤ (τs⁻-trans τs₁₂≤ τs₂₃≤)

    τ⁻-trans : ∀ {Δ τ⁻₁ τ⁻₂ τ⁻₃} → Δ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂ →
                                   Δ ⊢ τ⁻₂ ≤τ⁻ τ⁻₃ →
                                   Δ ⊢ τ⁻₁ ≤τ⁻ τ⁻₃
    τ⁻-trans (τ⁻-≤ τ⋆ φ₁≤φ₂) (τ⁻-≤ τ⋆' φ₂≤φ₃) = τ⁻-≤ τ⋆ (φ-trans φ₁≤φ₂ φ₂≤φ₃)

    τs⁻-trans :
      ∀ {Δ τs₁ τs₂ τs₃} →
        AllZip (λ τ⁻₁ τ⁻₂ → Δ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂) τs₁ τs₂ →
        AllZip (λ τ⁻₂ τ⁻₃ → Δ ⊢ τ⁻₂ ≤τ⁻ τ⁻₃) τs₂ τs₃ →
        AllZip (λ τ⁻₁ τ⁻₃ → Δ ⊢ τ⁻₁ ≤τ⁻ τ⁻₃) τs₁ τs₃
    τs⁻-trans [] [] = []
    τs⁻-trans (τ₁₂≤ ∷ τs₁₂≤) (τ₂₃≤ ∷ τs₂₃≤) =
      τ⁻-trans τ₁₂≤ τ₂₃≤ ∷ τs⁻-trans τs₁₂≤ τs₂₃≤

    σ-trans : ∀ {Δ σ₁ σ₂ σ₃} → Δ ⊢ σ₁ ≤σ σ₂ → Δ ⊢ σ₂ ≤σ σ₃ → Δ ⊢ σ₁ ≤σ σ₃
    σ-trans (ρ⁼-≤ l) (ρ⁼-≤ l') = ρ⁼-≤ l
    σ-trans [] [] = []
    σ-trans (τ₁≤τ₂ ∷ σ₁≤σ₂) (τ₂≤τ₃ ∷ σ₂≤σ₃) =
      τ-trans τ₁≤τ₂ τ₂≤τ₃ ∷ σ-trans σ₁≤σ₂ σ₂≤σ₃

    Γ-trans : ∀ {Δ Γ₁ Γ₂ Γ₃} → Δ ⊢ Γ₁ ≤Γ Γ₂ → Δ ⊢ Γ₂ ≤Γ Γ₃ → Δ ⊢ Γ₁ ≤Γ Γ₃
    Γ-trans (Γ-≤ sp₁₂≤ regs₁₂≤) (Γ-≤ sp₂₃≤ regs₂₃≤) =
      Γ-≤ (σ-trans sp₁₂≤ sp₂₃≤) (regs-trans regs₁₂≤ regs₂₃≤)

    regs-trans : ∀ {Δ m} {τs₁ τs₂ τs₃ : Vec Type m} →
                   AllZipᵥ (λ τ₁ τ₂ → Δ ⊢ τ₁ ≤τ τ₂) τs₁ τs₂ →
                   AllZipᵥ (λ τ₂ τ₃ → Δ ⊢ τ₂ ≤τ τ₃) τs₂ τs₃ →
                   AllZipᵥ (λ τ₁ τ₃ → Δ ⊢ τ₁ ≤τ τ₃) τs₁ τs₃
    regs-trans [] [] = []
    regs-trans (τ₁₂≤ ∷ τs₁₂≤) (τ₂₃≤ ∷ τs₂₃≤) =
      τ-trans τ₁₂≤ τ₂₃≤ ∷ regs-trans τs₁₂≤ τs₂₃≤

  mutual
    τ-valid : ∀ {Δ τ₁ τ₂} → Δ ⊢ τ₁ ≤τ τ₂ → Δ ⊢ τ₁ Type × Δ ⊢ τ₂ Type
    τ-valid (α⁼-≤ l) = valid-α⁼ l , valid-α⁼ l
    τ-valid int-≤ = valid-int , valid-int
    τ-valid ns-≤ = valid-ns , valid-ns
    τ-valid (∀-≤ Δ⋆ Γ≤) with Γ-valid Γ≤
    ... | Γ₁⋆ , Γ₂⋆ = valid-∀ Δ⋆ Γ₁⋆ , valid-∀ Δ⋆ Γ₂⋆
    τ-valid (tuple-≤ τs⋆) with τs⁻-valid τs⋆
    ... | τs₁⋆ , τs₂⋆ = (valid-tuple τs₁⋆) , valid-tuple τs₂⋆

    τ⁻-valid : ∀ {Δ τ⁻₁ τ⁻₂} → Δ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂ →
                               Δ ⊢ τ⁻₁ InitType × Δ ⊢ τ⁻₂ InitType
    τ⁻-valid (τ⁻-≤ τ⋆ φ₁≤φ₂) = valid-τ⁻ τ⋆ , valid-τ⁻ τ⋆

    τs⁻-valid :
      ∀ {Δ τs₁ τs₂} →
        AllZip (λ τ⁻₁ τ⁻₂ → Δ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂) τs₁ τs₂ →
        All (λ τ⁻ → Δ ⊢ τ⁻ InitType) τs₁ ×
        All (λ τ⁻ → Δ ⊢ τ⁻ InitType) τs₂
    τs⁻-valid [] = [] , []
    τs⁻-valid (τ⁻≤ ∷ τs⁻≤)
      with τ⁻-valid τ⁻≤ | τs⁻-valid τs⁻≤
    ...   | τ⁻₁⋆ , τ⁻₂⋆ | τs₁⋆ , τs₂⋆ = τ⁻₁⋆ ∷ τs₁⋆ , τ⁻₂⋆ ∷ τs₂⋆

    σ-valid : ∀ {Δ σ₁ σ₂} → Δ ⊢ σ₁ ≤σ σ₂ →
                            Δ ⊢ σ₁ StackType ×
                            Δ ⊢ σ₂ StackType
    σ-valid (ρ⁼-≤ l) = valid-ρ⁼ l , valid-ρ⁼ l
    σ-valid [] = valid-[] , valid-[]
    σ-valid (τ₁≤τ₂ ∷ σ₁≤σ₂) = Σ-zip _∷_ _∷_ (τ-valid τ₁≤τ₂) (σ-valid σ₁≤σ₂)

    Γ-valid : ∀ {Δ Γ₁ Γ₂} → Δ ⊢ Γ₁ ≤Γ Γ₂ →
                            Δ ⊢ Γ₁ RegisterAssignment ×
                            Δ ⊢ Γ₂ RegisterAssignment
    Γ-valid  (Γ-≤ sp≤ regs≤) with σ-valid sp≤ | regs-valid regs≤
    ... | sp₁⋆ , sp₂⋆ | regs₁⋆ , regs₂⋆ =
      valid-registerₐ sp₁⋆ regs₁⋆ , valid-registerₐ sp₂⋆ regs₂⋆

    regs-valid :
      ∀ {Δ m} {τs₁ τs₂ : Vec Type m} →
        AllZipᵥ (λ τ₁ τ₂ → Δ ⊢ τ₁ ≤τ τ₂) τs₁ τs₂ →
        Allᵥ (λ τ → Δ ⊢ τ Type) τs₁ ×
        Allᵥ (λ τ → Δ ⊢ τ Type) τs₂
    regs-valid [] = [] , []
    regs-valid (τ≤ ∷ τs≤)
      with τ-valid τ≤ | regs-valid τs≤
    ...   | τ₁⋆ , τ₂⋆ | τs₁⋆ , τs₂⋆ = τ₁⋆ ∷ τs₁⋆ , τ₂⋆ ∷ τs₂⋆

  mutual
    τ-weaken : ∀ {Δ Δ' τ₁ τ₂} →
                 Δ ⊢ τ₁ ≤τ τ₂ →
                 Δ ++ Δ' ⊢ τ₁ ≤τ τ₂
    τ-weaken {Δ' = Δ'} (α⁼-≤ l) = α⁼-≤ (↓-add-right Δ' l)
    τ-weaken int-≤ = int-≤
    τ-weaken ns-≤ = ns-≤
    τ-weaken {Δ} {Δ'} (∀-≤ {Δ' = Δᵢ} Δᵢ⋆ Γ₁≤Γ₂) with Γ-weaken {Δ' = Δ'} Γ₁≤Γ₂
    ... | Γ₁≤Γ₂' rewrite List-++-assoc Δᵢ Δ Δ' = ∀-≤ (valid-++ Δᵢ⋆) Γ₁≤Γ₂'
    τ-weaken (tuple-≤ τs⁻) = tuple-≤ (τs⁻-weaken τs⁻)

    τ⁻-weaken : ∀ {Δ Δ' τ⁻₁ τ⁻₂} →
                  Δ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂ →
                  Δ ++ Δ' ⊢ τ⁻₁ ≤τ⁻ τ⁻₂
    τ⁻-weaken (τ⁻-≤ τ⋆ φ₁≤φ₂) = τ⁻-≤ (valid-++ τ⋆) φ₁≤φ₂

    τs⁻-weaken : ∀ {Δ Δ' τs⁻₁ τs⁻₂} →
                   AllZip (λ τ⁻₁ τ⁻₂ → Δ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂) τs⁻₁ τs⁻₂ →
                   AllZip (λ τ⁻₁ τ⁻₂ → Δ ++ Δ' ⊢ τ⁻₁ ≤τ⁻ τ⁻₂) τs⁻₁ τs⁻₂
    τs⁻-weaken [] = []
    τs⁻-weaken (τ⁻₁≤τ⁻₂ ∷ τs⁻₁≤τs⁻₂) =
      τ⁻-weaken τ⁻₁≤τ⁻₂ ∷ τs⁻-weaken τs⁻₁≤τs⁻₂

    σ-weaken : ∀ {Δ Δ' σ₁ σ₂} →
                 Δ ⊢ σ₁ ≤σ σ₂ →
                 Δ ++ Δ' ⊢ σ₁ ≤σ σ₂
    σ-weaken {Δ' = Δ'} (ρ⁼-≤ l) = ρ⁼-≤ (↓-add-right Δ' l)
    σ-weaken [] = []
    σ-weaken (τ₁≤τ₂ ∷ σ₁≤σ₂) = τ-weaken τ₁≤τ₂ ∷ σ-weaken σ₁≤σ₂

    Γ-weaken : ∀ {Δ Δ' Γ₁ Γ₂} →
                 Δ ⊢ Γ₁ ≤Γ Γ₂ →
                 Δ ++ Δ' ⊢ Γ₁ ≤Γ Γ₂
    Γ-weaken (Γ-≤ sp₁≤sp₂ regs₁≤regs₂) =
      Γ-≤ (σ-weaken sp₁≤sp₂) (regs-weaken regs₁≤regs₂)

    regs-weaken : ∀ {Δ Δ' m} {τs₁ τs₂ : Vec Type m} →
                   AllZipᵥ (λ τ₁ τ₂ → Δ ⊢ τ₁ ≤τ τ₂) τs₁ τs₂ →
                   AllZipᵥ (λ τ₁ τ₂ → Δ ++ Δ' ⊢ τ₁ ≤τ τ₂) τs₁ τs₂
    regs-weaken [] = []
    regs-weaken (τ₁≤τ₂ ∷ τs₁≤τs₂) = τ-weaken τ₁≤τ₂ ∷ regs-weaken τs₁≤τs₂

  mutual
    τ-change₁ : ∀ {Δ₁ Δ₂ τ₁ τ₂} →
                  Δ₁ ⊢ τ₁ ≤τ τ₂ →
                  Δ₂ ⊢ τ₁ Valid →
                  Δ₂ ⊢ τ₁ ≤τ τ₂
    τ-change₁ (α⁼-≤ l) (valid-α⁼ l') = α⁼-≤ l'
    τ-change₁ int-≤ valid-int = int-≤
    τ-change₁ ns-≤ valid-ns = ns-≤
    τ-change₁ (∀-≤ Δ⋆ Γ₁≤Γ₂) (valid-∀ Δ⋆' Γ₁⋆) = ∀-≤ Δ⋆' (Γ-change₁ Γ₁≤Γ₂ Γ₁⋆)
    τ-change₁ (tuple-≤ τs⁻₁≤τs⁻₂) (valid-tuple τs⁻₁⋆) =
      tuple-≤ (τs⁻-change₁ τs⁻₁≤τs⁻₂ τs⁻₁⋆)

    τ⁻-change₁ : ∀ {Δ₁ Δ₂ τ⁻₁ τ⁻₂} →
                   Δ₁ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂ →
                   Δ₂ ⊢ τ⁻₁ Valid →
                   Δ₂ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂
    τ⁻-change₁ (τ⁻-≤ τ⋆ φ₁≤φ₂) (valid-τ⁻ τ⋆') = τ⁻-≤ τ⋆' φ₁≤φ₂

    τs⁻-change₁ : ∀ {Δ₁ Δ₂ τs⁻₁ τs⁻₂} →
                    AllZip (λ τ⁻₁ τ⁻₂ → Δ₁ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂) τs⁻₁ τs⁻₂ →
                    Δ₂ ⊢ τs⁻₁ Valid →
                    AllZip (λ τ⁻₁ τ⁻₂ → Δ₂ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂) τs⁻₁ τs⁻₂
    τs⁻-change₁ [] [] = []
    τs⁻-change₁ (τ⁻₁≤τ⁻₂ ∷ τs⁻₁≤τs⁻₂) (τ⁻₁⋆ ∷ τs⁻₁⋆) =
      τ⁻-change₁ τ⁻₁≤τ⁻₂ τ⁻₁⋆ ∷ τs⁻-change₁ τs⁻₁≤τs⁻₂ τs⁻₁⋆

    σ-change₁ : ∀ {Δ₁ Δ₂ σ₁ σ₂} →
                  Δ₁ ⊢ σ₁ ≤σ σ₂ →
                  Δ₂ ⊢ σ₁ Valid →
                  Δ₂ ⊢ σ₁ ≤σ σ₂
    σ-change₁ (ρ⁼-≤ l) (valid-ρ⁼ l') = ρ⁼-≤ l'
    σ-change₁ [] valid-[] = []
    σ-change₁ (τ₁≤τ₂ ∷ σ₁≤σ₂) (τ₁⋆ ∷ σ₁⋆) =
      τ-change₁ τ₁≤τ₂ τ₁⋆ ∷ σ-change₁ σ₁≤σ₂ σ₁⋆

    Γ-change₁ : ∀ {Δ₁ Δ₂ Γ₁ Γ₂} →
                  Δ₁ ⊢ Γ₁ ≤Γ Γ₂ →
                  Δ₂ ⊢ Γ₁ Valid →
                  Δ₂ ⊢ Γ₁ ≤Γ Γ₂
    Γ-change₁ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂) (valid-registerₐ sp₁⋆ regs₁⋆) =
      Γ-≤ (σ-change₁ sp₁≤sp₂ sp₁⋆) (regs-change₁ regs₁≤regs₂ regs₁⋆)

    regs-change₁ : ∀ {Δ₁ Δ₂ m} {τs₁ τs₂ : Vec Type m} →
                     AllZipᵥ (λ τ₁ τ₂ → Δ₁ ⊢ τ₁ ≤τ τ₂) τs₁ τs₂ →
                     Δ₂ ⊢ τs₁ Valid →
                     AllZipᵥ (λ τ₁ τ₂ → Δ₂ ⊢ τ₁ ≤τ τ₂) τs₁ τs₂
    regs-change₁ [] [] = []
    regs-change₁ (τ₁≤τ₂ ∷ τs₁≤τs₂) (τ₁⋆ ∷ τs₁⋆) =
      τ-change₁ τ₁≤τ₂ τ₁⋆ ∷ regs-change₁ τs₁≤τs₂ τs₁⋆

  mutual
    τ-change₂ : ∀ {Δ₁ Δ₂ τ₁ τ₂} →
                  Δ₁ ⊢ τ₁ ≤τ τ₂ →
                  Δ₂ ⊢ τ₂ Valid →
                  Δ₂ ⊢ τ₁ ≤τ τ₂
    τ-change₂ (α⁼-≤ l) (valid-α⁼ l') = α⁼-≤ l'
    τ-change₂ int-≤ valid-int = int-≤
    τ-change₂ ns-≤ valid-ns = ns-≤
    τ-change₂ (∀-≤ Δ⋆ Γ₁≤Γ₂) (valid-∀ Δ⋆' Γ₂⋆) = ∀-≤ Δ⋆' (Γ-change₂ Γ₁≤Γ₂ Γ₂⋆)
    τ-change₂ (tuple-≤ τs⁻₁≤τs⁻₂) (valid-tuple τs⁻₂⋆) =
      tuple-≤ (τs⁻-change₂ τs⁻₁≤τs⁻₂ τs⁻₂⋆)

    τ⁻-change₂ : ∀ {Δ₁ Δ₂ τ⁻₁ τ⁻₂} →
                   Δ₁ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂ →
                   Δ₂ ⊢ τ⁻₂ Valid →
                   Δ₂ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂
    τ⁻-change₂ (τ⁻-≤ τ⋆ φ₁≤φ₂) (valid-τ⁻ τ⋆') = τ⁻-≤ τ⋆' φ₁≤φ₂

    τs⁻-change₂ : ∀ {Δ₁ Δ₂ τs⁻₁ τs⁻₂} →
                    AllZip (λ τ⁻₁ τ⁻₂ → Δ₁ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂) τs⁻₁ τs⁻₂ →
                    Δ₂ ⊢ τs⁻₂ Valid →
                    AllZip (λ τ⁻₁ τ⁻₂ → Δ₂ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂) τs⁻₁ τs⁻₂
    τs⁻-change₂ [] [] = []
    τs⁻-change₂ (τ⁻₁≤τ⁻₂ ∷ τs⁻₁≤τs⁻₂) (τ⁻₂⋆ ∷ τs⁻₂⋆) =
      τ⁻-change₂ τ⁻₁≤τ⁻₂ τ⁻₂⋆ ∷ τs⁻-change₂ τs⁻₁≤τs⁻₂ τs⁻₂⋆

    σ-change₂ : ∀ {Δ₁ Δ₂ σ₁ σ₂} →
                  Δ₁ ⊢ σ₁ ≤σ σ₂ →
                  Δ₂ ⊢ σ₂ Valid →
                  Δ₂ ⊢ σ₁ ≤σ σ₂
    σ-change₂ (ρ⁼-≤ l) (valid-ρ⁼ l') = ρ⁼-≤ l'
    σ-change₂ [] valid-[] = []
    σ-change₂ (τ₁≤τ₂ ∷ σ₁≤σ₂) (τ₂⋆ ∷ σ₂⋆) =
      τ-change₂ τ₁≤τ₂ τ₂⋆ ∷ σ-change₂ σ₁≤σ₂ σ₂⋆

    Γ-change₂ : ∀ {Δ₁ Δ₂ Γ₁ Γ₂} →
                  Δ₁ ⊢ Γ₁ ≤Γ Γ₂ →
                  Δ₂ ⊢ Γ₂ Valid →
                  Δ₂ ⊢ Γ₁ ≤Γ Γ₂
    Γ-change₂ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂) (valid-registerₐ sp₂⋆ regs₂⋆) =
      Γ-≤ (σ-change₂ sp₁≤sp₂ sp₂⋆) (regs-change₂ regs₁≤regs₂ regs₂⋆)

    regs-change₂ : ∀ {Δ₁ Δ₂ m} {τs₁ τs₂ : Vec Type m} →
                     AllZipᵥ (λ τ₁ τ₂ → Δ₁ ⊢ τ₁ ≤τ τ₂) τs₁ τs₂ →
                     Δ₂ ⊢ τs₂ Valid →
                     AllZipᵥ (λ τ₁ τ₂ → Δ₂ ⊢ τ₁ ≤τ τ₂) τs₁ τs₂
    regs-change₂ [] [] = []
    regs-change₂ (τ₁≤τ₂ ∷ τs₁≤τs₂) (τ₂⋆ ∷ τs₂⋆) =
      τ-change₂ τ₁≤τ₂ τ₂⋆ ∷ regs-change₂ τs₁≤τs₂ τs₂⋆

Vec-Subtype⁺ : ∀ A {T S} {{S⁺ : Subtype⁺ A {{T}} {{S}}}} m →
                 Subtype⁺ (Vec A m) {{Vec-TypeLike A m}} {{Vec-Subtype A m}}
Vec-Subtype⁺ A {T} {S} m = subtype⁺
    dec'
    refl'
    trans'
    valid
    xs-weaken
    xs-change₁
    xs-change₂
  where _⊢_≤xs_ : ∀ {m} → TypeAssignment → Vec A m → Vec A m → Set
        Δ ⊢ xs₁ ≤xs xs₂ = AllZipᵥ (λ x₁ x₂ → Δ ⊢ x₁ ≤ x₂) xs₁ xs₂

        dec' : ∀ {m} Δ (xs₁ xs₂ : Vec A m) →
                 Dec (Δ ⊢ xs₁ ≤xs xs₂)
        dec' Δ [] [] = yes []
        dec' Δ (x₁ ∷ xs₁) (x₂ ∷ xs₂)
          with Δ ⊢ x₁ ≤? x₂ | dec' Δ xs₁ xs₂
        ... | yes x₁≤x₂ | yes xs₁≤xs₂ = yes (x₁≤x₂ ∷ xs₁≤xs₂)
        ... | no x₁≰x₂ | _ = no (λ { (x₁≤x₂ ∷ xs₁≤xs₂) → x₁≰x₂ x₁≤x₂ })
        ... | _ | no xs₁≰xs₂ = no (λ { (x₁≤x₂ ∷ xs₁≤xs₂) → xs₁≰xs₂ xs₁≤xs₂ })

        refl' : ∀ {Δ m} {xs : Vec A m} →
                  _⊢_Valid {{Vec-TypeLike A m}} Δ xs →
                  Δ ⊢ xs ≤xs xs
        refl' [] = []
        refl' (x⋆ ∷ xs⋆) = ≤-refl x⋆ ∷ refl' xs⋆

        trans' : ∀ {Δ m} {xs₁ xs₂ xs₃ : Vec A m} →
                   Δ ⊢ xs₁ ≤xs xs₂ →
                   Δ ⊢ xs₂ ≤xs xs₃ →
                   Δ ⊢ xs₁ ≤xs xs₃
        trans' [] [] = []
        trans' (x₁₂≤ ∷ xs₁₂≤) (x₂₃≤ ∷ xs₂₃≤) =
          (≤-trans x₁₂≤ x₂₃≤) ∷ trans' xs₁₂≤ xs₂₃≤

        valid : ∀ {Δ m} {xs₁ xs₂ : Vec A m} →
                  Δ ⊢ xs₁ ≤xs xs₂ →
                  _⊢_Valid {{Vec-TypeLike A m}} Δ xs₁ ×
                  _⊢_Valid {{Vec-TypeLike A m}} Δ xs₂
        valid [] = [] , []
        valid (x≤ ∷ xs≤)
          with ≤-valid x≤ | valid xs≤
        ... | x₁⋆ , x₂⋆ | xs₁⋆ , xs₂⋆ = x₁⋆ ∷ xs₁⋆ , x₂⋆ ∷ xs₂⋆

        xs-weaken : ∀ {m Δ Δ'} {xs₁ xs₂ : Vec A m} →
                      Δ ⊢ xs₁ ≤xs xs₂ →
                      (Δ ++ Δ') ⊢ xs₁ ≤xs xs₂
        xs-weaken [] = []
        xs-weaken (x₁≤x₂ ∷ xs₁≤xs₂) = ≤-++ x₁≤x₂ ∷ xs-weaken xs₁≤xs₂

        xs-change₁ : ∀ {Δ₁ Δ₂ m} {xs₁ xs₂ : Vec A m} →
                       Δ₁ ⊢ xs₁ ≤xs xs₂ →
                       _⊢_Valid {{Vec-TypeLike A m}} Δ₂ xs₁ →
                       Δ₂ ⊢ xs₁ ≤xs xs₂
        xs-change₁ [] [] = []
        xs-change₁ (x₁≤x₂ ∷ xs₁≤xs₂) (x₁⋆ ∷ xs₁⋆) =
          ≤-change₁ x₁≤x₂ x₁⋆ ∷ xs-change₁ xs₁≤xs₂ xs₁⋆

        xs-change₂ : ∀ {Δ₁ Δ₂ m} {xs₁ xs₂ : Vec A m} →
                       Δ₁ ⊢ xs₁ ≤xs xs₂ →
                       _⊢_Valid {{Vec-TypeLike A m}} Δ₂ xs₂ →
                       Δ₂ ⊢ xs₁ ≤xs xs₂
        xs-change₂ [] [] = []
        xs-change₂ (x₁≤x₂ ∷ xs₁≤xs₂) (x₂⋆ ∷ xs₂⋆) =
          ≤-change₂ x₁≤x₂ x₂⋆ ∷ xs-change₂ xs₁≤xs₂ xs₂⋆

List-Subtype⁺ : ∀ A {T S} {{S⁺ : Subtype⁺ A {{T}} {{S}}}} →
                  Subtype⁺ (List A) {{List-TypeLike A}} {{List-Subtype A}}
List-Subtype⁺ A {T} {S} = subtype⁺
    dec'
    refl'
    trans'
    valid
    xs-weaken
    xs-change₁
    xs-change₂
  where _⊢_≤xs_ : TypeAssignment → List A → List A → Set
        Δ ⊢ xs₁ ≤xs xs₂ = AllZip (λ x₁ x₂ → Δ ⊢ x₁ ≤ x₂) xs₁ xs₂

        dec' : ∀ Δ xs₁ xs₂ →
                 Dec (Δ ⊢ xs₁ ≤xs xs₂)
        dec' Δ [] [] = yes []
        dec' Δ (x₁ ∷ xs₁) [] = no (λ ())
        dec' Δ [] (x₂ ∷ xs₂) = no (λ ())
        dec' Δ (x₁ ∷ xs₁) (x₂ ∷ xs₂)
          with Δ ⊢ x₁ ≤? x₂ | dec' Δ xs₁ xs₂
        ... | yes x₁≤x₂ | yes xs₁≤xs₂ = yes (x₁≤x₂ ∷ xs₁≤xs₂)
        ... | no x₁≰x₂ | _ = no (λ { (x₁≤x₂ ∷ xs₁≤xs₂) → x₁≰x₂ x₁≤x₂ })
        ... | _ | no xs₁≰xs₂ = no (λ { (x₁≤x₂ ∷ xs₁≤xs₂) → xs₁≰xs₂ xs₁≤xs₂ })

        refl' : ∀ {Δ xs} →
                  _⊢_Valid {{List-TypeLike A}} Δ xs →
                  Δ ⊢ xs ≤xs xs
        refl' [] = []
        refl' (x⋆ ∷ xs⋆) = ≤-refl x⋆ ∷ refl' xs⋆

        trans' : ∀ {Δ xs₁ xs₂ xs₃} →
                   Δ ⊢ xs₁ ≤xs xs₂ →
                   Δ ⊢ xs₂ ≤xs xs₃ →
                   Δ ⊢ xs₁ ≤xs xs₃
        trans' [] [] = []
        trans' (x₁₂≤ ∷ xs₁₂≤) (x₂₃≤ ∷ xs₂₃≤) =
          (≤-trans x₁₂≤ x₂₃≤) ∷ trans' xs₁₂≤ xs₂₃≤

        valid : ∀ {Δ xs₁ xs₂} →
                  Δ ⊢ xs₁ ≤xs xs₂ →
                  _⊢_Valid {{List-TypeLike A}} Δ xs₁ ×
                  _⊢_Valid {{List-TypeLike A}} Δ xs₂
        valid [] = [] , []
        valid (x≤ ∷ xs≤)
          with ≤-valid x≤ | valid xs≤
        ... | x₁⋆ , x₂⋆ | xs₁⋆ , xs₂⋆ = x₁⋆ ∷ xs₁⋆ , x₂⋆ ∷ xs₂⋆

        xs-weaken : ∀ {Δ Δ' xs₁ xs₂} →
                      Δ ⊢ xs₁ ≤xs xs₂ →
                      (Δ ++ Δ') ⊢ xs₁ ≤xs xs₂
        xs-weaken [] = []
        xs-weaken (x₁≤x₂ ∷ xs₁≤xs₂) = ≤-++ x₁≤x₂ ∷ xs-weaken xs₁≤xs₂

        xs-change₁ : ∀ {Δ₁ Δ₂ xs₁ xs₂} →
                       Δ₁ ⊢ xs₁ ≤xs xs₂ →
                       _⊢_Valid {{List-TypeLike A}} Δ₂ xs₁ →
                       Δ₂ ⊢ xs₁ ≤xs xs₂
        xs-change₁ [] [] = []
        xs-change₁ (x₁≤x₂ ∷ xs₁≤xs₂) (x₁⋆ ∷ xs₁⋆) =
          ≤-change₁ x₁≤x₂ x₁⋆ ∷ xs-change₁ xs₁≤xs₂ xs₁⋆

        xs-change₂ : ∀ {Δ₁ Δ₂ xs₁ xs₂} →
                       Δ₁ ⊢ xs₁ ≤xs xs₂ →
                       _⊢_Valid {{List-TypeLike A}} Δ₂ xs₂ →
                       Δ₂ ⊢ xs₁ ≤xs xs₂
        xs-change₂ [] [] = []
        xs-change₂ (x₁≤x₂ ∷ xs₁≤xs₂) (x₂⋆ ∷ xs₂⋆) =
          ≤-change₂ x₁≤x₂ x₂⋆ ∷ xs-change₂ xs₁≤xs₂ xs₂⋆

instance
  InitializationFlag-Subtype⁺ : Subtype⁺ InitializationFlag
  InitializationFlag-Subtype⁺ = subtype⁺
    (const _≤φ?_)
    (const φ-refl)
    φ-trans
    (const (tt , tt))
    id
    (λ φ₁≤φ₂ _ → φ₁≤φ₂)
    (λ φ₁≤φ₂ _ → φ₁≤φ₂)

  Type-Subtype⁺ : Subtype⁺ Type
  Type-Subtype⁺ =
    subtype⁺ _⊢_≤τ?_ τ-refl τ-trans τ-valid τ-weaken τ-change₁ τ-change₂

  TypeVec-Subtype⁺ : ∀ {m} → Subtype⁺ (Vec Type m)
  TypeVec-Subtype⁺ = Vec-Subtype⁺ Type _

  TypeList-Subtype⁺ : Subtype⁺ (List Type)
  TypeList-Subtype⁺ = List-Subtype⁺ Type

  InitType-Subtype⁺ : Subtype⁺ InitType
  InitType-Subtype⁺ =
    subtype⁺ _⊢_≤τ⁻?_ τ⁻-refl τ⁻-trans τ⁻-valid
             τ⁻-weaken τ⁻-change₁ τ⁻-change₂

  InitTypeVec-Subtype⁺ : ∀ {m} → Subtype⁺ (Vec InitType m)
  InitTypeVec-Subtype⁺ = Vec-Subtype⁺ InitType _

  InitTypeList-Subtype⁺ : Subtype⁺ (List InitType)
  InitTypeList-Subtype⁺ = List-Subtype⁺ InitType

  StackType-Subtype⁺ : Subtype⁺ StackType
  StackType-Subtype⁺ =
    subtype⁺ _⊢_≤σ?_ σ-refl σ-trans σ-valid σ-weaken σ-change₁ σ-change₂

  RegisterAssignment-Subtype⁺ : Subtype⁺ RegisterAssignment
  RegisterAssignment-Subtype⁺ =
    subtype⁺ _⊢_≤Γ?_ Γ-refl Γ-trans Γ-valid Γ-weaken Γ-change₁ Γ-change₂
