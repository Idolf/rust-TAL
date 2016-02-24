module Lemmas.Types where

open import Util
open import Judgments
open import Lemmas.Equality using () -- only instances

-- The purpose of this file is to include proofs that:
-- * Subtyping is a preorder when restricted to valid terms.
-- * "Δ ⊢ x Valid" is equivalent to "Δ ⊢ x ≤ x".
-- * "Δ ⊢ x ≤ y" implies both that both "x" and "y" are valid.
-- * Subtyping and validity are both decidible.

record TypeLike⁺ (A : Set) {{_ : TypeLike A}} : Set1 where
  constructor typeLike⁺
  infix 3 _⊢?_Valid
  field
    ≤-refl : ∀ {Δ} {x : A} → Δ ⊢ x Valid → Δ ⊢ x ≤ x
    ≤-trans : ∀ {Δ} {x₁ x₂ x₃ : A} → Δ ⊢ x₁ ≤ x₂ → Δ ⊢ x₂ ≤ x₃ → Δ ⊢ x₁ ≤ x₃
    ≤-valid : ∀ {Δ} {x₁ x₂ : A} → Δ ⊢ x₁ ≤ x₂ → Δ ⊢ x₁ Valid × Δ ⊢ x₂ Valid
    _⊢_≤?_ : ∀ Δ (x₁ x₂ : A) → Dec (Δ ⊢ x₁ ≤ x₂)

  ≤-valid₁ : ∀ {Δ} {x₁ x₂ : A} → Δ ⊢ x₁ ≤ x₂ → Δ ⊢ x₁ Valid
  ≤-valid₁ = proj₁ ∘ ≤-valid

  ≤-valid₂ : ∀ {Δ} {x₁ x₂ : A} → Δ ⊢ x₁ ≤ x₂ → Δ ⊢ x₂ Valid
  ≤-valid₂ = proj₂ ∘ ≤-valid

  _⊢?_Valid : ∀ Δ (x : A) → Dec (Δ ⊢ x Valid)
  Δ ⊢? x Valid = dec-inj ≤-valid₁ ≤-refl (Δ ⊢ x ≤? x)
open TypeLike⁺ {{...}} public

private
  φ-refl : ∀ {φ} → φ ≤φ φ
  φ-refl {init} = φ-≤-init
  φ-refl {uninit} = φ-≤-uninit

  mutual
    reflᵗ : ∀ A {{_ : TypeLike A}} → Set
    reflᵗ A = ∀ {Δ} {x : A} → Δ ⊢ x Valid → Δ ⊢ x ≤ x

    τ-refl : reflᵗ Type
    τ-refl (valid-α⁼ l) = α⁼-≤ l
    τ-refl valid-int = int-≤
    τ-refl valid-uninit = uninit-≤
    τ-refl (valid-∀ Γ⋆) = ∀-≤ (Γ-refl Γ⋆)
    τ-refl (valid-tuple τs⋆) = tuple-≤ (τs⁻-refl τs⋆)

    τ⁻-refl : reflᵗ InitType
    τ⁻-refl (valid-τ⁻ τ⋆) = τ⁻-≤ τ⋆ φ-refl

    τs⁻-refl : reflᵗ (List InitType)
    τs⁻-refl [] = []
    τs⁻-refl (τ⁻⋆ ∷ τs⁻⋆) = τ⁻-refl τ⁻⋆ ∷ τs⁻-refl τs⁻⋆

    σ-refl : reflᵗ StackType
    σ-refl (valid-ρ⁼ l) = ρ⁼-≤ l
    σ-refl [] = []
    σ-refl (τ⋆ ∷ σ⋆) = τ-refl τ⋆ ∷ σ-refl σ⋆

    Γ-refl : reflᵗ RegisterAssignment
    Γ-refl (valid-registerₐ sp⋆ regs⋆) =
      Γ-≤ (σ-refl sp⋆) (regs-refl regs⋆)

    regs-refl : ∀ {n} → reflᵗ (Vec Type n)
    regs-refl [] = []
    regs-refl (τ⋆ ∷ regs⋆) = τ-refl τ⋆ ∷ regs-refl regs⋆

  φ-trans : ∀ {φ₁ φ₂ φ₃} → φ₁ ≤φ φ₂ → φ₂ ≤φ φ₃ → φ₁ ≤φ φ₃
  φ-trans φ-≤-init φ-≤-init = φ-≤-init
  φ-trans _ φ-≤-uninit = φ-≤-uninit

  mutual
    transᵗ : ∀ A {{_ : TypeLike A}} → Set
    transᵗ A = ∀ {Δ} {x₁ x₂ x₃ : A} → Δ ⊢ x₁ ≤ x₂ → Δ ⊢ x₂ ≤ x₃ → Δ ⊢ x₁ ≤ x₃

    τ-trans : transᵗ Type
    τ-trans (α⁼-≤ l) (α⁼-≤ l') = α⁼-≤ l
    τ-trans int-≤ int-≤ = int-≤
    τ-trans uninit-≤ uninit-≤ = uninit-≤
    τ-trans (∀-≤ Γ₂₁≤) (∀-≤ Γ₃₂≤) = ∀-≤ (Γ-trans Γ₃₂≤ Γ₂₁≤)
    τ-trans (tuple-≤ τs₁₂≤) (tuple-≤ τs₂₃≤) = tuple-≤ (τs⁻-trans τs₁₂≤ τs₂₃≤)

    τ⁻-trans : transᵗ InitType
    τ⁻-trans (τ⁻-≤ τ⋆ φ₁≤φ₂) (τ⁻-≤ τ⋆' φ₂≤φ₃) = τ⁻-≤ τ⋆ (φ-trans φ₁≤φ₂ φ₂≤φ₃)

    τs⁻-trans : transᵗ (List InitType)
    τs⁻-trans [] [] = []
    τs⁻-trans (τ₁₂≤ ∷ τs₁₂≤) (τ₂₃≤ ∷ τs₂₃≤) =
      τ⁻-trans τ₁₂≤ τ₂₃≤ ∷ τs⁻-trans τs₁₂≤ τs₂₃≤

    σ-trans : transᵗ StackType
    σ-trans (ρ⁼-≤ l) (ρ⁼-≤ l') = ρ⁼-≤ l
    σ-trans [] [] = []
    σ-trans (τ₁≤τ₂ ∷ σ₁≤σ₂) (τ₂≤τ₃ ∷ σ₂≤σ₃) =
      τ-trans τ₁≤τ₂ τ₂≤τ₃ ∷ σ-trans σ₁≤σ₂ σ₂≤σ₃

    Γ-trans : transᵗ RegisterAssignment
    Γ-trans (Γ-≤ sp₁≤sp₂ regs₁≤regs₂) (Γ-≤ sp₂≤sp₃ regs₂≤regs₃) =
      Γ-≤ (σ-trans sp₁≤sp₂ sp₂≤sp₃) (regs-trans regs₁≤regs₂ regs₂≤regs₃)

    regs-trans : ∀ {n} → transᵗ (Vec Type n)
    regs-trans [] [] = []
    regs-trans (τ₁₂≤ ∷ τs₁₂≤) (τ₂₃≤ ∷ τs₂₃≤) =
      τ-trans τ₁₂≤ τ₂₃≤ ∷ regs-trans τs₁₂≤ τs₂₃≤

  mutual
    validᵗ : ∀ A {{_ : TypeLike A}} → Set
    validᵗ A = ∀ {Δ} {x₁ x₂ : A} → Δ ⊢ x₁ ≤ x₂ → Δ ⊢ x₁ Valid × Δ ⊢ x₂ Valid

    τ-valid : validᵗ Type
    τ-valid (α⁼-≤ l) = valid-α⁼ l , valid-α⁼ l
    τ-valid int-≤ = valid-int , valid-int
    τ-valid uninit-≤ = valid-uninit , valid-uninit
    τ-valid (∀-≤ Γ₂≤Γ₁) with Γ-valid Γ₂≤Γ₁
    ... | Γ₂⋆ , Γ₁⋆ = valid-∀ Γ₁⋆ , valid-∀ Γ₂⋆
    τ-valid (tuple-≤ τs⋆) with τs⁻-valid τs⋆
    ... | τs₁⋆ , τs₂⋆ = (valid-tuple τs₁⋆) , valid-tuple τs₂⋆

    τ⁻-valid : validᵗ InitType
    τ⁻-valid (τ⁻-≤ τ⋆ φ₁≤φ₂) = valid-τ⁻ τ⋆ , valid-τ⁻ τ⋆

    τs⁻-valid : validᵗ (List InitType)
    τs⁻-valid [] = [] , []
    τs⁻-valid (τ⁻≤ ∷ τs⁻≤)
      with τ⁻-valid τ⁻≤ | τs⁻-valid τs⁻≤
    ... | τ⁻₁⋆ , τ⁻₂⋆ | τs₁⋆ , τs₂⋆ = τ⁻₁⋆ ∷ τs₁⋆ , τ⁻₂⋆ ∷ τs₂⋆

    σ-valid : validᵗ StackType
    σ-valid (ρ⁼-≤ l) = valid-ρ⁼ l , valid-ρ⁼ l
    σ-valid [] = [] , []
    σ-valid (τ₁≤τ₂ ∷ σ₁≤σ₂) = Σ-zip _∷_ _∷_ (τ-valid τ₁≤τ₂) (σ-valid σ₁≤σ₂)

    Γ-valid : validᵗ RegisterAssignment
    Γ-valid (Γ-≤ sp₁≤sp₂ regs₁≤regs₂) with σ-valid sp₁≤sp₂ | regs-valid regs₁≤regs₂
    ... | sp₁⋆ , sp₂⋆ | regs₁⋆ , regs₂⋆ =
      valid-registerₐ sp₁⋆ regs₁⋆ , valid-registerₐ sp₂⋆ regs₂⋆

    regs-valid : ∀ {n} → validᵗ (Vec Type n)
    regs-valid [] = [] , []
    regs-valid (τ≤ ∷ τs≤)
      with τ-valid τ≤ | regs-valid τs≤
    ... | τ₁⋆ , τ₂⋆ | τs₁⋆ , τs₂⋆ = τ₁⋆ ∷ τs₁⋆ , τ₂⋆ ∷ τs₂⋆

  infix 3 _≤φ?_
  _≤φ?_ : ∀ φ₁ φ₂ → Dec (φ₁ ≤φ φ₂)
  init ≤φ? init = yes φ-≤-init
  uninit ≤φ? init = no (λ ())
  _ ≤φ? uninit = yes φ-≤-uninit

  mutual
    subtype-decᵗ : ∀ A {{_ : TypeLike A}} → Set
    subtype-decᵗ A = ∀ Δ (x₁ x₂ : A) → Dec (Δ ⊢ x₁ ≤ x₂)

    infix 3 _⊢_≤τ?_
    _⊢_≤τ?_ : subtype-decᵗ Type
    Δ ⊢ α⁼ ι₁ ≤τ? α⁼ ι₂ with ι₁ ≟ ι₂ | ↓-decᵥ Δ ι₁ α
    Δ ⊢ α⁼ ι ≤τ? α⁼ .ι | yes refl | yes l = yes (α⁼-≤ l)
    Δ ⊢ α⁼ ι ≤τ? α⁼ .ι | yes refl | no ¬l =
      no (λ { (α⁼-≤ l) → ¬l l })
    Δ ⊢ α⁼ ι₁ ≤τ? α⁼ ι₂ | no ι₁≢ι₂ | _ = no (ι₁≢ι₂ ∘ help)
      where help : ∀ {Δ ι₁ ι₂} → Δ ⊢ α⁼ ι₁ ≤τ α⁼ ι₂ → ι₁ ≡ ι₂
            help (α⁼-≤ l) = refl
    Δ ⊢ α⁼ ι₁ ≤τ? int = no (λ ())
    Δ ⊢ α⁼ ι₁ ≤τ? uninit = no (λ ())
    Δ ⊢ α⁼ ι₁ ≤τ? (∀[ Δ₂ ] Γ₂) = no (λ ())
    Δ ⊢ α⁼ ι₁ ≤τ? tuple τs₂ = no (λ ())
    Δ ⊢ int ≤τ? α⁼ ι₂ = no (λ ())
    Δ ⊢ int ≤τ? int = yes int-≤
    Δ ⊢ int ≤τ? uninit = no (λ ())
    Δ ⊢ int ≤τ? (∀[ Δ₂ ] Γ₂) = no (λ ())
    Δ ⊢ int ≤τ? tuple τs₂ = no (λ ())
    Δ ⊢ uninit ≤τ? α⁼ ι₂ = no (λ ())
    Δ ⊢ uninit ≤τ? int = no (λ ())
    Δ ⊢ uninit ≤τ? uninit = yes uninit-≤
    Δ ⊢ uninit ≤τ? (∀[ Δ₂ ] Γ₂) = no (λ ())
    Δ ⊢ uninit ≤τ? tuple τs₂ = no (λ ())
    Δ ⊢ ∀[ Δ₁ ] Γ₁ ≤τ? α⁼ ι₂ = no (λ ())
    Δ ⊢ ∀[ Δ₁ ] Γ₁ ≤τ? int = no (λ ())
    Δ ⊢ ∀[ Δ₁ ] Γ₁ ≤τ? uninit = no (λ ())
    Δ ⊢ ∀[ Δ₁ ] Γ₁ ≤τ? (∀[ Δ₂ ] Γ₂)
      with Δ₁ ≟ Δ₂ | Δ₁ ++ Δ ⊢ Γ₂ ≤Γ? Γ₁
    Δ ⊢ ∀[ Δ' ] Γ₁ ≤τ? (∀[ .Δ' ] Γ₂)
      | yes refl | yes Γ₂≤Γ₁ = yes (∀-≤ Γ₂≤Γ₁)
    Δ ⊢ ∀[ Δ' ] Γ₁ ≤τ? (∀[ .Δ' ] Γ₂)
      | yes refl | no Γ₂≰Γ₁ = no (λ { (∀-≤ Γ₂≤Γ₁) → Γ₂≰Γ₁ Γ₂≤Γ₁ })
    Δ ⊢ ∀[ Δ₁ ] Γ₁ ≤τ? (∀[ Δ₂ ] Γ₂) | no Δ₁≢Δ₂ | _ = no (Δ₁≢Δ₂ ∘ help)
      where help : ∀ {Δ Δ₁ Δ₂ Γ₁ Γ₂} → Δ ⊢ ∀[ Δ₁ ] Γ₁ ≤τ ∀[ Δ₂ ] Γ₂ → Δ₁ ≡ Δ₂
            help (∀-≤ Γ₂≤Γ₁) = refl
    Δ ⊢ ∀[ Δ₁ ] Γ₁ ≤τ? tuple τs₂ = no (λ ())
    Δ ⊢ tuple τs₁ ≤τ? α⁼ ι₂ = no (λ ())
    Δ ⊢ tuple τs₁ ≤τ? int = no (λ ())
    Δ ⊢ tuple τs₁ ≤τ? uninit = no (λ ())
    Δ ⊢ tuple τs₁ ≤τ? ∀[ Δ₂ ] Γ₂ = no (λ ())
    Δ ⊢ tuple τs₁ ≤τ? tuple τs₂ with Δ ⊢ τs₁ ≤τs⁻? τs₂
    ... | yes τs₁≤τs₂ = yes (tuple-≤ τs₁≤τs₂)
    ... | no τs₁≰τs₂ = no (λ { (tuple-≤ τs₁≤τs₂) → τs₁≰τs₂ τs₁≤τs₂ })

    infix 3 _⊢_≤τ⁻?_
    _⊢_≤τ⁻?_ : subtype-decᵗ InitType
    Δ ⊢ τ₁ , φ₁ ≤τ⁻? τ₂ , φ₂ with τ₁ ≟ τ₂
    ... | no τ₁≢τ₂ = no (help τ₁≢τ₂)
      where help : ∀ {τ₁ τ₂} →
                     τ₁ ≢ τ₂ →
                     ¬ (Δ ⊢ τ₁ , φ₁ ≤τ⁻ τ₂ , φ₂)
            help τ₁≢τ₂ (τ⁻-≤ τ⋆ φ₁≤φ₂) = τ₁≢τ₂ refl
    Δ ⊢ τ , φ₁ ≤τ⁻? .τ , φ₂
        | yes refl with Δ ⊢ τ ≤τ? τ | φ₁ ≤φ? φ₂
    ... | yes τ≤τ | yes φ₁≤φ₂ = yes (τ⁻-≤ (proj₁ (τ-valid τ≤τ)) φ₁≤φ₂)
    ... | no τ≰τ | _ = no (λ { (τ⁻-≤ τ⋆ φ₁≤φ₂) → τ≰τ (τ-refl τ⋆)})
    ... | _ | no φ₁≰φ₂ = no (λ { (τ⁻-≤ τ⋆ φ₁≤φ₂) → φ₁≰φ₂ φ₁≤φ₂})

    infix 3 _⊢_≤τs⁻?_
    _⊢_≤τs⁻?_ : subtype-decᵗ (List InitType)
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
    _⊢_≤σ?_ : subtype-decᵗ StackType
    Δ ⊢ ρ⁼ ι₁ ≤σ? ρ⁼ ι₂ with ι₁ ≟ ι₂ | ↓-decᵥ Δ ι₁ ρ
    Δ ⊢ ρ⁼ ι ≤σ? ρ⁼ .ι | yes refl | yes l = yes (ρ⁼-≤ l)
    Δ ⊢ ρ⁼ ι ≤σ? ρ⁼ .ι | yes refl | no ¬l =
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
    _⊢_≤Γ?_ : subtype-decᵗ RegisterAssignment
    Δ ⊢ registerₐ sp₁ regs₁ ≤Γ? registerₐ sp₂ regs₂
      with Δ ⊢ sp₁ ≤σ? sp₂ | Δ ⊢ regs₁ ≤regs? regs₂
    ... | yes sp₁≤sp₂ | yes regs₁≤regs₂ = yes (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
    ... | no sp₁≰sp₂ | _ =
      no (λ { (Γ-≤ sp₁≤sp₂ regs₁≤regs₂) → sp₁≰sp₂ sp₁≤sp₂ })
    ... | _ | no regs₁≰regs₂ =
      no (λ { (Γ-≤ sp₁≤sp₂ regs₁≤regs₂) → regs₁≰regs₂ regs₁≤regs₂ })

    infix 3 _⊢_≤regs?_
    _⊢_≤regs?_ : ∀ {n} → subtype-decᵗ (Vec Type n)
    Δ ⊢ [] ≤regs? [] = yes []
    Δ ⊢ τ₁ ∷ τs₁ ≤regs? τ₂ ∷ τs₂ with
      Δ ⊢ τ₁ ≤τ? τ₂ | Δ ⊢ τs₁ ≤regs? τs₂
    ... | yes τ₁≤τ₂ | yes τs₁≤τs₂ = yes (τ₁≤τ₂ ∷ τs₁≤τs₂)
    ... | no τ₁≰τ₂ | _ = no (λ { (τ₁≤τ₂ ∷ τs₁≤τs₂) → τ₁≰τ₂ τ₁≤τ₂ })
    ... | _ | no τs₁≰τs₂ =
      no (λ { (τ₁≤τ₂ ∷ τs₁≤τs₂) → τs₁≰τs₂ τs₁≤τs₂ })

List-TypeLike⁺ : ∀ A {T : TypeLike A} {{T⁺ : TypeLike⁺ A}} →
                   TypeLike⁺ (List A) {{List-TypeLike A}}
List-TypeLike⁺ A = typeLike⁺
    (All→AllZip ∘ All-map ≤-refl)
    (AllZip-trans ≤-trans)
    (AllZip-split' ∘ AllZip-map ≤-valid)
    (AllZip-dec ∘ _⊢_≤?_)

instance
  Type-TypeLike⁺ : TypeLike⁺ Type
  Type-TypeLike⁺ = typeLike⁺ τ-refl τ-trans τ-valid _⊢_≤τ?_

  TypeVec-TypeLike⁺ : ∀ {n} → TypeLike⁺ (Vec Type n)
  TypeVec-TypeLike⁺ = typeLike⁺ regs-refl regs-trans regs-valid _⊢_≤regs?_

  TypeList-TypeLike⁺ : TypeLike⁺ (List Type)
  TypeList-TypeLike⁺ = List-TypeLike⁺ Type

  InitType-TypeLike⁺ : TypeLike⁺ InitType
  InitType-TypeLike⁺ = typeLike⁺ τ⁻-refl τ⁻-trans τ⁻-valid _⊢_≤τ⁻?_

  InitTypeList-TypeLike⁺ : TypeLike⁺ (List InitType)
  InitTypeList-TypeLike⁺ = typeLike⁺ τs⁻-refl τs⁻-trans τs⁻-valid _⊢_≤τs⁻?_

  StackType-TypeLike⁺ : TypeLike⁺ StackType
  StackType-TypeLike⁺ = typeLike⁺ σ-refl σ-trans σ-valid _⊢_≤σ?_

  RegisterAssignment-TypeLike⁺ : TypeLike⁺ RegisterAssignment
  RegisterAssignment-TypeLike⁺ = typeLike⁺ Γ-refl Γ-trans Γ-valid _⊢_≤Γ?_
