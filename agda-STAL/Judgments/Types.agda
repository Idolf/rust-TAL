module Judgments.Types where

open import Util
open import Judgments.Grammar
open HighGrammar

-- This file contains judgments to determine if
-- a type-like object is valid in a given context,
-- and to determine if one value is a subtype of another.
record TypeLike (A : Set) : Set1 where
  constructor typeLike
  infix 3 _⊢_Valid
  infix 3 _⊢_≤_
  field
    _⊢_Valid : TypeAssumptions → A → Set
    _⊢_≤_ : TypeAssumptions → A → A → Set
open TypeLike {{...}} public

mutual
  infix 3 _⊢_Type
  data _⊢_Type (Δ : TypeAssumptions) : Type → Set where
    valid-α⁼ :
         ∀ {ι} →
       Δ ↓ ι ⇒ α →
      -------------
      Δ ⊢ α⁼ ι Type

    valid-int :
      ------------
      Δ ⊢ int Type

    valid-ns :
      ------------
      Δ ⊢ ns Type

    valid-∀ :
                 ∀ {Δ' Γ} →
      Δ' ++ Δ ⊢ Γ RegisterAssignment →
      --------------------------------
            Δ ⊢ ∀[ Δ' ] Γ Type

    valid-tuple :
         ∀ {τs : List InitType} →
      All (λ τ⁻ → Δ ⊢ τ⁻ InitType) τs →
      ---------------------------------
             Δ ⊢ tuple τs Type

  infix 3 _⊢_InitType
  data _⊢_InitType (Δ : TypeAssumptions) : InitType → Set where
    valid-τ⁻ :
           ∀ {τ φ} →
          Δ ⊢ τ Type →
      ------------------
      Δ ⊢ τ , φ InitType

  infix 3 _⊢_StackType
  data _⊢_StackType (Δ : TypeAssumptions) : StackType → Set where
    valid-ρ⁼ :
           ∀ {ι} →
         Δ ↓ ι ⇒ ρ →
      ------------------
      Δ ⊢ ρ⁼ ι StackType

    [] :
      ----------------
      Δ ⊢ [] StackType

    _∷_ :
          ∀ {τ σ} →
         Δ ⊢ τ Type →
       Δ ⊢ σ StackType →
      -------------------
      Δ ⊢ τ ∷ σ StackType

  infix 3 _⊢_RegisterAssignment
  data _⊢_RegisterAssignment (Δ : TypeAssumptions) :
                             RegisterAssignment → Set where
    valid-registerₐ :
                  ∀ {sp regs} →
                Δ ⊢ sp StackType →
           Allᵥ (λ τ → Δ ⊢ τ Type) regs →
      ----------------------------------------
      Δ ⊢ registerₐ sp regs RegisterAssignment

mutual
  infix 3 _⊢_≤τ_
  data _⊢_≤τ_ (Δ : TypeAssumptions) : Type → Type → Set where
    α⁼-≤ :
          ∀ {ι} →
        Δ ↓ ι ⇒ α →
      ----------------
      Δ ⊢ α⁼ ι ≤τ α⁼ ι

    int-≤ :
      --------------
      Δ ⊢ int ≤τ int

    ns-≤ :
      ------------
      Δ ⊢ ns ≤τ ns

    ∀-≤ :
            ∀ {Δ' Γ₁ Γ₂} →
          Δ' ++ Δ ⊢ Γ₂ ≤Γ Γ₁ →
      ----------------------------
      Δ ⊢ ∀[ Δ' ] Γ₁ ≤τ ∀[ Δ' ] Γ₂

    tuple-≤ :
                     ∀ {τs₁ τs₂} →
      AllZip (λ τ⁻₁ τ⁻₂ → Δ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂) τs₁ τs₂ →
      ----------------------------------------------
               Δ ⊢ tuple τs₁ ≤τ tuple τs₂

  infix 3 _≤φ_
  data _≤φ_ : InitializationFlag → InitializationFlag → Set where
    φ-≤-init :
       ∀ {φ} →
      ---------
      init ≤φ φ

    φ-≤-uninit :
        ∀ {φ} →
      -----------
      φ ≤φ uninit

  infix 3 _⊢_≤τ⁻_
  data _⊢_≤τ⁻_ (Δ : TypeAssumptions) : InitType → InitType → Set where
    τ⁻-≤ :
          ∀ {τ φ₁ φ₂} →
          Δ ⊢ τ Type →
            φ₁ ≤φ φ₂ →
      ---------------------
      Δ ⊢ τ , φ₁ ≤τ⁻ τ , φ₂

  infix 3 _⊢_≤σ_
  infixr 5 _∷_
  data _⊢_≤σ_ (Δ : TypeAssumptions) : StackType → StackType → Set where
    ρ⁼-≤ :
          ∀ {ι} →
        Δ ↓ ι ⇒ ρ →
      ----------------
      Δ ⊢ ρ⁼ ι ≤σ ρ⁼ ι

    [] :
      ------------
      Δ ⊢ [] ≤σ []

    _∷_ :
       ∀ {τ₁ τ₂ σ₁ σ₂} →
         Δ ⊢ τ₁ ≤τ τ₂ →
         Δ ⊢ σ₁ ≤σ σ₂ →
      ----------------------
      Δ ⊢ τ₁ ∷ σ₁ ≤σ τ₂ ∷ σ₂

  infix 3 _⊢_≤Γ_
  data _⊢_≤Γ_ (Δ : TypeAssumptions) : (Γ₁ Γ₂ : RegisterAssignment) → Set where
    Γ-≤ :
                ∀ {sp₁ sp₂ regs₁ regs₂} →
                    Δ ⊢ sp₁ ≤σ sp₂ →
      AllZipᵥ (λ τ₂ τ₁ → Δ ⊢ τ₂ ≤τ τ₁) regs₁ regs₂ →
      ----------------------------------------------
      Δ ⊢ registerₐ sp₁ regs₁ ≤Γ registerₐ sp₂ regs₂

List-TypeLike : ∀ A {{T : TypeLike A}} → TypeLike (List A)
List-TypeLike A =
  typeLike (λ Δ xs → All (λ x → Δ ⊢ x Valid) xs)
           (λ Δ xs₁ xs₂ → AllZip (λ x₁ x₂ → Δ ⊢ x₁ ≤ x₂) xs₁ xs₂)

instance
  Type-TypeLike : TypeLike Type
  Type-TypeLike = typeLike _⊢_Type _⊢_≤τ_

  TypeVec-TypeLike : ∀ {n} → TypeLike (Vec Type n)
  TypeVec-TypeLike =
    typeLike (λ Δ → Allᵥ (λ τ → Δ ⊢ τ Type))
             (λ Δ → AllZipᵥ (λ τ₂ τ₁ → Δ ⊢ τ₂ ≤τ τ₁))

  TypeList-TypeLike : TypeLike (List Type)
  TypeList-TypeLike = List-TypeLike Type

  InitType-TypeLike : TypeLike InitType
  InitType-TypeLike = typeLike _⊢_InitType _⊢_≤τ⁻_

  InitTypeList-TypeLike : TypeLike (List InitType)
  InitTypeList-TypeLike = List-TypeLike InitType

  StackType-TypeLike : TypeLike StackType
  StackType-TypeLike = typeLike _⊢_StackType _⊢_≤σ_

  RegisterAssignment-TypeLike : TypeLike RegisterAssignment
  RegisterAssignment-TypeLike = typeLike _⊢_RegisterAssignment _⊢_≤Γ_
