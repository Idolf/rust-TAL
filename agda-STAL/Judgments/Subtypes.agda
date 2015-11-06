module Judgments.Subtypes where

open import Util
open import Judgments.Grammar
open import Judgments.Types

-- This file contains judgments to determine subtyping
-- relations. As syntactic sugar, we include this record
-- and add instances for it:
record Subtype (A : Set) : Set1 where
  constructor subtype
  infix 3 _⊢_≤_
  field
    _⊢_≤_ : TypeAssignment → A → A → Set

-- It would be really nice if these were equivalent, but they are
-- apparently not.
-- open Subtype {{...}} public
infix 3 _⊢_≤_
_⊢_≤_ : ∀ {A} {{S : Subtype A}} →
        TypeAssignment → A → A → Set
_⊢_≤_ {{S}} = Subtype._⊢_≤_ S

mutual
  infix 3 _⊢_≤τ_
  data _⊢_≤τ_ (Δ : TypeAssignment) : Type → Type → Set where
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
        Δ ⊢ Δ' TypeAssignment →
          Δ' ++ Δ ⊢ Γ₁ ≤Γ Γ₂ →
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
      ------------
      init ≤φ init

    φ-≤-uninit :
        ∀ {φ} →
      -----------
      φ ≤φ uninit

  infix 3 _⊢_≤τ⁻_
  data _⊢_≤τ⁻_ (Δ : TypeAssignment) : InitType → InitType → Set where
    τ⁻-≤ :
          ∀ {τ φ₁ φ₂} →
          Δ ⊢ τ Valid →
            φ₁ ≤φ φ₂ →
      ---------------------
      Δ ⊢ τ , φ₁ ≤τ⁻ τ , φ₂

  infix 3 _⊢_≤σ_
  infixr 5 _∷_
  data _⊢_≤σ_ (Δ : TypeAssignment) : StackType → StackType → Set where
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
  data _⊢_≤Γ_ (Δ : TypeAssignment) : (Γ₁ Γ₂ : RegisterAssignment) → Set where
    Γ-≤ :
                ∀ {sp₁ sp₂ regs₁ regs₂} →
                    Δ ⊢ sp₁ ≤σ sp₂ →
      AllZipᵥ (λ τ₁ τ₂ → Δ ⊢ τ₁ ≤τ τ₂) regs₁ regs₂ →
      ----------------------------------------------
      Δ ⊢ registerₐ sp₁ regs₁ ≤Γ registerₐ sp₂ regs₂


Vec-Subtype : ∀ A m {{S : Subtype A}} → Subtype (Vec A m)
Vec-Subtype A m =
  subtype (λ Δ xs₁ xs₂ → AllZipᵥ (λ x₁ x₂ → Δ ⊢ x₁ ≤ x₂) xs₁ xs₂)

List-Subtype : ∀ A {{S : Subtype A}} → Subtype (List A)
List-Subtype A =
  subtype (λ Δ xs₁ xs₂ → AllZip (λ x₁ x₂ → Δ ⊢ x₁ ≤ x₂) xs₁ xs₂)

instance
  InitializationFlag-Subtype : Subtype InitializationFlag
  InitializationFlag-Subtype = subtype (const _≤φ_)

  Type-Subtype : Subtype Type
  Type-Subtype = subtype _⊢_≤τ_

  TypeVec-Subtype : ∀ {m} → Subtype (Vec Type m)
  TypeVec-Subtype = Vec-Subtype Type _

  TypeList-Subtype : Subtype (List Type)
  TypeList-Subtype = List-Subtype Type

  InitType-Subtype : Subtype InitType
  InitType-Subtype = subtype _⊢_≤τ⁻_

  InitTypeVec-Subtype : ∀ {m} → Subtype (Vec InitType m)
  InitTypeVec-Subtype = Vec-Subtype InitType _

  InitTypeList-Subtype : Subtype (List InitType)
  InitTypeList-Subtype = List-Subtype InitType

  StackType-Subtype : Subtype StackType
  StackType-Subtype = subtype _⊢_≤σ_

  RegisterAssignment-Subtype : Subtype RegisterAssignment
  RegisterAssignment-Subtype = subtype _⊢_≤Γ_
