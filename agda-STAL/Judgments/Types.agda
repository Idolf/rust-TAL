module Judgments.Types where

open import Util
open import Judgments.Grammar

-- This file contains judgments to determine of
-- a type-like object is valid in a given context.
-- As syntactic sugar, we include this record and
-- add instances for it:
record TypeLike (A : Set) : Set1 where
  constructor typeLike
  infix 3 _⊢_Valid
  field
    _⊢_Valid : TypeAssumptions → A → Set
    TypeLike-junk : ⊤
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

  infix 3  _⊢_StackType
  infixr 5 _∷_
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

infix 3 ⊢_GlobalLabelAssignment
⊢_GlobalLabelAssignment : GlobalLabelAssignment → Set
⊢ ψ₁ GlobalLabelAssignment = All (λ τ → [] ⊢ τ Type) ψ₁

infix 3 ⊢_HeapLabelAssignment
⊢_HeapLabelAssignment : HeapLabelAssignment → Set
⊢ ψ₂ HeapLabelAssignment = All (λ τ → [] ⊢ τ Type) ψ₂

infix 3 ⊢_LabelAssignment
⊢_LabelAssignment : LabelAssignment → Set
⊢ ψ₁ , ψ₂ LabelAssignment =
  (⊢ ψ₁ GlobalLabelAssignment) × (⊢ ψ₂ HeapLabelAssignment)

Vec-TypeLike : ∀ A m {{T : TypeLike A}} → TypeLike (Vec A m)
Vec-TypeLike A m = typeLike (λ Δ xs → Allᵥ (λ x → Δ ⊢ x Valid) xs) tt

List-TypeLike : ∀ A {{T : TypeLike A}} → TypeLike (List A)
List-TypeLike A = typeLike (λ Δ xs → All (λ x → Δ ⊢ x Valid) xs) tt

instance
  InitializationFlag-TypeLike : TypeLike InitializationFlag
  InitializationFlag-TypeLike = typeLike (λ Δ φ → ⊤) tt

  Type-TypeLike : TypeLike Type
  Type-TypeLike = typeLike _⊢_Type tt

  TypeVec-TypeLike : ∀ {n} → TypeLike (Vec Type n)
  TypeVec-TypeLike = Vec-TypeLike Type _

  TypeList-TypeLike : TypeLike (List Type)
  TypeList-TypeLike = List-TypeLike Type

  InitType-TypeLike : TypeLike InitType
  InitType-TypeLike = typeLike _⊢_InitType tt

  InitTypeVec-TypeLike : ∀ {n} → TypeLike (Vec InitType n)
  InitTypeVec-TypeLike = Vec-TypeLike InitType _

  InitTypeList-TypeLike : TypeLike (List InitType)
  InitTypeList-TypeLike = List-TypeLike InitType

  StackType-TypeLike : TypeLike StackType
  StackType-TypeLike = typeLike _⊢_StackType tt

  LabelAssignment-TypeLike : TypeLike LabelAssignment
  LabelAssignment-TypeLike = typeLike (const ⊢_LabelAssignment) tt

  RegisterAssignment-TypeLike : TypeLike RegisterAssignment
  RegisterAssignment-TypeLike = typeLike _⊢_RegisterAssignment tt
