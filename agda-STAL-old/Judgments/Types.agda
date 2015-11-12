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
    _⊢_Valid : TypeAssignment → A → Set

-- It would be really nice if these were equivalent, but they are
-- apparently not.
-- open TypeLike {{...}} public
infix 3 _⊢_Valid
_⊢_Valid : {A : Set} {{T : TypeLike A}} → TypeAssignment → A → Set
_⊢_Valid {{T}} = TypeLike._⊢_Valid T

mutual
  infix 3 _⊢_Type
  data _⊢_Type (Δ : TypeAssignment) : Type → Set where
    valid-α⁼ :
         ∀ {ι} →
       Δ ↓ ι ⇒ α →
      -------------
      Δ ⊢ α⁼ ι Type

    valid-int :
      ------------
      Δ ⊢ int Type

    valid-ns :
      -----------
      Δ ⊢ ns Type

    valid-∀ :
                 ∀ {Δ' Γ} →
           Δ ⊢ Δ' TypeAssignment →
      Δ' ++ Δ ⊢ Γ RegisterAssignment →
      --------------------------------
            Δ ⊢ ∀[ Δ' ] Γ Type

    valid-tuple :
         ∀ {τs : List InitType} →
      All (λ τ⁻ → Δ ⊢ τ⁻ InitType) τs →
      ---------------------------------
             Δ ⊢ tuple τs Type

  infix 3 _⊢_InitType
  data _⊢_InitType (Δ : TypeAssignment) : InitType → Set where
    valid-τ⁻ :
           ∀ {τ φ} →
          Δ ⊢ τ Type →
      ------------------
      Δ ⊢ τ , φ InitType

  infix 3  _⊢_StackType
  data _⊢_StackType (Δ : TypeAssignment) : StackType → Set where
    valid-ρ⁼ :
           ∀ {ι} →
         Δ ↓ ι ⇒ ρ →
      ------------------
      Δ ⊢ ρ⁼ ι StackType

    valid-[] :
      ----------------
      Δ ⊢ [] StackType

    _∷_ :
          ∀ {τ σ} →
         Δ ⊢ τ Type →
       Δ ⊢ σ StackType →
      -------------------
      Δ ⊢ τ ∷ σ StackType

  infix 3  _⊢_TypeAssignment
  infixr 5 _∷_
  data _⊢_TypeAssignment : TypeAssignment → TypeAssignment → Set where
    [] :
             ∀ {Δ} →
      ---------------------
      Δ ⊢ [] TypeAssignment

    _∷_ :
              ∀ {a Δ₁ Δ₂} →
      Δ₂ ++ Δ₁ ⊢ a TypeAssignmentValue →
           Δ₁ ⊢ Δ₂ TypeAssignment →
      ----------------------------------
         Δ₁ ⊢ a ∷ Δ₂ TypeAssignment

  infix 3  _⊢_TypeAssignmentValue
  data _⊢_TypeAssignmentValue : TypeAssignment →
                                TypeAssignmentValue → Set where
    valid-α :
              ∀ {Δ} →
      -------------------------
      Δ ⊢ α TypeAssignmentValue

    valid-ρ :
              ∀ {Δ} →
      -------------------------
      Δ ⊢ ρ TypeAssignmentValue

  infix 3 _⊢_RegisterAssignment
  data _⊢_RegisterAssignment (Δ : TypeAssignment) :
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

infix 3 _⊢_Instantiation
data _⊢_Instantiation : TypeAssignment → Instantiation → Set where
  valid-α :
           ∀ {Δ τ} →
          Δ ⊢ τ Type →
    -------------------------
    α ∷ Δ ⊢ α τ Instantiation

  valid-ρ :
           ∀ {Δ σ} →
        Δ ⊢ σ StackType →
    -------------------------
    ρ ∷ Δ ⊢ ρ σ Instantiation

infix 3 _⊢_WeakCastValue
data _⊢_WeakCastValue : TypeAssignment → WeakCastValue → Set where
  valid-weaken :
             ∀ {Δ n} →
    --------------------------
    Δ ⊢ weaken n WeakCastValue

  valid-inst :
           ∀ {Δ i} →
      Δ ⊢ i Instantiation →
    ------------------------
    Δ ⊢ inst i WeakCastValue

infix 3 _⊢_StrongCastValue
data _⊢_StrongCastValue : TypeAssignment → StrongCastValue → Set where
  valid-weaken :
             ∀ {Δ Δ⁺} →
       Δ ⊢ Δ⁺ TypeAssignment →
    -----------------------------
    Δ ⊢ weaken Δ⁺ StrongCastValue

  valid-inst :
            ∀ {Δ i} →
       Δ ⊢ i Instantiation →
    --------------------------
    Δ ⊢ inst i StrongCastValue

infix 3 _⊢_WeakCast
data _⊢_WeakCast : TypeAssignment → WeakCast → Set where
  valid-zero :
          ∀ {Δ cᵥ} →
    Δ ⊢ cᵥ WeakCastValue →
    ----------------------
    Δ ⊢ cᵥ / zero WeakCast

  valid-suc :
           ∀ {a Δ cᵥ ι} →
        Δ ⊢ cᵥ / ι WeakCast →
    ---------------------------
    a ∷ Δ ⊢ cᵥ / suc ι WeakCast

infix 3 _⊢_StrongCast
data _⊢_StrongCast : TypeAssignment → StrongCast → Set where
  valid-zero :
          ∀ {Δ cᵥ} →
    Δ ⊢ cᵥ StrongCastValue →
    ----------------------
    Δ ⊢ cᵥ / zero StrongCast

  valid-suc :
           ∀ {a Δ cᵥ ι} →
        Δ ⊢ cᵥ / ι StrongCast →
    ---------------------------
    a ∷ Δ ⊢ cᵥ / suc ι StrongCast

Vec-TypeLike : ∀ A m {{T : TypeLike A}} → TypeLike (Vec A m)
Vec-TypeLike A m = typeLike (λ Δ xs → Allᵥ (λ x → Δ ⊢ x Valid) xs)

List-TypeLike : ∀ A {{T : TypeLike A}} → TypeLike (List A)
List-TypeLike A = typeLike (λ Δ xs → All (λ x → Δ ⊢ x Valid) xs)

instance
  InitializationFlag-TypeLike : TypeLike InitializationFlag
  InitializationFlag-TypeLike = typeLike (λ Δ φ → ⊤)

  Type-TypeLike : TypeLike Type
  Type-TypeLike = typeLike _⊢_Type

  TypeVec-TypeLike : ∀ {m} → TypeLike (Vec Type m)
  TypeVec-TypeLike = Vec-TypeLike Type _

  TypeList-TypeLike : TypeLike (List Type)
  TypeList-TypeLike = List-TypeLike Type

  InitType-TypeLike : TypeLike InitType
  InitType-TypeLike = typeLike _⊢_InitType

  InitTypeVec-TypeLike : ∀ {m} → TypeLike (Vec InitType m)
  InitTypeVec-TypeLike = Vec-TypeLike InitType _

  InitTypeList-TypeLike : TypeLike (List InitType)
  InitTypeList-TypeLike = List-TypeLike InitType

  StackType-TypeLike : TypeLike StackType
  StackType-TypeLike = typeLike _⊢_StackType

  LabelAssignment-TypeLike : TypeLike LabelAssignment
  LabelAssignment-TypeLike = typeLike (const ⊢_LabelAssignment)

  TypeAssignment-TypeLike : TypeLike TypeAssignment
  TypeAssignment-TypeLike = typeLike _⊢_TypeAssignment

  TypeAssignmentValue-TypeLike : TypeLike TypeAssignmentValue
  TypeAssignmentValue-TypeLike = typeLike _⊢_TypeAssignmentValue

  RegisterAssignment-TypeLike : TypeLike RegisterAssignment
  RegisterAssignment-TypeLike = typeLike _⊢_RegisterAssignment

  Instantiation-TypeLike : TypeLike Instantiation
  Instantiation-TypeLike = typeLike _⊢_Instantiation

  WeakCastValue-TypeLike : TypeLike WeakCastValue
  WeakCastValue-TypeLike = typeLike _⊢_WeakCastValue

  WeakCast-TypeLike : TypeLike WeakCast
  WeakCast-TypeLike = typeLike _⊢_WeakCast

  StrongCastValue-TypeLike : TypeLike StrongCastValue
  StrongCastValue-TypeLike = typeLike _⊢_StrongCastValue

  StrongCast-TypeLike : TypeLike StrongCast
  StrongCast-TypeLike = typeLike _⊢_StrongCast
