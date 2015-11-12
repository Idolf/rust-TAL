module Lemmas.Types where

open import Util
open import Judgments
open import Lemmas.Equality

-- The purpose of this file is
-- to include instances of this record.
record TypeLike⁺ (A : Set) {{_ : TypeLike A}} : Set1 where
  constructor typeLike⁺
  infix 3 _⊢?_Valid
  field
    _⊢?_Valid : ∀ Δ (v : A) → Dec (Δ ⊢ v Valid)
    valid-++ : ∀ {Δ Δ'} {v : A} → Δ ⊢ v Valid → Δ ++ Δ' ⊢ v Valid
open TypeLike⁺ {{...}} public

private
  mutual
    infix 3 _⊢?_Type
    _⊢?_Type : ∀ Δ τ → Dec (Δ ⊢ τ Type)
    Δ ⊢? α⁼ ι Type = dec-inj valid-α⁼ (λ { (valid-α⁼ l) → l }) (↓-decᵥ Δ ι α)
    Δ ⊢? int Type = yes valid-int
    Δ ⊢? ns Type = yes valid-ns
    Δ ⊢? ∀[ Δ' ] Γ Type =
      dec-inj valid-∀ (λ { (valid-∀ Γ⋆) → Γ⋆ }) (Δ' ++ Δ ⊢? Γ RegisterAssignment)
    Δ ⊢? tuple τs Type =
      dec-inj valid-tuple (λ { (valid-tuple τs⋆) → τs⋆ }) (Δ ⊢? τs InitTypes)

    infix 3 _⊢?_InitType
    _⊢?_InitType : ∀ Δ τ⁻ → Dec (Δ ⊢ τ⁻ InitType)
    Δ ⊢? τ , φ InitType =
      dec-inj valid-τ⁻ (λ { (valid-τ⁻ τ⋆) → τ⋆ }) (Δ ⊢? τ Type)

    infix 3 _⊢?_InitTypes
    _⊢?_InitTypes : ∀ Δ τs⁻ → Dec (All (λ τ⁻ → Δ ⊢ τ⁻ InitType) τs⁻)
    Δ ⊢? [] InitTypes = yes []
    Δ ⊢? τ ∷ τs InitTypes with Δ ⊢? τ InitType | Δ ⊢? τs InitTypes
    ... | yes τ⋆ | yes τs⋆ = yes (τ⋆ ∷ τs⋆)
    ... | no ¬τ⋆ | _  = no (λ { (τ⋆ ∷ τs⋆) → ¬τ⋆ τ⋆ })
    ... | _ | no ¬τs⋆ = no (λ { (τ⋆ ∷ τs⋆) → ¬τs⋆ τs⋆ })

    infix 3  _⊢?_StackType
    _⊢?_StackType : ∀ Δ σ → Dec (Δ ⊢ σ StackType)
    Δ ⊢? ρ⁼ ι StackType =
      dec-inj valid-ρ⁼ (λ { (valid-ρ⁼ l) → l }) (↓-decᵥ Δ ι ρ)
    Δ ⊢? [] StackType = yes []
    Δ ⊢? τ ∷ σ StackType with Δ ⊢? τ Type | Δ ⊢? σ StackType
    ... | yes τ⋆ | yes σ⋆ = yes (τ⋆ ∷ σ⋆)
    ... | no ¬τ⋆ | _  = no (λ { (τ⋆ ∷ σ⋆) → ¬τ⋆ τ⋆ })
    ... | _ | no ¬σ⋆ = no (λ { (τ⋆ ∷ σ⋆) → ¬σ⋆ σ⋆ })

    infix 3 _⊢?_Types
    _⊢?_Types : ∀ Δ (τs : List Type) → Dec (All (λ τ → Δ ⊢ τ Type) τs)
    Δ ⊢? [] Types = yes []
    Δ ⊢? τ ∷ τs Types with Δ ⊢? τ Type | Δ ⊢? τs Types
    ... | yes τ⋆ | yes τs⋆ = yes (τ⋆ ∷ τs⋆)
    ... | no ¬τ⋆ | _  = no (λ { (τ⋆ ∷ τs⋆) → ¬τ⋆ τ⋆ })
    ... | _ | no ¬τs⋆ = no (λ { (τ⋆ ∷ τs⋆) → ¬τs⋆ τs⋆ })

    infix 3 ⊢?_GlobalLabelAssignment
    ⊢?_GlobalLabelAssignment : ∀ ψ₁ → Dec (⊢ ψ₁ GlobalLabelAssignment)
    ⊢? ψ₁ GlobalLabelAssignment = [] ⊢? ψ₁ Types

    infix 3 ⊢?_HeapLabelAssignment
    ⊢?_HeapLabelAssignment : ∀ ψ₂ → Dec (⊢ ψ₂ HeapLabelAssignment)
    ⊢? ψ₂ HeapLabelAssignment = [] ⊢? ψ₂ Types

    infix 3 ⊢?_LabelAssignment
    ⊢?_LabelAssignment : ∀ ψ → Dec (⊢ ψ LabelAssignment)
    ⊢? ψ₁ , ψ₂ LabelAssignment =
      dec-inj₂ _,_
               id
               (⊢? ψ₁ GlobalLabelAssignment)
               (⊢? ψ₂ HeapLabelAssignment)

    infix 3 _⊢?_RegisterAssignment
    _⊢?_RegisterAssignment : ∀ Δ Γ → Dec (Δ ⊢ Γ RegisterAssignment)
    Δ ⊢? registerₐ sp regs RegisterAssignment =
      dec-inj₂ valid-registerₐ
               (λ { (valid-registerₐ sp⋆ regs⋆) → sp⋆ , regs⋆ })
               (Δ ⊢? sp StackType)
               (Δ ⊢? regs RegTypes)

    infix 3 _⊢?_RegTypes
    _⊢?_RegTypes : ∀ Δ {m} (τs : Vec Type m) →
                     Dec (Allᵥ (λ τ → Δ ⊢ τ Type) τs)
    Δ ⊢? [] RegTypes = yes []
    Δ ⊢? τ ∷ τs RegTypes with Δ ⊢? τ Type | Δ ⊢? τs RegTypes
    ... | yes τ⋆ | yes τs⋆ = yes (τ⋆ ∷ τs⋆)
    ... | no ¬τ⋆ | _  = no (λ { (τ⋆ ∷ τs⋆) → ¬τ⋆ τ⋆ })
    ... | _ | no ¬τs⋆ = no (λ { (τ⋆ ∷ τs⋆) → ¬τs⋆ τs⋆ })

  mutual
    τ-valid-++ : ∀ {Δ Δ' τ} →
                   Δ ⊢ τ Type →
                   Δ ++ Δ' ⊢ τ Type
    τ-valid-++ (valid-α⁼ l) = valid-α⁼ (↓-add-right _ l)
    τ-valid-++ valid-int = valid-int
    τ-valid-++ valid-ns = valid-ns
    τ-valid-++ {Δ = Δ} {Δ'} (valid-∀ {Δᵥ} {Γ} Γ⋆) =
      valid-∀ (subst (λ Δ → Δ ⊢ Γ RegisterAssignment)
              (List-++-assoc Δᵥ Δ Δ') (Γ-valid-++ Γ⋆))
    τ-valid-++ (valid-tuple τs⋆) = valid-tuple (τs⁻-valid-++ τs⋆)

    τ⁻-valid-++ : ∀ {Δ Δ' τ⁻} →
                    Δ ⊢ τ⁻ InitType →
                    Δ ++ Δ' ⊢ τ⁻ InitType
    τ⁻-valid-++ (valid-τ⁻ τ⋆) = valid-τ⁻ (τ-valid-++ τ⋆)

    τs⁻-valid-++ : ∀ {Δ Δ' τs⁻} →
                     All (λ τ⁻ → Δ ⊢ τ⁻ InitType) τs⁻ →
                     All (λ τ⁻ → Δ ++ Δ' ⊢ τ⁻ InitType) τs⁻
    τs⁻-valid-++ [] = []
    τs⁻-valid-++ (τ⁻⋆ ∷ τs⁻⋆) = τ⁻-valid-++ τ⁻⋆ ∷ τs⁻-valid-++ τs⁻⋆

    σ-valid-++ : ∀ {Δ Δ' σ} →
                     Δ ⊢ σ StackType →
                     Δ ++ Δ' ⊢ σ StackType
    σ-valid-++ (valid-ρ⁼ l) = valid-ρ⁼ (↓-add-right _ l)
    σ-valid-++ [] = []
    σ-valid-++ (τ⋆ ∷ σ⋆) = τ-valid-++ τ⋆ ∷ σ-valid-++ σ⋆

    Γ-valid-++ : ∀ {Δ Δ' Γ} →
                   Δ ⊢ Γ RegisterAssignment →
                   Δ ++ Δ' ⊢ Γ RegisterAssignment
    Γ-valid-++ (valid-registerₐ sp⋆ regs⋆) =
      valid-registerₐ (σ-valid-++ sp⋆) (regs-valid-++ regs⋆)

    regs-valid-++ : ∀ {Δ Δ' m} {τs : Vec Type m} →
                      Allᵥ (λ τ → Δ ⊢ τ Type) τs →
                      Allᵥ (λ τ → Δ ++ Δ' ⊢ τ Type) τs
    regs-valid-++ [] = []
    regs-valid-++ (τ⋆ ∷ τs⋆) = τ-valid-++ τ⋆ ∷ regs-valid-++ τs⋆



Vec-TypeLike⁺ : ∀ A {T : TypeLike A} {{T⁺ : TypeLike⁺ A}} {n} →
                 TypeLike⁺ (Vec A n) {{Vec-TypeLike A n}}
Vec-TypeLike⁺ A {T} {{T⁺}} = typeLike⁺
    (λ Δ xs → Allᵥ-dec (λ x → Δ ⊢? x Valid) xs) xs-valid-++
  where xs-valid-++ : ∀ {n} {Δ Δ' : TypeAssumptions} {xs : Vec A n} →
                        _⊢_Valid {{Vec-TypeLike A n}} Δ xs →
                        _⊢_Valid {{Vec-TypeLike A n}} (Δ ++ Δ') xs
        xs-valid-++ [] = []
        xs-valid-++ (x⋆ ∷ xs⋆) = valid-++ {{T⁺}} x⋆ ∷ xs-valid-++ xs⋆

List-TypeLike⁺ : ∀ A {T : TypeLike A} {{T⁺ : TypeLike⁺ A}} →
                  TypeLike⁺ (List A) {{List-TypeLike A}}
List-TypeLike⁺ A {T} {{T⁺}} = typeLike⁺
    (λ Δ xs → All-dec (λ x → Δ ⊢? x Valid) xs) xs-valid-++
  where xs-valid-++ : ∀ {Δ Δ' : TypeAssumptions} {xs : List A} →
                        _⊢_Valid {{List-TypeLike A}} Δ xs →
                        _⊢_Valid {{List-TypeLike A}} (Δ ++ Δ') xs
        xs-valid-++ [] = []
        xs-valid-++ (x⋆ ∷ xs⋆) = valid-++ {{T⁺}} x⋆ ∷ xs-valid-++ xs⋆

instance
  InitializationFlag-TypeLike⁺ : TypeLike⁺ InitializationFlag
  InitializationFlag-TypeLike⁺ = typeLike⁺ (λ Δ φ → yes tt) id

  Type-TypeLike⁺ : TypeLike⁺ Type
  Type-TypeLike⁺ = typeLike⁺ _⊢?_Type τ-valid-++

  TypeVec-TypeLike⁺ : ∀ {n} → TypeLike⁺ (Vec Type n)
  TypeVec-TypeLike⁺ = Vec-TypeLike⁺ Type

  TypeList-TypeLike⁺ : TypeLike⁺ (List Type)
  TypeList-TypeLike⁺ = List-TypeLike⁺ Type

  InitType-TypeLike⁺ : TypeLike⁺ InitType
  InitType-TypeLike⁺ = typeLike⁺ _⊢?_InitType τ⁻-valid-++

  InitTypeVec-InitTypeLike⁺ : ∀ {n} → TypeLike⁺ (Vec InitType n)
  InitTypeVec-InitTypeLike⁺ = Vec-TypeLike⁺ InitType

  InitTypeList-InitTypeLike⁺ : TypeLike⁺ (List InitType)
  InitTypeList-InitTypeLike⁺ = List-TypeLike⁺ InitType

  StackType-TypeLike⁺ : TypeLike⁺ StackType
  StackType-TypeLike⁺ = typeLike⁺ _⊢?_StackType σ-valid-++

  LabelAssignment-TypeLike⁺ : TypeLike⁺ LabelAssignment
  LabelAssignment-TypeLike⁺ = typeLike⁺ (const ⊢?_LabelAssignment) id

  RegisterAssignment-TypeLike⁺ : TypeLike⁺ RegisterAssignment
  RegisterAssignment-TypeLike⁺ = typeLike⁺ _⊢?_RegisterAssignment Γ-valid-++
