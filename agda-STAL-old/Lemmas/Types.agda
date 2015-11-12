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
      dec-inj₂ valid-∀ (λ { (valid-∀ Δ'⋆ Γ⋆) → Δ'⋆ , Γ⋆ })
        (Δ ⊢? Δ' TypeAssignment) (Δ' ++ Δ ⊢? Γ RegisterAssignment)
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
    Δ ⊢? [] StackType = yes valid-[]
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

    infix 3  _⊢?_TypeAssignment
    _⊢?_TypeAssignment : ∀ Δ₁ Δ₂  → Dec (Δ₁ ⊢ Δ₂ TypeAssignment)
    Δ₁ ⊢? [] TypeAssignment = yes []
    Δ₁ ⊢? a ∷ Δ₂ TypeAssignment with Δ₂ ++ Δ₁ ⊢? a TypeAssignmentValue
                                   | Δ₁ ⊢? Δ₂ TypeAssignment
    ... | yes a⋆ | yes Δ₂⋆ = yes (a⋆ ∷ Δ₂⋆)
    ... | no ¬a⋆ | _  = no (λ { (a⋆ ∷ Δ₂⋆) → ¬a⋆ a⋆ })
    ... | _ | no ¬Δ₂⋆ = no (λ { (a⋆ ∷ Δ₂⋆) → ¬Δ₂⋆ Δ₂⋆ })

    infix 3  _⊢?_TypeAssignmentValue
    _⊢?_TypeAssignmentValue : ∀ Δ₁ a  → Dec (Δ₁ ⊢ a TypeAssignmentValue)
    Δ₁ ⊢? α TypeAssignmentValue = yes valid-α
    Δ₁ ⊢? ρ TypeAssignmentValue = yes valid-ρ

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

    infix 3 _⊢?_Instantiation
    _⊢?_Instantiation : ∀ Δ i → Dec (Δ ⊢ i Instantiation)
    [] ⊢? i Instantiation = no (λ ())
    α ∷ Δ ⊢? α τ Instantiation with Δ ⊢? τ Type
    ... | yes τ⋆ = yes (valid-α τ⋆)
    ... | no ¬τ⋆ = no (λ { (valid-α τ⋆) → ¬τ⋆ τ⋆ })
    ρ ∷ Δ ⊢? α τ Instantiation = no (λ ())
    α ∷ Δ ⊢? ρ σ Instantiation = no (λ ())
    ρ ∷ Δ ⊢? ρ σ Instantiation with Δ ⊢? σ StackType
    ... | yes σ⋆ = yes (valid-ρ σ⋆)
    ... | no ¬σ⋆ = no (λ { (valid-ρ σ⋆) → ¬σ⋆ σ⋆ })

    infix 3 _⊢?_WeakCastValue
    _⊢?_WeakCastValue : ∀ Δ cᵥ → Dec (Δ ⊢ cᵥ WeakCastValue)
    Δ ⊢? inst i WeakCastValue
      with Δ ⊢? i Instantiation
    ... | yes i⋆ = yes (valid-inst i⋆)
    ... | no ¬i⋆ = no (λ { (valid-inst i⋆) → ¬i⋆ i⋆ })
    Δ ⊢? weaken n WeakCastValue = yes valid-weaken

    infix 3 _⊢?_WeakCast
    _⊢?_WeakCast : ∀ Δ c → Dec (Δ ⊢ c WeakCast)
    Δ ⊢? cᵥ / zero WeakCast
      with Δ ⊢? cᵥ WeakCastValue
    ... | yes cᵥ⋆ = yes (valid-zero cᵥ⋆)
    ... | no ¬cᵥ⋆ = no (λ { (valid-zero cᵥ⋆) → ¬cᵥ⋆ cᵥ⋆ })
    [] ⊢? cᵥ / suc ι WeakCast = no (λ ())
    a ∷ Δ ⊢? cᵥ / suc ι WeakCast
      with Δ ⊢? cᵥ / ι WeakCast
    ... | yes cᵥ⋆ = yes (valid-suc cᵥ⋆)
    ... | no ¬cᵥ⋆ = no (λ { (valid-suc cᵥ⋆) → ¬cᵥ⋆ cᵥ⋆ })

    infix 3 _⊢?_StrongCastValue
    _⊢?_StrongCastValue : ∀ Δ cᵥ → Dec (Δ ⊢ cᵥ StrongCastValue)
    Δ ⊢? inst i StrongCastValue
      with Δ ⊢? i Instantiation
    ... | yes i⋆ = yes (valid-inst i⋆)
    ... | no ¬i⋆ = no (λ { (valid-inst i⋆) → ¬i⋆ i⋆ })
    Δ ⊢? weaken Δ⁺ StrongCastValue
      with Δ ⊢? Δ⁺ TypeAssignment
    ... | yes Δ⁺⋆ = yes (valid-weaken Δ⁺⋆)
    ... | no ¬Δ⁺⋆ = no (λ { (valid-weaken Δ⁺⋆) → ¬Δ⁺⋆ Δ⁺⋆ })

    infix 3 _⊢?_StrongCast
    _⊢?_StrongCast : ∀ Δ c → Dec (Δ ⊢ c StrongCast)
    Δ ⊢? cᵥ / zero StrongCast
      with Δ ⊢? cᵥ StrongCastValue
    ... | yes cᵥ⋆ = yes (valid-zero cᵥ⋆)
    ... | no ¬cᵥ⋆ = no (λ { (valid-zero cᵥ⋆) → ¬cᵥ⋆ cᵥ⋆ })
    [] ⊢? cᵥ / suc ι StrongCast = no (λ ())
    a ∷ Δ ⊢? cᵥ / suc ι StrongCast
      with Δ ⊢? cᵥ / ι StrongCast
    ... | yes cᵥ⋆ = yes (valid-suc cᵥ⋆)
    ... | no ¬cᵥ⋆ = no (λ { (valid-suc cᵥ⋆) → ¬cᵥ⋆ cᵥ⋆ })

  mutual
    τ-valid-++ : ∀ {Δ Δ' τ} →
                   Δ ⊢ τ Type →
                   Δ ++ Δ' ⊢ τ Type
    τ-valid-++ (valid-α⁼ l) = valid-α⁼ (↓-add-right _ l)
    τ-valid-++ valid-int = valid-int
    τ-valid-++ valid-ns = valid-ns
    τ-valid-++ {Δ = Δ} {Δ'} (valid-∀ {Δᵥ} {Γ} Δ⋆ Γ⋆) =
      valid-∀ (Δ-valid-++ Δ⋆)
              (subst (λ Δ → Δ ⊢ Γ RegisterAssignment)
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
    σ-valid-++ valid-[] = valid-[]
    σ-valid-++ (τ⋆ ∷ σ⋆) = τ-valid-++ τ⋆ ∷ σ-valid-++ σ⋆

    Δ-valid-++ : ∀ {Δ Δ' Δᵥ} →
                   Δ ⊢ Δᵥ TypeAssignment →
                   Δ ++ Δ' ⊢ Δᵥ TypeAssignment
    Δ-valid-++ [] = []
    Δ-valid-++ {Δ} {Δ'} {a ∷ Δᵥ} (a⋆ ∷ Δᵥ⋆) =
      subst (λ Δ → Δ ⊢ a TypeAssignmentValue)
            (List-++-assoc Δᵥ Δ Δ') (a-valid-++ a⋆)
      ∷ Δ-valid-++ Δᵥ⋆

    a-valid-++ : ∀ {Δ Δ' a} →
                   Δ ⊢ a TypeAssignmentValue →
                   Δ ++ Δ' ⊢ a TypeAssignmentValue
    a-valid-++ valid-α = valid-α
    a-valid-++ valid-ρ = valid-ρ

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

    i-valid-++ : ∀ {Δ Δ' i} →
                   Δ ⊢ i Instantiation →
                   Δ ++ Δ' ⊢ i Instantiation
    i-valid-++ (valid-α τ⋆) = valid-α (τ-valid-++ τ⋆)
    i-valid-++ (valid-ρ σ⋆) = valid-ρ (σ-valid-++ σ⋆)

    cᵥw-valid-++ : ∀ {Δ Δ' cᵥ} →
                     Δ ⊢ cᵥ WeakCastValue →
                     Δ ++ Δ' ⊢ cᵥ WeakCastValue
    cᵥw-valid-++ (valid-inst i⋆) = valid-inst (i-valid-++ i⋆)
    cᵥw-valid-++ valid-weaken = valid-weaken

    cw-valid-++ : ∀ {Δ Δ' c} →
                    Δ ⊢ c WeakCast →
                    Δ ++ Δ' ⊢ c WeakCast
    cw-valid-++ (valid-zero cᵥ⋆) = valid-zero (cᵥw-valid-++ cᵥ⋆)
    cw-valid-++ (valid-suc c⋆) = valid-suc (cw-valid-++ c⋆)

    cᵥ-valid-++ : ∀ {Δ Δ' cᵥ} →
                   Δ ⊢ cᵥ StrongCastValue →
                   Δ ++ Δ' ⊢ cᵥ StrongCastValue
    cᵥ-valid-++ (valid-inst i⋆) = valid-inst (i-valid-++ i⋆)
    cᵥ-valid-++ (valid-weaken Δ⁺⋆) = valid-weaken (Δ-valid-++ Δ⁺⋆)

    c-valid-++ : ∀ {Δ Δ' c} →
                  Δ ⊢ c StrongCast →
                  Δ ++ Δ' ⊢ c StrongCast
    c-valid-++ (valid-zero cᵥ⋆) = valid-zero (cᵥ-valid-++ cᵥ⋆)
    c-valid-++ (valid-suc c⋆) = valid-suc (c-valid-++ c⋆)

Vec-TypeLike⁺ : ∀ A {T : TypeLike A} {{T⁺ : TypeLike⁺ A}} {m} →
                 TypeLike⁺ (Vec A m) {{Vec-TypeLike A m}}
Vec-TypeLike⁺ A = typeLike⁺
    (λ Δ xs → Allᵥ-dec (λ x → Δ ⊢? x Valid) xs)
    xs-valid-++
  where xs-valid-++ : ∀ {Δ Δ' m} {xs : Vec A m} →
                        Allᵥ (λ v → Δ ⊢ v Valid) xs →
                        Allᵥ (λ v → Δ ++ Δ' ⊢ v Valid) xs
        xs-valid-++ [] = []
        xs-valid-++ (x⋆ ∷ xs⋆) = valid-++ x⋆ ∷ xs-valid-++ xs⋆

List-TypeLike⁺ : ∀ A {T : TypeLike A} {{T⁺ : TypeLike⁺ A}} →
                  TypeLike⁺ (List A) {{List-TypeLike A}}
List-TypeLike⁺ A = typeLike⁺
    (λ Δ xs → All-dec (λ x → Δ ⊢? x Valid) xs)
    xs-valid-++
  where xs-valid-++ : ∀ {Δ Δ'} {xs : List A} →
                        All (λ v → Δ ⊢ v Valid) xs →
                        All (λ v → Δ ++ Δ' ⊢ v Valid) xs
        xs-valid-++ [] = []
        xs-valid-++ (x⋆ ∷ xs⋆) = valid-++ x⋆ ∷ xs-valid-++ xs⋆

instance
  InitializationFlag-TypeLike⁺ : TypeLike⁺ InitializationFlag
  InitializationFlag-TypeLike⁺ = typeLike⁺ (λ Δ φ → yes tt) id

  Type-TypeLike⁺ : TypeLike⁺ Type
  Type-TypeLike⁺ = typeLike⁺ _⊢?_Type τ-valid-++

  TypeVec-TypeLike⁺ : ∀ {m} → TypeLike⁺ (Vec Type m)
  TypeVec-TypeLike⁺ = Vec-TypeLike⁺ Type

  TypeList-TypeLike⁺ : TypeLike⁺ (List Type)
  TypeList-TypeLike⁺ = List-TypeLike⁺ Type

  InitType-TypeLike⁺ : TypeLike⁺ InitType
  InitType-TypeLike⁺ = typeLike⁺ _⊢?_InitType τ⁻-valid-++

  InitTypeVec-InitTypeLike⁺ : ∀ {m} → TypeLike⁺ (Vec InitType m)
  InitTypeVec-InitTypeLike⁺ = Vec-TypeLike⁺ InitType

  InitTypeList-InitTypeLike⁺ : TypeLike⁺ (List InitType)
  InitTypeList-InitTypeLike⁺ = List-TypeLike⁺ InitType

  StackType-TypeLike⁺ : TypeLike⁺ StackType
  StackType-TypeLike⁺ = typeLike⁺ _⊢?_StackType σ-valid-++

  LabelAssignment-TypeLike⁺ : TypeLike⁺ LabelAssignment
  LabelAssignment-TypeLike⁺ = typeLike⁺ (const ⊢?_LabelAssignment) id

  TypeAssignment-TypeLike⁺ : TypeLike⁺ TypeAssignment
  TypeAssignment-TypeLike⁺ = typeLike⁺ _⊢?_TypeAssignment Δ-valid-++

  TypeAssignmentValue-TypeLike⁺ : TypeLike⁺ TypeAssignmentValue
  TypeAssignmentValue-TypeLike⁺ = typeLike⁺ _⊢?_TypeAssignmentValue a-valid-++

  RegisterAssignment-TypeLike⁺ : TypeLike⁺ RegisterAssignment
  RegisterAssignment-TypeLike⁺ = typeLike⁺ _⊢?_RegisterAssignment Γ-valid-++

  Instantiation-TypeLike⁺ : TypeLike⁺ Instantiation
  Instantiation-TypeLike⁺ = typeLike⁺ _⊢?_Instantiation i-valid-++

  WeakCastValue-TypeLike⁺ : TypeLike⁺ WeakCastValue
  WeakCastValue-TypeLike⁺ = typeLike⁺ _⊢?_WeakCastValue cᵥw-valid-++

  WeakCast-TypeLike⁺ : TypeLike⁺ WeakCast
  WeakCast-TypeLike⁺ = typeLike⁺ _⊢?_WeakCast cw-valid-++

  StrongCastValue-TypeLike⁺ : TypeLike⁺ StrongCastValue
  StrongCastValue-TypeLike⁺ = typeLike⁺ _⊢?_StrongCastValue cᵥ-valid-++

  StrongCast-TypeLike⁺ : TypeLike⁺ StrongCast
  StrongCast-TypeLike⁺ = typeLike⁺ _⊢?_StrongCast c-valid-++
