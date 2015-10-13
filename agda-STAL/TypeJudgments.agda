open import Util
open import Grammar
open import GrammarEq
open import Substitution

mutual
  infix 4 _⊢_Type
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
         ∀ {m} {τs : Vec InitType m} →
      Allᵥ (λ τ⁻ → Δ ⊢ τ⁻ InitType) τs →
      ---------------------------------
             Δ ⊢ tuple τs Type

  infix 4 _⊢_InitType
  data _⊢_InitType (Δ : TypeAssignment) : InitType → Set where
    valid-τ⁻ :
             ∀ {τ φ} →
            Δ ⊢ τ Type →
        --------------------
        Δ ⊢ τ , φ InitType

  infix 4  _⊢_StackType
  data _⊢_StackType (Δ : TypeAssignment) : StackType → Set where
    valid-ρ⁼ :
         ∀ {ι} →
       Δ ↓ ι ⇒ ρ →
      -------------
      Δ ⊢ ρ⁼ ι StackType

    valid-nil :
      -----------------
      Δ ⊢ nil StackType

    valid-∷ :
          ∀ {τ σ} →
         Δ ⊢ τ Type →
       Δ ⊢ σ StackType →
      -------------------
      Δ ⊢ τ ∷ σ StackType

  infix 4 ⊢_GlobalLabelAssignment
  data ⊢_GlobalLabelAssignment : GlobalLabelAssignment → Set where
    valid-G :
                ∀ {G} →
      All (λ τ → [] ⊢ τ Type) G →
      ---------------------------
       ⊢ G GlobalLabelAssignment

  infix 4 ⊢_HeapLabelAssignment
  data ⊢_HeapLabelAssignment : HeapLabelAssignment → Set where
    valid-H :
                ∀ {H} →
      All (λ τ → [] ⊢ τ Type) H →
      ---------------------------
        ⊢ H HeapLabelAssignment

  infix 4 ⊢_LabelAssignment
  ⊢_LabelAssignment : LabelAssignment → Set
  ⊢ ψ₁ , ψ₂ LabelAssignment =
    (⊢ ψ₁ GlobalLabelAssignment) × (⊢ ψ₂ HeapLabelAssignment)

  infix 4  _⊢_TypeAssignment
  data _⊢_TypeAssignment : TypeAssignment → TypeAssignment → Set where
    valid-[] :
             ∀ {Δ} →
      ---------------------
      Δ ⊢ [] TypeAssignment

    valid-∷ :
              ∀ {a Δ₁ Δ₂} →
       Δ₂ ++ Δ₁ ⊢ a TypeAssignmentValue →
         Δ₁ ⊢ Δ₂ TypeAssignment →
      -----------------------------------
           Δ₁ ⊢ a ∷ Δ₂ TypeAssignment

  infix 4  _⊢_TypeAssignmentValue
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

  infix 4 _⊢_RegisterAssignment
  record _⊢_RegisterAssignment
         (Δ : TypeAssignment) (Γ : RegisterAssignment) : Set where
    inductive
    constructor valid-registerₐ
    field
      valid-sp : Δ ⊢ stack-type Γ StackType
      valid-regs : Allᵥ (λ τ → Δ ⊢ τ Type) (reg-types Γ)

  infix 4 _⊢_Instantiation
  data _⊢_Instantiation : TypeAssignment → Instantiation → Set where
    valid-α :
      ∀ {Δ τ} →
      Δ ⊢ τ Type →
      α ∷ Δ ⊢ α τ Instantiation

    valid-ρ :
      ∀ {Δ σ} →
      Δ ⊢ σ StackType →
      ρ ∷ Δ ⊢ ρ σ Instantiation

  infix 4 _⊢_WeakCastValue
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

  infix 4 _⊢_WeakCast
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

private
  mutual
    infix 4 _⊢?_Type
    _⊢?_Type : ∀ Δ τ → Dec (Δ ⊢ τ Type)
    Δ ⊢? α⁼ ι Type = dec-inj valid-α⁼ (λ { (valid-α⁼ l) → l }) (↓-decᵥ Δ ι α)
    Δ ⊢? int Type = yes valid-int
    Δ ⊢? ns Type = yes valid-ns
    Δ ⊢? ∀[ Δ' ] Γ Type =
      dec-inj₂ valid-∀ (λ { (valid-∀ Δ'⋆ Γ⋆) → Δ'⋆ , Γ⋆ })
        (Δ ⊢? Δ' TypeAssignment) (Δ' ++ Δ ⊢? Γ RegisterAssignment)
    Δ ⊢? tuple τs Type =
      dec-inj valid-tuple (λ { (valid-tuple τs⋆) → τs⋆ }) (Δ ⊢? τs InitTypes)

    infix 4 _⊢?_InitType
    _⊢?_InitType : ∀ Δ τ⁻ → Dec (Δ ⊢ τ⁻ InitType)
    Δ ⊢? τ , φ InitType =
      dec-inj valid-τ⁻ (λ { (valid-τ⁻ τ⋆) → τ⋆ }) (Δ ⊢? τ Type)

    infix 4 _⊢?_InitTypes
    _⊢?_InitTypes : ∀ Δ {m} (τs : Vec InitType m) →
                      Dec (Allᵥ (λ τ⁻ → Δ ⊢ τ⁻ InitType) τs)
    Δ ⊢? [] InitTypes = yes []
    Δ ⊢? τ ∷ τs InitTypes with Δ ⊢? τ InitType | Δ ⊢? τs InitTypes
    ... | yes τ⋆ | yes τs⋆ = yes (τ⋆ ∷ τs⋆)
    ... | no ¬τ⋆ | _  = no (λ { (τ⋆ ∷ τs⋆) → ¬τ⋆ τ⋆ })
    ... | _ | no ¬τs⋆ = no (λ { (τ⋆ ∷ τs⋆) → ¬τs⋆ τs⋆ })

    infix 4  _⊢?_StackType
    _⊢?_StackType : ∀ Δ σ → Dec (Δ ⊢ σ StackType)
    Δ ⊢? ρ⁼ ι StackType =
      dec-inj valid-ρ⁼ (λ { (valid-ρ⁼ l) → l }) (↓-decᵥ Δ ι ρ)
    Δ ⊢? nil StackType = yes valid-nil
    Δ ⊢? τ ∷ σ StackType with Δ ⊢? τ Type | Δ ⊢? σ StackType
    ... | yes τ⋆ | yes σ⋆ = yes (valid-∷ τ⋆ σ⋆)
    ... | no ¬τ⋆ | _  = no (λ { (valid-∷ τ⋆ σ⋆) → ¬τ⋆ τ⋆ })
    ... | _ | no ¬σ⋆ = no (λ { (valid-∷ τ⋆ σ⋆) → ¬σ⋆ σ⋆ })

    infix 4 _⊢?_Types
    _⊢?_Types : ∀ Δ (τs : List Type) → Dec (All (λ τ → Δ ⊢ τ Type) τs)
    Δ ⊢? [] Types = yes []
    Δ ⊢? τ ∷ τs Types with Δ ⊢? τ Type | Δ ⊢? τs Types
    ... | yes τ⋆ | yes τs⋆ = yes (τ⋆ ∷ τs⋆)
    ... | no ¬τ⋆ | _  = no (λ { (τ⋆ ∷ τs⋆) → ¬τ⋆ τ⋆ })
    ... | _ | no ¬τs⋆ = no (λ { (τ⋆ ∷ τs⋆) → ¬τs⋆ τs⋆ })

    infix 4 ⊢?_GlobalLabelAssignment
    ⊢?_GlobalLabelAssignment : ∀ ψ₁ → Dec (⊢ ψ₁ GlobalLabelAssignment)
    ⊢? ψ₁ GlobalLabelAssignment =
      dec-inj valid-G (λ { (valid-G τs⋆) → τs⋆ }) ([] ⊢? ψ₁ Types)

    infix 4 ⊢?_HeapLabelAssignment
    ⊢?_HeapLabelAssignment : ∀ ψ₂ → Dec (⊢ ψ₂ HeapLabelAssignment)
    ⊢? ψ₂ HeapLabelAssignment =
      dec-inj valid-H (λ { (valid-H τs⋆) → τs⋆ }) ([] ⊢? ψ₂ Types)

    infix 4 ⊢?_LabelAssignment
    ⊢?_LabelAssignment : ∀ ψ → Dec (⊢ ψ LabelAssignment)
    ⊢? ψ₁ , ψ₂ LabelAssignment =
      dec-inj₂ _,_
               id
               (⊢? ψ₁ GlobalLabelAssignment)
               (⊢? ψ₂ HeapLabelAssignment)

    infix 4  _⊢?_TypeAssignment
    _⊢?_TypeAssignment : ∀ Δ₁ Δ₂  → Dec (Δ₁ ⊢ Δ₂ TypeAssignment)
    Δ₁ ⊢? [] TypeAssignment = yes valid-[]
    Δ₁ ⊢? a ∷ Δ₂ TypeAssignment with Δ₂ ++ Δ₁ ⊢? a TypeAssignmentValue
                                   | Δ₁ ⊢? Δ₂ TypeAssignment
    ... | yes a⋆ | yes Δ₂⋆ = yes (valid-∷ a⋆ Δ₂⋆)
    ... | no ¬a⋆ | _  = no (λ { (valid-∷ a⋆ Δ₂⋆) → ¬a⋆ a⋆ })
    ... | _ | no ¬Δ₂⋆ = no (λ { (valid-∷ a⋆ Δ₂⋆) → ¬Δ₂⋆ Δ₂⋆ })

    infix 4  _⊢?_TypeAssignmentValue
    _⊢?_TypeAssignmentValue : ∀ Δ₁ a  → Dec (Δ₁ ⊢ a TypeAssignmentValue)
    Δ₁ ⊢? α TypeAssignmentValue = yes valid-α
    Δ₁ ⊢? ρ TypeAssignmentValue = yes valid-ρ

    infix 4 _⊢?_RegisterAssignment
    _⊢?_RegisterAssignment : ∀ Δ Γ → Dec (Δ ⊢ Γ RegisterAssignment)
    Δ ⊢? registerₐ sp regs RegisterAssignment =
      dec-inj₂ valid-registerₐ
               (λ { (valid-registerₐ sp⋆ regs⋆) → sp⋆ , regs⋆ })
               (Δ ⊢? sp StackType)
               (Δ ⊢? regs RegTypes)

    infix 4 _⊢?_RegTypes
    _⊢?_RegTypes : ∀ Δ {m} (τs : Vec Type m) →
                     Dec (Allᵥ (λ τ → Δ ⊢ τ Type) τs)
    Δ ⊢? [] RegTypes = yes []
    Δ ⊢? τ ∷ τs RegTypes with Δ ⊢? τ Type | Δ ⊢? τs RegTypes
    ... | yes τ⋆ | yes τs⋆ = yes (τ⋆ ∷ τs⋆)
    ... | no ¬τ⋆ | _  = no (λ { (τ⋆ ∷ τs⋆) → ¬τ⋆ τ⋆ })
    ... | _ | no ¬τs⋆ = no (λ { (τ⋆ ∷ τs⋆) → ¬τs⋆ τs⋆ })

    infix 4 _⊢?_Instantiation
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

    infix 4 _⊢?_WeakCastValue
    _⊢?_WeakCastValue : ∀ Δ cᵥ → Dec (Δ ⊢ cᵥ WeakCastValue)
    Δ ⊢? inst i WeakCastValue =
      dec-inj valid-inst (λ { (valid-inst i⋆) → i⋆ }) (Δ ⊢? i Instantiation)
    Δ ⊢? weaken x WeakCastValue = yes valid-weaken

    infix 4 _⊢?_WeakCast
    _⊢?_WeakCast : ∀ Δ c → Dec (Δ ⊢ c WeakCast)
    Δ ⊢? cᵥ / zero WeakCast = dec-inj (valid-zero {Δ})
                                      (λ { (valid-zero cᵥ⋆) → cᵥ⋆ })
                                      (Δ ⊢? cᵥ WeakCastValue)
    [] ⊢? cᵥ / suc ι WeakCast = no (λ ())
    a ∷ Δ ⊢? cᵥ / suc ι WeakCast = dec-inj valid-suc
                                           (λ { (valid-suc c⋆) → c⋆ })
                                           (Δ ⊢? cᵥ / ι WeakCast)

record TypeLike (A Ctx : Set) : Set1 where
  constructor typeLike
  field
    _⊢_Valid : Ctx → A → Set
    _⊢?_Valid : ∀ C v → Dec (C ⊢ v Valid)
  infix 4 _⊢_Valid _⊢?_Valid
open TypeLike {{...}} public

Vec-typeLike : ∀ {A Ctx : Set} {{_ : TypeLike A Ctx}} {m} →
                 TypeLike (Vec A m) Ctx
Vec-typeLike {{r}} = typeLike
  (λ C xs → Allᵥ (λ x → C ⊢ x Valid) xs)
  (λ C xs → Allᵥ-dec (λ x → C ⊢? x Valid) xs)

List-typeLike : ∀ {A Ctx : Set} {{_ : TypeLike A Ctx}} →
                  TypeLike (List A) Ctx
List-typeLike {{r}} = typeLike
  (λ C xs → All (λ x → C ⊢ x Valid) xs)
  (λ C xs → All-dec (λ x → C ⊢? x Valid) xs)

instance
  Type-typeLike : TypeLike Type TypeAssignment
  Type-typeLike = typeLike _⊢_Type _⊢?_Type

  Typevec-typeLike : ∀ {m} → TypeLike (Vec Type m) TypeAssignment
  Typevec-typeLike = Vec-typeLike

  Typelist-typeLike : TypeLike (List Type) TypeAssignment
  Typelist-typeLike = List-typeLike

  InitType-typeLike : TypeLike InitType TypeAssignment
  InitType-typeLike = typeLike _⊢_InitType _⊢?_InitType

  InitTypevec-typeLike : ∀ {m} → TypeLike (Vec InitType m) TypeAssignment
  InitTypevec-typeLike = Vec-typeLike

  InitTypelist-typeLike : TypeLike (List InitType) TypeAssignment
  InitTypelist-typeLike = List-typeLike

  StackType-typeLike : TypeLike StackType TypeAssignment
  StackType-typeLike = typeLike _⊢_StackType _⊢?_StackType

  LabelAssignment-typeLike : TypeLike LabelAssignment ⊤
  LabelAssignment-typeLike = typeLike (λ _ ψ → ⊢ ψ LabelAssignment)
                                (λ _ ψ → ⊢? ψ LabelAssignment)

  TypeAssignment-typeLike : TypeLike TypeAssignment TypeAssignment
  TypeAssignment-typeLike = typeLike _⊢_TypeAssignment
                                     _⊢?_TypeAssignment

  TypeAssignmentValue-typeLike : TypeLike TypeAssignmentValue TypeAssignment
  TypeAssignmentValue-typeLike = typeLike _⊢_TypeAssignmentValue
                                          _⊢?_TypeAssignmentValue

  RegisterAssignment-typeLike : TypeLike RegisterAssignment TypeAssignment
  RegisterAssignment-typeLike =
    typeLike _⊢_RegisterAssignment _⊢?_RegisterAssignment

  Instantiation-typeLike : TypeLike Instantiation TypeAssignment
  Instantiation-typeLike = typeLike _⊢_Instantiation _⊢?_Instantiation

  WeakCastValue-typeLike : TypeLike WeakCastValue TypeAssignment
  WeakCastValue-typeLike = typeLike _⊢_WeakCastValue _⊢?_WeakCastValue

  WeakCast-typeLike : TypeLike WeakCast TypeAssignment
  WeakCast-typeLike = typeLike _⊢_WeakCast _⊢?_WeakCast

  StrongCastValue-typeLike : TypeLike StrongCastValue TypeAssignment
  StrongCastValue-typeLike = typeLike
    (λ Δ cᵥ → Δ ⊢ Strong→WeakCastValue cᵥ WeakCastValue)
    (λ Δ cᵥ → Δ ⊢? Strong→WeakCastValue cᵥ WeakCastValue)

  StrongCast-typeLike : TypeLike StrongCast TypeAssignment
  StrongCast-typeLike = typeLike
    (λ Δ c → Δ ⊢ Strong→WeakCast c WeakCast)
    (λ Δ c → Δ ⊢? Strong→WeakCast c WeakCast)
