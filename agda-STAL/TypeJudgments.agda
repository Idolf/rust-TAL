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
           ⊢ Δ' TypeAssignment →
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

  infix 4 ⊢_LabelAssignment
  data ⊢_LabelAssignment : LabelAssignment → Set where
    valid-ψ :
              ∀ {ψ} →
      All (λ τ → [] ⊢ τ Type) ψ →
      ---------------------------
         ⊢ ψ LabelAssignment

  infix 4  ⊢_TypeAssignment
  data ⊢_TypeAssignment : TypeAssignment → Set where
    valid-[] :
      ⊢ [] TypeAssignment

    valid-∷ :
             ∀ {a Δ} →
       ⊢ Δ TypeAssignment →
      ----------------------
      ⊢ a ∷ Δ TypeAssignment

  infix 4 _⊢_RegisterAssignment
  record _⊢_RegisterAssignment
         (Δ : TypeAssignment) (Γ : RegisterAssignment) : Set where
    inductive
    constructor valid-registerₐ
    field
      valid-sp : Δ ⊢ stack-type Γ StackType
      valid-regs : Allᵥ (λ τ → Δ ⊢ τ Type) (reg-types Γ)

  infix 4 _⊢_Cast
  data _⊢_Cast : TypeAssignment → Cast → Set where
    valid-α-zero :
             ∀ {Δ τ} →
            Δ ⊢ τ Type →
      ----------------------------
      α ∷ Δ ⊢ inst α τ / zero Cast

    valid-ρ :
              ∀ {Δ σ} →
           Δ ⊢ σ StackType →
      ----------------------------
      ρ ∷ Δ ⊢ inst ρ σ / zero Cast

    valid-weaken-zero :
            ∀ {Δ a} →
      ------------------------
      Δ ⊢ weaken a / zero Cast

    valid-suc :
          ∀ {Δ a cᵥ ι} →
         Δ ⊢ cᵥ / ι Cast →
      -----------------------
      a ∷ Δ ⊢ cᵥ / suc ι Cast

private
  mutual
    infix 4 _⊢?_Type
    _⊢?_Type : ∀ Δ τ → Dec (Δ ⊢ τ Type)
    Δ ⊢? α⁼ ι Type with ↓-decᵥ Δ ι α
    ... | yes l = yes (valid-α⁼ l)
    ... | no ¬l = no (λ { (valid-α⁼ l) → ¬l l })
    Δ ⊢? int Type = yes valid-int
    Δ ⊢? ns Type = yes valid-ns
    Δ ⊢? ∀[ Δ' ] Γ Type =
      dec-inj₂ valid-∀ (λ { (valid-∀ Δ'⋆ Γ⋆) → Δ'⋆ , Γ⋆ })
        (⊢? Δ' TypeAssignment) (Δ' ++ Δ ⊢? Γ RegisterAssignment)
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
    Δ ⊢? ρ⁼ ι StackType with ↓-decᵥ Δ ι ρ
    ... | yes l = yes (valid-ρ⁼ l)
    ... | no ¬l = no (λ { (valid-ρ⁼ l) → ¬l l })
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

    infix 4 ⊢?_LabelAssignment
    ⊢?_LabelAssignment : ∀ ψ → Dec (⊢ ψ LabelAssignment)
    ⊢? ψ LabelAssignment =
      dec-inj valid-ψ (λ { (valid-ψ ψ⋆) → ψ⋆ }) ([] ⊢? ψ Types)

    infix 4  ⊢?_TypeAssignment
    ⊢?_TypeAssignment : ∀ Δ → Dec (⊢ Δ TypeAssignment)
    ⊢? [] TypeAssignment = yes valid-[]
    ⊢? a ∷ Δ TypeAssignment with ⊢? Δ TypeAssignment
    ... | yes ⋆Δ = yes (valid-∷ ⋆Δ)
    ... | no ¬⋆Δ = no (λ { (valid-∷ Δ⋆) → ¬⋆Δ Δ⋆ })

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

    infix 4 _⊢?_Cast
    _⊢?_Cast : ∀ Δ c → Dec (Δ ⊢ c Cast)
    [] ⊢? inst a i / zero Cast = no (λ ())
    [] ⊢? weaken n / zero Cast = yes valid-weaken-zero
    α ∷ Δ ⊢? inst α τ / zero Cast with Δ ⊢? τ Type
    α ∷ Δ ⊢? inst α τ / zero Cast | yes τ⋆ = yes (valid-α-zero τ⋆)
    α ∷ Δ ⊢? inst α τ / zero Cast | no ¬τ⋆ = no (λ { (valid-α-zero τ⋆) → ¬τ⋆ τ⋆ })
    α ∷ Δ ⊢? inst ρ σ / zero Cast = no (λ ())
    ρ ∷ Δ ⊢? inst α τ / zero Cast = no (λ ())
    ρ ∷ Δ ⊢? inst ρ σ / zero Cast with Δ ⊢? σ StackType
    ρ ∷ Δ ⊢? inst ρ σ / zero Cast | yes σ⋆ = yes (valid-ρ σ⋆)
    ρ ∷ Δ ⊢? inst ρ σ / zero Cast | no ¬σ⋆ = no (λ { (valid-ρ σ⋆) → ¬σ⋆ σ⋆ })
    a ∷ Δ ⊢? weaken n / zero Cast = yes valid-weaken-zero
    [] ⊢? cᵥ / suc ι Cast = no (λ ())
    a ∷ Δ ⊢? cᵥ / suc ι Cast with Δ ⊢? cᵥ / ι Cast
    a ∷ Δ ⊢? cᵥ / suc ι Cast | yes c⋆ = yes (valid-suc c⋆)
    a ∷ Δ ⊢? cᵥ / suc ι Cast | no ¬c⋆ = no (λ { (valid-suc c⋆) → ¬c⋆ c⋆ })

record TypeLike (A Ctx : Set) : Set1 where
  constructor typeLike
  field
    _⊢_Valid : Ctx → A → Set
    _⊢?_Valid : ∀ C v → Dec (C ⊢ v Valid)

-- These two should do the same, but they do not
-- open TypeLike {{...}} public
infix 4 _⊢_Valid ∙⊢_Valid _⊢?_Valid ∙⊢?_Valid
_⊢_Valid : ∀ {A Ctx : Set} {{_ : TypeLike A Ctx}} →
             Ctx → A → Set
_⊢_Valid {{r}} = TypeLike._⊢_Valid r
∙⊢_Valid : ∀ {A : Set} {{_ : TypeLike A ⊤}} →
             A → Set
∙⊢_Valid {{r}} = TypeLike._⊢_Valid r tt
_⊢?_Valid : ∀ {A Ctx : Set} {{_ : TypeLike A Ctx}} →
              ∀ C v → Dec (C ⊢ v Valid)
_⊢?_Valid {{r}} = TypeLike._⊢?_Valid r
∙⊢?_Valid : ∀ {A : Set} {{_ : TypeLike A ⊤}} →
              ∀ v → Dec (tt ⊢ v Valid)
∙⊢?_Valid {{r}} = TypeLike._⊢?_Valid r tt

instance
  Type-typeLike : TypeLike Type TypeAssignment
  Type-typeLike = typeLike _⊢_Type _⊢?_Type

  InitType-typeLike : TypeLike InitType TypeAssignment
  InitType-typeLike = typeLike _⊢_InitType _⊢?_InitType

  StackType-typeLike : TypeLike StackType TypeAssignment
  StackType-typeLike = typeLike _⊢_StackType _⊢?_StackType

  LabelAssignment-typeLike : TypeLike LabelAssignment ⊤
  LabelAssignment-typeLike = typeLike (λ _ ψ → ⊢ ψ LabelAssignment)
                                (λ _ ψ → ⊢? ψ LabelAssignment)

  TypeAssignment-typeLike : TypeLike TypeAssignment ⊤
  TypeAssignment-typeLike = typeLike (λ _ Δ → ⊢ Δ TypeAssignment)
                               (λ _ Δ → ⊢? Δ TypeAssignment)

  RegisterAssignment-typeLike : TypeLike RegisterAssignment TypeAssignment
  RegisterAssignment-typeLike =
    typeLike _⊢_RegisterAssignment _⊢?_RegisterAssignment

  Cast-typeLike : TypeLike Cast TypeAssignment
  Cast-typeLike = typeLike _⊢_Cast _⊢?_Cast

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
