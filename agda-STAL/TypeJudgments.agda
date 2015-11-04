module TypeJudgments where

open import Util
open import Grammar
open import GrammarEq
open import Substitution

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
        --------------------
        Δ ⊢ τ , φ InitType

  infix 3  _⊢_StackType
  data _⊢_StackType (Δ : TypeAssignment) : StackType → Set where
    valid-ρ⁼ :
         ∀ {ι} →
       Δ ↓ ι ⇒ ρ →
      -------------
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
      -----------------------------------
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
  record _⊢_RegisterAssignment
         (Δ : TypeAssignment) (Γ : RegisterAssignment) : Set where
    inductive
    constructor valid-registerₐ
    field
      valid-sp : Δ ⊢ stack-type Γ StackType
      valid-regs : Allᵥ (λ τ → Δ ⊢ τ Type) (reg-types Γ)

  infix 3 _⊢_Instantiation
  data _⊢_Instantiation : TypeAssignment → Instantiation → Set where
    valid-α :
      ∀ {Δ τ} →
      Δ ⊢ τ Type →
      α ∷ Δ ⊢ α τ Instantiation

    valid-ρ :
      ∀ {Δ σ} →
      Δ ⊢ σ StackType →
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
      --------------------------
      Δ ⊢ weaken Δ⁺ StrongCastValue

    valid-inst :
             ∀ {Δ i} →
        Δ ⊢ i Instantiation →
      ------------------------
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

record TypeLike (A : Set) : Set1 where
  constructor typeLike
  field
    _⊢_Valid : TypeAssignment → A → Set
    _⊢?_Valid : ∀ Δ v → Dec (Δ ⊢ v Valid)
    valid-++ : ∀ {Δ Δ' v} → Δ ⊢ v Valid → Δ ++ Δ' ⊢ v Valid
  infix 3 _⊢_Valid _⊢?_Valid
open TypeLike {{...}} public

Vec-typeLike : ∀ {A} {{_ : TypeLike A}} {m} →
                 TypeLike (Vec A m)
Vec-typeLike {A} = typeLike
    (λ Δ xs → Allᵥ (λ x → Δ ⊢ x Valid) xs)
    (λ Δ xs → Allᵥ-dec (λ x → Δ ⊢? x Valid) xs)
    xs-valid-++
  where xs-valid-++ : ∀ {Δ Δ' m} {xs : Vec A m} →
                        Allᵥ (λ v → Δ ⊢ v Valid) xs →
                        Allᵥ (λ v → Δ ++ Δ' ⊢ v Valid) xs
        xs-valid-++ [] = []
        xs-valid-++ (x⋆ ∷ xs⋆) = valid-++ x⋆ ∷ xs-valid-++ xs⋆


List-typeLike : ∀ {A} {{_ : TypeLike A}} →
                  TypeLike (List A)
List-typeLike {A} = typeLike
    (λ Δ xs → All (λ x → Δ ⊢ x Valid) xs)
    (λ Δ xs → All-dec (λ x → Δ ⊢? x Valid) xs)
    xs-valid-++
  where xs-valid-++ : ∀ {Δ Δ'} {xs : List A} →
                        All (λ v → Δ ⊢ v Valid) xs →
                        All (λ v → Δ ++ Δ' ⊢ v Valid) xs
        xs-valid-++ [] = []
        xs-valid-++ (x⋆ ∷ xs⋆) = valid-++ x⋆ ∷ xs-valid-++ xs⋆


instance
  InitializationFlag-typeLike : TypeLike InitializationFlag
  InitializationFlag-typeLike = typeLike (λ Δ φ → ⊤) (λ Δ φ → yes tt) id

  Type-typeLike : TypeLike Type
  Type-typeLike = typeLike _⊢_Type _⊢?_Type τ-valid-++

  TypeVec-typeLike : ∀ {m} → TypeLike (Vec Type m)
  TypeVec-typeLike = Vec-typeLike

  TypeList-typeLike : TypeLike (List Type)
  TypeList-typeLike = List-typeLike

  InitType-typeLike : TypeLike InitType
  InitType-typeLike = typeLike _⊢_InitType _⊢?_InitType τ⁻-valid-++

  InitTypeVec-typeLike : ∀ {m} → TypeLike (Vec InitType m)
  InitTypeVec-typeLike = Vec-typeLike

  InitTypeList-typeLike : TypeLike (List InitType)
  InitTypeList-typeLike = List-typeLike

  StackType-typeLike : TypeLike StackType
  StackType-typeLike = typeLike _⊢_StackType _⊢?_StackType σ-valid-++

  LabelAssignment-typeLike : TypeLike LabelAssignment
  LabelAssignment-typeLike = typeLike (const ⊢_LabelAssignment)
                                      (const ⊢?_LabelAssignment)
                                      id

  TypeAssignment-typeLike : TypeLike TypeAssignment
  TypeAssignment-typeLike = typeLike _⊢_TypeAssignment
                                     _⊢?_TypeAssignment
                                     Δ-valid-++

  TypeAssignmentValue-typeLike : TypeLike TypeAssignmentValue
  TypeAssignmentValue-typeLike = typeLike _⊢_TypeAssignmentValue
                                          _⊢?_TypeAssignmentValue
                                          a-valid-++

  RegisterAssignment-typeLike : TypeLike RegisterAssignment
  RegisterAssignment-typeLike =
    typeLike _⊢_RegisterAssignment _⊢?_RegisterAssignment Γ-valid-++

  Instantiation-typeLike : TypeLike Instantiation
  Instantiation-typeLike = typeLike _⊢_Instantiation _⊢?_Instantiation i-valid-++

  WeakCastValue-typeLike : TypeLike WeakCastValue
  WeakCastValue-typeLike = typeLike _⊢_WeakCastValue _⊢?_WeakCastValue cᵥw-valid-++

  WeakCast-typeLike : TypeLike WeakCast
  WeakCast-typeLike = typeLike _⊢_WeakCast _⊢?_WeakCast cw-valid-++

  StrongCastValue-typeLike : TypeLike StrongCastValue
  StrongCastValue-typeLike = typeLike _⊢_StrongCastValue _⊢?_StrongCastValue cᵥ-valid-++

  StrongCast-typeLike : TypeLike StrongCast
  StrongCast-typeLike = typeLike _⊢_StrongCast _⊢?_StrongCast c-valid-++

c-valid-add-left : ∀ Δ₁ {Δ₂ ι} {cᵥ : StrongCastValue} →
                    Δ₂ ⊢ cᵥ / ι Valid →
                    Δ₁ ++ Δ₂ ⊢ cᵥ / length Δ₁ + ι Valid
c-valid-add-left [] c⋆ = c⋆
c-valid-add-left (a ∷ Δ₁) c⋆ = valid-suc (c-valid-add-left Δ₁ c⋆)

c-valid-remove-left : ∀ Δ₁ {Δ₂ ι} {cᵥ : StrongCastValue} →
                    Δ₁ ++ Δ₂ ⊢ cᵥ / length Δ₁ + ι Valid →
                    Δ₂ ⊢ cᵥ / ι Valid
c-valid-remove-left [] c⋆ = c⋆
c-valid-remove-left (a ∷ Δ₁) (valid-suc c⋆) = c-valid-remove-left Δ₁ c⋆
