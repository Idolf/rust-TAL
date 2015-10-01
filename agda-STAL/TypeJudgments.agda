open import Util
open import Grammar

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
    constructor valid-Γ
    field
      valid-sp : Δ ⊢ stack-type Γ StackType
      valid-regs : Allᵥ (λ τ → Δ ⊢ τ Type) (reg-types Γ)
