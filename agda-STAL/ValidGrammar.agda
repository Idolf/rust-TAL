open import Util
open import Grammar

infix 5 _++_
infix 4 _↓_⇒_
infix 4 _⊢_Type _⊢_StackType ⊢_LabelAssignment ⊢_TypeAssignment _⊢_RegisterAssignment
infix 4 _⊢_≤τ_

_++_ : TypeAssignment → TypeAssignment → TypeAssignment
Δ ++ ∙ = Δ
Δ ++ Δ' , a = (Δ ++ Δ') , a

data _↓_⇒_ : TypeAssignment → AssignmentIndex → TypeAssignmentValue → Set where
  here :
        ∀ {Δ a} →
    ----------------
    Δ , a ↓ zero ⇒ a

  there :
      ∀ {Δ a a' ι} →
        Δ ↓ ι ⇒ a →
    ------------------
    Δ , a' ↓ suc ι ⇒ a

mutual
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
      Δ ++ Δ' ⊢ Γ RegisterAssignment →
      --------------------------------
            Δ ⊢ ∀[ Δ' ] Γ Type

    valid-tuple :
                  ∀ {τs} →
      All ((λ τ → Δ ⊢ τ Type) ∘ proj₁) τs →
      -------------------------------------
              Δ ⊢ tuple τs Type

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

  data ⊢_LabelAssignment : LabelAssignment → Set where
    valid-ψ :
              ∀ {ψ} →
      All (λ τ → ∙ ⊢ τ Type) ψ →
      --------------------------
         ⊢ ψ LabelAssignment

  data ⊢_TypeAssignment : TypeAssignment → Set where
    valid-Δ :
            ∀ {Δ} →
      ------------------
      ⊢ Δ TypeAssignment

  record _⊢_RegisterAssignment (Δ : TypeAssignment) (Γ : RegisterAssignment) : Set where
    inductive
    field
      valid-sp : Δ ⊢ stack-type Γ StackType
      valid-regs : All (λ τ → Δ ⊢ τ Type) (toList (reg-types Γ))

  data _⊢_≤τ_ (Δ : TypeAssignment) : Type → Type → Set where
    refl :
        ∀ {τ} →
      Δ ⊢ τ Type →
      ------------
       Δ ⊢ τ ≤τ τ

    trans :
      ∀ {τ₁ τ₂ τ₃} →
      Δ ⊢ τ₁ ≤τ τ₂ →
      Δ ⊢ τ₂ ≤τ τ₃ →
      --------------
      Δ ⊢ τ₁ ≤τ τ₃

  data _⊢_≤Γ_ (Δ : TypeAssignment) : RegisterAssignment → RegisterAssignment → Set where
    refl :
               ∀ {Γ} →
      Δ ⊢ Γ RegisterAssignment →
      --------------------------
             Δ ⊢ Γ ≤Γ Γ

    trans :
      ∀ {Γ₁ Γ₂ Γ₃} →
      Δ ⊢ Γ₁ ≤Γ Γ₂ →
      Δ ⊢ Γ₂ ≤Γ Γ₃ →
      --------------
      Δ ⊢ Γ₁ ≤Γ Γ₃
