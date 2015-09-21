open import Types

open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax)

infix 4 ⊢_Ctx _⊢_CtxVal _⊢_Stack _,_⊢_StackVal _,_⊢_Typeₙ_ _⊢_Register _,_⊢_Lifetime

mutual
  data ⊢_Ctx : Ctx → Set where
    valid-Ɛ :
         ⊢ Ɛ Ctx

    valid-∷ :
        ∀ {Δ a} →
        ⊢ Δ Ctx →
      Δ ⊢ a CtxVal →
      --------------
        ⊢ Δ , a Ctx

  data _⊢_CtxVal (Δ : Ctx) : CtxVal → Set where
    valid-ρ :
      Δ ⊢ ρ CtxVal

    valid-α :
          ∀ {σ} →
       Δ ⊢ σ Stack →
      --------------
      Δ ⊢ α σ CtxVal

    valid-β :
         ∀ {σ ♯b} →
        Δ ⊢ σ Stack →
      -----------------
      Δ ⊢ β σ ♯b CtxVal

    valid-≤a :
            ∀ {σ ℓ₁ ℓ₂} →
            Δ ⊢ σ Stack →
        Δ , σ ⊢ ℓ₁ Lifetime →
        Δ , σ ⊢ ℓ₂ Lifetime →
      -------------------------
      Δ ⊢ ℓ₁ ≤a ℓ₂ / σ CtxVal

  data _⊢_Stack (Δ : Ctx) : Stack → Set where
    valid-nil :
      Δ ⊢ nil Stack

    valid-∷ :
            ∀ {σ v} →
          Δ ⊢ σ Stack →
      Δ , σ ⊢ v StackVal →
      --------------------
         Δ ⊢ v ∷ σ Stack

    valid-ρ⁼ :
           ∀ {ι} →
         Δ ↓ₐ ι ≡ ρ →
      ----------------
        Δ ⊢ ρ⁼ ι Stack

  data _,_⊢_StackVal (Δ : Ctx) (σ : Stack) : StackVal → Set where
    valid-type :
               ∀ {τ} →
          Δ , σ ⊢ τ Type →
      -----------------------
      Δ , σ ⊢ type τ StackVal

    valid-γ :
      Δ , σ ⊢ γ StackVal

  _,_⊢_Type : (Δ : Ctx) (σ : Stack) → Type → Set
  Δ , σ ⊢ τ Type = Σ[ ♯b ∈ ℕ ] Δ , σ ⊢ τ Typeₙ ♯b

  data _,_⊢_Typeₙ_ (Δ : Ctx) (σ : Stack) : Type → ℕ → Set where
    valid-β⁼ :
           ∀ {σ' ι ♯b} →
       Δ ↓ₐ ι ≡ β σ' ♯b →
            σ' ⊏ σ →
      ---------------------
      Δ , σ ⊢ β⁼ ι Typeₙ ♯b

    valid-int :
      Δ , σ ⊢ int Typeₙ 4

    valid-void :
              ∀ {♯b} →
      ------------------------
      Δ , σ ⊢ void ♯b Typeₙ ♯b

    valid-~ :
            ∀ {τ} →
       Δ , σ ⊢ τ Type →
      -------------------
      Δ , σ ⊢ ~ τ Typeₙ 4

    valid-& :
             ∀ {ℓ q τ} →
          Δ , σ ⊢ ℓ Lifetime →
          Δ , σ ⊢ τ Type →
      -----------------------
      Δ , σ ⊢ & ℓ q τ Typeₙ 4

    valid-∀ :
             ∀ {Δ' Γ} →
                ⊢ Δ' Ctx →
        Δ ++ Δ' ⊢ Γ Register →
      -------------------------
      Δ , σ ⊢ ∀[ Δ' ] Γ Typeₙ 4

  record _⊢_Register (Δ : Ctx) (Γ : Register) : Set where
    inductive
    constructor valid-register
    field
      sp⋆ : Δ ⊢ sp Γ Stack
      r0⋆ : Δ , sp Γ ⊢ r0 Γ Typeₙ 4
      r1⋆ : Δ , sp Γ ⊢ r1 Γ Typeₙ 4
      r2⋆ : Δ , sp Γ ⊢ r2 Γ Typeₙ 4

  data _,_⊢_Lifetime (Δ : Ctx) (σ : Stack) : Lifetime → Set where
    valid-α⁼ :
           ∀ {σ' ι} →
          Δ ↓ₐ ι ≡ α σ' →
            σ' ⊏ σ →
      ---------------------
      Δ , σ ⊢ α⁼ ι Lifetime

    valid-γ⁼ :
             ∀ {ι} →
           σ ↓ᵥ ι ≡ γ →
      ---------------------
      Δ , σ ⊢ γ⁼ ι Lifetime

    valid-static :
      Δ , σ ⊢ static Lifetime
