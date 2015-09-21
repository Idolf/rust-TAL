open import Types
open import ListProperties

open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

mutual
  data IsValidCtx : Ctx → Set where
    valid-Ɛ : IsValidCtx Ɛ
    valid-∷ : ∀ {Δ a} → IsValidCtx Δ → IsValidCtxVal Δ a → IsValidCtx (Δ , a)

  data IsValidCtxVal (Δ : Ctx) : CtxVal → Set where
    valid-ρ  : IsValidCtxVal Δ ρ
    valid-α  : ∀ {σ}   → IsValidStack Δ σ → IsValidCtxVal Δ (α σ)
    valid-β  : ∀ {σ ♯b} → IsValidStack Δ σ → IsValidCtxVal Δ (β σ ♯b)
    valid-≤a : ∀ {σ ℓ₁ ℓ₂} → IsValidStack Δ σ → IsValidLifetime Δ σ ℓ₁ → IsValidLifetime Δ σ ℓ₂ → IsValidCtxVal Δ (ℓ₁ ≤a ℓ₂ / σ)

  data IsValidStack (Δ : Ctx) : Stack → Set where
    valid-nil : IsValidStack Δ nil
    valid-∷   : ∀ {σ v} → IsValidStack Δ σ → IsValidStackVal Δ σ v → IsValidStack Δ (v ∷ σ)
    valid-ρ⁼  : ∀ {ι} → Δ-lookup Δ ι ρ → IsValidStack Δ (ρ⁼ ι)

  data IsValidStackVal (Δ : Ctx) (σ : Stack) : StackVal → Set where
    valid-type  : ∀ {τ} → IsValidType Δ σ τ → IsValidStackVal Δ σ (type τ)
    valid-γ     : IsValidStackVal Δ σ γ

  IsValidType : (Δ : Ctx) (σ : Stack) → Type → Set
  IsValidType Δ σ τ = Σ[ ♯b ∈ ℕ ] IsValidTypeₙ Δ σ τ ♯b

  data IsValidTypeₙ (Δ : Ctx) (σ : Stack) : Type → ℕ → Set where
    valid-β⁼     : ∀ {σ' ι ♯b} → Δ-lookup Δ ι (β σ' ♯b) → IsStackSuffix σ' σ → IsValidTypeₙ Δ σ (β⁼ ι) ♯b
    valid-int    : IsValidTypeₙ Δ σ int 4
    valid-void   : ∀ {♯b}      → IsValidTypeₙ Δ σ (void ♯b) ♯b
    valid-~      : ∀ {τ}       → IsValidType Δ σ τ → IsValidTypeₙ Δ σ (~ τ) 4
    valid-&      : ∀ {ℓ q τ}   → IsValidLifetime Δ σ ℓ → IsValidType Δ σ τ → IsValidTypeₙ Δ σ (& ℓ q τ) 4
    valid-∀      : ∀ {Δ' Γ}    → IsValidCtx Δ' → IsValidRegister (Δ ++ Δ') Γ → IsValidTypeₙ Δ σ (∀[ Δ' ] Γ) 4

  record IsValidRegister (Δ : Ctx) (Γ : Register) : Set where
    inductive
    constructor valid-register
    field
      valid-sp : IsValidStack Δ (sp Γ)
      valid-r0 : IsValidTypeₙ Δ (sp Γ) (r0 Γ) 4
      valid-r1 : IsValidTypeₙ Δ (sp Γ) (r1 Γ) 4
      valid-r2 : IsValidTypeₙ Δ (sp Γ) (r2 Γ) 4

  data IsValidLifetime (Δ : Ctx) (σ : Stack) : Lifetime → Set where
    valid-α⁼     : ∀ {σ' ι} → Δ-lookup Δ ι (α σ') → IsStackSuffix σ' σ → IsValidLifetime Δ σ (α⁼ ι)
    valid-γ⁼     : ∀ {ι}    → σ-lookup σ ι γ → IsValidLifetime Δ σ (γ⁼ ι)
    valid-static : IsValidLifetime Δ σ static


IsValidTypeₙ-unique : ∀ {Δ σ₁ σ₂ τ ♯b₁ ♯b₂} → IsValidTypeₙ Δ σ₁ τ ♯b₁ → IsValidTypeₙ Δ σ₂ τ ♯b₂ → ♯b₁ ≡ ♯b₂
IsValidTypeₙ-unique (valid-β⁼ l₁ suf₁) (valid-β⁼ l₂ suf₂) with Δ-lookup-unique l₁ l₂
IsValidTypeₙ-unique (valid-β⁼ l₁ suf₁) (valid-β⁼ l₂ suf₂) | refl = refl
IsValidTypeₙ-unique valid-int valid-int = refl
IsValidTypeₙ-unique valid-void valid-void = refl
IsValidTypeₙ-unique (valid-~ τ₁⋆) (valid-~ τ₂⋆) = refl
IsValidTypeₙ-unique (valid-& ℓ₁⋆ τ₁⋆) (valid-& ℓ₂⋆ τ₂⋆) = refl
IsValidTypeₙ-unique (valid-∀ Δ₁⋆ Γ₁⋆) (valid-∀ Δ₂⋆ Γ₂⋆) = refl
