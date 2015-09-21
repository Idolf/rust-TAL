open import Types
open import ValidTypes

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

↓ₐ-unique : ∀ {Δ ι a₁ a₂} → Δ ↓ₐ ι ≡ a₁ → Δ ↓ₐ ι ≡ a₂ → a₁ ≡ a₂
↓ₐ-unique here here = refl
↓ₐ-unique (there l₁) (there l₂) = ↓ₐ-unique l₁ l₂

↓ᵥ-unique : ∀ {σ ι v₁ v₂} → σ ↓ᵥ ι ≡ v₁ → σ ↓ᵥ ι ≡ v₂ → v₁ ≡ v₂
↓ᵥ-unique here here = refl
↓ᵥ-unique (there l₁) (there l₂) = ↓ᵥ-unique l₁ l₂

Typeₙ-unique : ∀ {Δ σ₁ σ₂ τ ♯b₁ ♯b₂} →
                 Δ , σ₁ ⊢ τ Typeₙ ♯b₁ →
                 Δ , σ₂ ⊢ τ Typeₙ ♯b₂ →
                 ♯b₁ ≡ ♯b₂
Typeₙ-unique (valid-β⁼ l₁ suf₁) (valid-β⁼ l₂ suf₂) with ↓ₐ-unique l₁ l₂
Typeₙ-unique (valid-β⁼ l₁ suf₁) (valid-β⁼ l₂ suf₂) | refl = refl
Typeₙ-unique valid-int valid-int = refl
Typeₙ-unique valid-void valid-void = refl
Typeₙ-unique (valid-~ τ₁⋆) (valid-~ τ₂⋆) = refl
Typeₙ-unique (valid-& ℓ₁⋆ τ₁⋆) (valid-& ℓ₂⋆ τ₂⋆) = refl
Typeₙ-unique (valid-∀ Δ₁⋆ Γ₁⋆) (valid-∀ Δ₂⋆ Γ₂⋆) = refl
