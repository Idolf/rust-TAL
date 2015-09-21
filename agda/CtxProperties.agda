open import Types
open import ValidTypes

open import Data.Nat using (ℕ ; suc ; zero)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym)


↓ₐ-++ : ∀ {Δ₁ Δ₂ ι a} → Δ₁ ↓ₐ ι ≡ a → Δ₂ ++ Δ₁ ↓ₐ ι ≡ a
↓ₐ-++ here = here
↓ₐ-++ (there l) = there (↓ₐ-++ l)

++-assoc : ∀ Δ₁ Δ₂ Δ₃ → Δ₁ ++ (Δ₂ ++ Δ₃) ≡ (Δ₁ ++ Δ₂) ++ Δ₃
++-assoc Δ₁ Δ₂ Ɛ = refl
++-assoc Δ₁ Δ₂ (Δ₃ , a) rewrite ++-assoc Δ₁ Δ₂ Δ₃ = refl

mutual
  valid-Ctx-++ : ∀ {Δ₁ Δ₂} → ⊢ Δ₁ Ctx → ⊢ Δ₂ Ctx → ⊢ (Δ₁ ++ Δ₂) Ctx
  valid-Ctx-++ Δ₁⋆ valid-Ɛ = Δ₁⋆
  valid-Ctx-++ Δ₁⋆ (valid-∷ Δ₂⋆ a⋆) = valid-∷ (valid-Ctx-++ Δ₁⋆ Δ₂⋆) (valid-CtxVal-++ a⋆)

  valid-CtxVal-++ : ∀ {Δ₁ Δ₂ a} → Δ₂ ⊢ a CtxVal → (Δ₁ ++ Δ₂) ⊢ a CtxVal
  valid-CtxVal-++ valid-ρ = valid-ρ
  valid-CtxVal-++ (valid-α σ⋆) = valid-α (valid-Stack-++ σ⋆)
  valid-CtxVal-++ (valid-β σ⋆) = valid-β (valid-Stack-++ σ⋆)
  valid-CtxVal-++ (valid-≤a σ⋆ ℓ₁⋆ ℓ₂⋆) = valid-≤a (valid-Stack-++ σ⋆) (valid-Lifetime-++ ℓ₁⋆) (valid-Lifetime-++ ℓ₂⋆)

  valid-Stack-++ : ∀ {Δ₁ Δ₂ σ} → Δ₂ ⊢ σ Stack → (Δ₁ ++ Δ₂) ⊢ σ Stack
  valid-Stack-++ valid-nil = valid-nil
  valid-Stack-++ (valid-∷ σ⋆ v⋆) = valid-∷ (valid-Stack-++ σ⋆) (valid-StackVal-++ v⋆)
  valid-Stack-++ (valid-ρ⁼ l) = valid-ρ⁼ (↓ₐ-++ l)

  valid-StackVal-++ : ∀ {Δ₁ Δ₂ σ v} → Δ₂ , σ ⊢ v StackVal → (Δ₁ ++ Δ₂) , σ ⊢ v StackVal
  valid-StackVal-++ (valid-type τ⋆) = valid-type (valid-Type-++ τ⋆)
  valid-StackVal-++ valid-γ = valid-γ

  valid-Type-++ : ∀ {Δ₁ Δ₂ σ τ} → Δ₂ , σ ⊢ τ Type → (Δ₁ ++ Δ₂) , σ ⊢ τ Type
  valid-Type-++ (♯b , τ⋆) = ♯b , valid-Typeₙ-++ τ⋆

  valid-Typeₙ-++ : ∀ {Δ₁ Δ₂ σ τ ♯b} → Δ₂ , σ ⊢ τ Typeₙ ♯b → (Δ₁ ++ Δ₂) , σ ⊢ τ Typeₙ ♯b
  valid-Typeₙ-++ (valid-β⁼ l suf) = valid-β⁼ (↓ₐ-++ l) suf
  valid-Typeₙ-++ valid-int = valid-int
  valid-Typeₙ-++ valid-void = valid-void
  valid-Typeₙ-++ (valid-~ τ⋆) = valid-~ (valid-Type-++ τ⋆)
  valid-Typeₙ-++ (valid-& ℓ⋆ τ⋆) = valid-& (valid-Lifetime-++ ℓ⋆) (valid-Type-++ τ⋆)
  valid-Typeₙ-++ {Δ₁} {Δ₂} (valid-∀ {Δ₃} {Γ} Δ₃⋆ Γ⋆) = valid-∀ Δ₃⋆ (help Δ₁ Δ₂ Δ₃ Γ⋆)
    where help : ∀ Δ₁ Δ₂ Δ₃ → (Δ₂ ++ Δ₃) ⊢ Γ Register →
                              ((Δ₁ ++ Δ₂) ++ Δ₃) ⊢ Γ Register
          help Δ₁ Δ₂ Δ₃ Γ⋆ rewrite (sym (++-assoc Δ₁ Δ₂ Δ₃)) = valid-Register-++ Γ⋆

  valid-Register-++ : ∀ {Δ₁ Δ₂ Γ} → Δ₂ ⊢ Γ Register → (Δ₁ ++ Δ₂) ⊢ Γ Register
  valid-Register-++ (valid-register sp⋆ r0⋆ r1⋆ r2⋆) =
    valid-register (valid-Stack-++ sp⋆)
                   (valid-Typeₙ-++ r0⋆)
                   (valid-Typeₙ-++ r1⋆)
                   (valid-Typeₙ-++ r2⋆)

  valid-Lifetime-++ : ∀ {Δ₁ Δ₂ σ ℓ} → Δ₂ , σ ⊢ ℓ Lifetime → (Δ₁ ++ Δ₂) , σ ⊢ ℓ Lifetime
  valid-Lifetime-++ (valid-α⁼ l suf) = valid-α⁼ (↓ₐ-++ l) suf
  valid-Lifetime-++ (valid-γ⁼ l) = valid-γ⁼ l
  valid-Lifetime-++ valid-static = valid-static
