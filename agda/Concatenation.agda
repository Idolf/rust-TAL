open import Types
open import ListProperties
open import ValidTypes

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (sym)


mutual
  valid-Ctx-++ : ∀ {Δ₁ Δ₂} → IsValidCtx Δ₁ → IsValidCtx Δ₂ → IsValidCtx (Δ₁ ++ Δ₂)
  valid-Ctx-++ Δ₁⋆ valid-Ɛ = Δ₁⋆
  valid-Ctx-++ Δ₁⋆ (valid-∷ Δ₂⋆ a⋆) = valid-∷ (valid-Ctx-++ Δ₁⋆ Δ₂⋆) (valid-CtxVal-++ a⋆)

  valid-CtxVal-++ : ∀ {Δ₁ Δ₂ a} → IsValidCtxVal Δ₂ a → IsValidCtxVal (Δ₁ ++ Δ₂) a
  valid-CtxVal-++ valid-ρ = valid-ρ
  valid-CtxVal-++ (valid-α σ⋆) = valid-α (valid-Stack-++ σ⋆)
  valid-CtxVal-++ (valid-β σ⋆) = valid-β (valid-Stack-++ σ⋆)
  valid-CtxVal-++ (valid-≤a σ⋆ ℓ₁⋆ ℓ₂⋆) = valid-≤a (valid-Stack-++ σ⋆) (valid-Lifetime-++ ℓ₁⋆) (valid-Lifetime-++ ℓ₂⋆)

  valid-Stack-++ : ∀ {Δ₁ Δ₂ σ} → IsValidStack Δ₂ σ → IsValidStack (Δ₁ ++ Δ₂) σ
  valid-Stack-++ valid-nil = valid-nil
  valid-Stack-++ (valid-∷ σ⋆ v⋆) = valid-∷ (valid-Stack-++ σ⋆) (valid-StackVal-++ v⋆)
  valid-Stack-++ (valid-ρ⁼ l) = valid-ρ⁼ (Δ-lookup-++ l)

  valid-StackVal-++ : ∀ {Δ₁ Δ₂ σ v} → IsValidStackVal Δ₂ σ v → IsValidStackVal (Δ₁ ++ Δ₂) σ v
  valid-StackVal-++ (valid-type τ⋆) = valid-type (valid-Type-++ τ⋆)
  valid-StackVal-++ valid-γ = valid-γ

  valid-Type-++ : ∀ {Δ₁ Δ₂ σ τ} → IsValidType Δ₂ σ τ → IsValidType (Δ₁ ++ Δ₂) σ τ
  valid-Type-++ (♯b , τ⋆) = ♯b , valid-Typeₙ-++ τ⋆

  valid-Typeₙ-++ : ∀ {Δ₁ Δ₂ σ τ ♯b} → IsValidTypeₙ Δ₂ σ τ ♯b → IsValidTypeₙ (Δ₁ ++ Δ₂) σ τ ♯b
  valid-Typeₙ-++ (valid-β⁼ l suf) = valid-β⁼ (Δ-lookup-++ l) suf
  valid-Typeₙ-++ valid-int = valid-int
  valid-Typeₙ-++ valid-void = valid-void
  valid-Typeₙ-++ (valid-~ τ⋆) = valid-~ (valid-Type-++ τ⋆)
  valid-Typeₙ-++ (valid-& ℓ⋆ τ⋆) = valid-& (valid-Lifetime-++ ℓ⋆) (valid-Type-++ τ⋆)
  valid-Typeₙ-++ {Δ₁} {Δ₂} (valid-∀ {Δ₃} {Γ} Δ₃⋆ Γ⋆) = valid-∀ Δ₃⋆ (help Δ₁ Δ₂ Δ₃ Γ⋆)
    where help : ∀ Δ₁ Δ₂ Δ₃ → IsValidRegister (Δ₂ ++ Δ₃) Γ →
                              IsValidRegister ((Δ₁ ++ Δ₂) ++ Δ₃) Γ
          help Δ₁ Δ₂ Δ₃ Γ⋆ rewrite (sym (++-assoc Δ₁ Δ₂ Δ₃)) = valid-Register-++ Γ⋆

  valid-Register-++ : ∀ {Δ₁ Δ₂ Γ} → IsValidRegister Δ₂ Γ → IsValidRegister (Δ₁ ++ Δ₂) Γ
  valid-Register-++ (valid-register sp⋆ r0⋆ r1⋆ r2⋆) =
    valid-register (valid-Stack-++ sp⋆)
                   (valid-Typeₙ-++ r0⋆)
                   (valid-Typeₙ-++ r1⋆)
                   (valid-Typeₙ-++ r2⋆)

  valid-Lifetime-++ : ∀ {Δ₁ Δ₂ σ ℓ} → IsValidLifetime Δ₂ σ ℓ → IsValidLifetime (Δ₁ ++ Δ₂) σ ℓ
  valid-Lifetime-++ (valid-α⁼ l suf) = valid-α⁼ (Δ-lookup-++ l) suf
  valid-Lifetime-++ (valid-γ⁼ l) = valid-γ⁼ l
  valid-Lifetime-++ valid-static = valid-static
