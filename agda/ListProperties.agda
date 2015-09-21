open import Types

open import Data.Nat using (ℕ ; suc ; zero)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

Δ-lookup-unique : ∀ {Δ ι a a'} → Δ-lookup Δ ι a → Δ-lookup Δ ι a' → a ≡ a'
Δ-lookup-unique here here = refl
Δ-lookup-unique (there l₁) (there l₂) = Δ-lookup-unique l₁ l₂

σ-lookup-unique : ∀ {σ ι v v'} → σ-lookup σ ι v → σ-lookup σ ι v' → v ≡ v'
σ-lookup-unique here here = refl
σ-lookup-unique (there l₁) (there l₂) = σ-lookup-unique l₁ l₂

Δ-lookup-++ : ∀ {Δ Δ' ι a} → Δ-lookup Δ ι a → Δ-lookup (Δ' ++ Δ) ι a
Δ-lookup-++ here = here
Δ-lookup-++ (there l) = there (Δ-lookup-++ l)

++-assoc : ∀ Δ₁ Δ₂ Δ₃ → Δ₁ ++ (Δ₂ ++ Δ₃) ≡ (Δ₁ ++ Δ₂) ++ Δ₃
++-assoc Δ₁ Δ₂ Ɛ = refl
++-assoc Δ₁ Δ₂ (Δ₃ , a) rewrite ++-assoc Δ₁ Δ₂ Δ₃ = refl
