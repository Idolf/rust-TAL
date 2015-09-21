open import Types
open import Weakening
open import Eq
open import TypesEq

open import Data.Nat using (zero ; suc)
open import Data.Product using (_,_ ; Σ-syntax)

open import Relation.Binary.Core using (Decidable ; _≡_ ; refl)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)

infix 4 _↓ₐ?_ _↓ᵥ?_ _⊏?_

_↓ₐ?_ : ∀ Δ ι → Dec (Σ[ a ∈ CtxVal ] Δ ↓ₐ ι ≡ a)
Ɛ ↓ₐ? ι = no λ { (a , ()) }
Δ , a ↓ₐ? zero = yes (a , here)
Δ , a ↓ₐ? suc ι with Δ ↓ₐ? ι
Δ , a ↓ₐ? suc ι | yes (a' , l) = yes (_ , there l)
Δ , a ↓ₐ? suc ι | no ¬l = no (λ { (._ , there l) → ¬l (_ , l) })

_↓ᵥ?_ : ∀ σ ι → Dec (Σ[ v ∈ StackVal ] σ ↓ᵥ ι ≡ v)
nil ↓ᵥ? ι = no λ { (v , ()) }
ρ⁼ ι ↓ᵥ? ι' = no λ { (v , ()) }
v ∷ σ ↓ᵥ? zero = yes (v , here)
v ∷ σ ↓ᵥ? suc ι with σ ↓ᵥ? ι
v ∷ σ ↓ᵥ? suc ι | yes (v' , l) = yes (v' , there l)
v ∷ σ ↓ᵥ? suc ι | no ¬l = no (λ { (v , there l) → ¬l (v , l)})

_⊏?_ : Decidable _⊏_
σ₁ ⊏? v₂ ∷ σ₂ with σ₁ ⊏? σ₂ | σ₁ ≟ v₂ ∷ σ₂
σ₁ ⊏? v₂ ∷ σ₂ | yes suf | _ = yes (there suf)
.(v₂ ∷ σ₂) ⊏? v₂ ∷ σ₂ | _ | yes refl = yes here
σ₁ ⊏? v₂ ∷ σ₂ | no ¬suf | no ¬eq = no (help ¬suf ¬eq)
  where help : ∀ {σ₁ v₂ σ₂} → ¬ (σ₁ ⊏ σ₂) → ¬ (σ₁ ≡ v₂ ∷ σ₂) → ¬ (σ₁ ⊏ v₂ ∷ σ₂)
        help ¬suf ¬p here = ¬p refl
        help ¬suf ¬p (there suf) = ¬suf suf
nil ⊏? nil = yes here
nil ⊏? ρ⁼ ι = no (λ ())
v₁ ∷ σ₁ ⊏? nil = no (λ ())
v₁ ∷ σ₁ ⊏? ρ⁼ ι₂ = no (λ ())
ρ⁼ ι₁ ⊏? nil = no (λ ())
ρ⁼ ι₁ ⊏? ρ⁼ ι₂ with ι₁ ≟ ι₂
ρ⁼ ι₁ ⊏? ρ⁼ .ι₁ | yes refl = yes here
ρ⁼ ι₁ ⊏? ρ⁼ ι₂ | no ¬eq = no (λ suf → ¬eq (help suf))
  where help : ∀ {ι₁ ι₂} → (ρ⁼ ι₁) ⊏ (ρ⁼ ι₂) → ι₁ ≡ ι₂
        help here = refl
