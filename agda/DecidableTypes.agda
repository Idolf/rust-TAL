open import Types
open import ListProperties
open import ValidTypes
open import Equality
open import EqualityContradictions

open import Data.Nat using (zero ; suc ; _≟_)
open import Data.Product using (_,_ ; Σ-syntax ; ∃)
open import Data.Empty using (⊥)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)


Δ-lookup? : ∀ Δ ι → Dec (Σ[ a ∈ CtxVal ] Δ-lookup Δ ι a)
Δ-lookup? Ɛ ι = no λ { (a , ()) }
Δ-lookup? (Δ , a) zero = yes (a , here)
Δ-lookup? (Δ , a) (suc ι) with Δ-lookup? Δ ι
Δ-lookup? (Δ , a) (suc ι) | yes (a' , l) = yes (a' , there l)
Δ-lookup? (Δ , a) (suc ι) | no ¬l = no (λ { (a , there l) → ¬l (a , l)})

σ-lookup? : ∀ σ ι → Dec (Σ[ v ∈ StackVal ] σ-lookup σ ι v)
σ-lookup? nil ι = no λ { (v , ()) }
σ-lookup? (ρ⁼ ι) ι' = no λ { (v , ()) }
σ-lookup? (v ∷ σ) zero = yes (v , here)
σ-lookup? (v ∷ σ) (suc ι) with σ-lookup? σ ι
σ-lookup? (v ∷ σ) (suc ι) | yes (v' , l) = yes (v' , there l)
σ-lookup? (v ∷ σ) (suc ι) | no ¬l = no (λ { (v , there l) → ¬l (v , l)})

IsStackSuffix? : ∀ σ₁ σ₂ → Dec (IsStackSuffix σ₁ σ₂)
IsStackSuffix? σ₁ (v₂ ∷ σ₂) with IsStackSuffix? σ₁ σ₂ | σ₁ ≟σ (v₂ ∷ σ₂)
IsStackSuffix? σ₁ (v₂ ∷ σ₂) | yes suf | _ = yes (there suf)
IsStackSuffix? .(v₂ ∷ σ₂) (v₂ ∷ σ₂) | _ | yes refl = yes here
IsStackSuffix? σ₁ (v₂ ∷ σ₂) | no ¬suf | no ¬eq = no (help ¬suf ¬eq)
  where help : ∀ {σ₁ v₂ σ₂} → ¬ (IsStackSuffix σ₁ σ₂) → ¬ (σ₁ ≡ v₂ ∷ σ₂) → ¬ (IsStackSuffix σ₁ (v₂ ∷ σ₂))
        help ¬suf ¬p here = ¬p refl
        help ¬suf ¬p (there suf) = ¬suf suf
IsStackSuffix? nil nil = yes here
IsStackSuffix? nil (ρ⁼ x) = no (λ ())
IsStackSuffix? (v₁ ∷ σ₁) nil = no (λ ())
IsStackSuffix? (v₁ ∷ σ₁) (ρ⁼ ι₂) = no (λ ())
IsStackSuffix? (ρ⁼ ι₁) nil = no (λ ())
IsStackSuffix? (ρ⁼ ι₁) (ρ⁼ ι₂) with ι₁ ≟ ι₂
IsStackSuffix? (ρ⁼ ι₁) (ρ⁼ .ι₁) | yes refl = yes here
IsStackSuffix? (ρ⁼ ι₁) (ρ⁼ ι₂) | no ¬eq = no (λ suf → ¬eq (help suf))
  where help : ∀ {ι₁ ι₂} → IsStackSuffix (ρ⁼ ι₁) (ρ⁼ ι₂) → ι₁ ≡ ι₂
        help here = refl

mutual
  IsValidCtx? : ∀ Δ → Dec (IsValidCtx Δ)
  IsValidCtx? Ɛ = yes valid-Ɛ
  IsValidCtx? (Δ , a) with IsValidCtx? Δ | IsValidCtxVal? Δ a
  IsValidCtx? (Δ , a) | yes Δ⋆ | yes a⋆ = yes (valid-∷ Δ⋆ a⋆)
  IsValidCtx? (Δ , a) | no ¬Δ⋆ | _ = no (λ { (valid-∷ Δ⋆ a⋆) → ¬Δ⋆ Δ⋆ })
  IsValidCtx? (Δ , a) | _ | no ¬a⋆ = no (λ { (valid-∷ Δ⋆ a⋆) → ¬a⋆ a⋆ })

  IsValidCtxVal? : ∀ Δ a → Dec (IsValidCtxVal Δ a)
  IsValidCtxVal? Δ ρ = yes valid-ρ
  IsValidCtxVal? Δ (α σ) with IsValidStack? Δ σ
  IsValidCtxVal? Δ (α σ) | yes σ⋆ = yes (valid-α σ⋆)
  IsValidCtxVal? Δ (α σ) | no ¬σ⋆ = no (λ { (valid-α σ⋆) → ¬σ⋆ σ⋆ })
  IsValidCtxVal? Δ (β σ ♯b) with IsValidStack? Δ σ
  IsValidCtxVal? Δ (β σ ♯b) | yes σ⋆ = yes (valid-β σ⋆)
  IsValidCtxVal? Δ (β σ ♯b) | no ¬σ⋆ = no (λ { (valid-β σ⋆) → ¬σ⋆ σ⋆ })
  IsValidCtxVal? Δ (ℓ₁ ≤a ℓ₂ / σ) with IsValidStack? Δ σ | IsValidLifetime? Δ σ ℓ₁ | IsValidLifetime? Δ σ ℓ₂
  IsValidCtxVal? Δ (ℓ₁ ≤a ℓ₂ / σ) | yes ⋆σ | yes ⋆ℓ₁ | yes ⋆ℓ₂ = yes (valid-≤a ⋆σ ⋆ℓ₁ ⋆ℓ₂)
  IsValidCtxVal? Δ (ℓ₁ ≤a ℓ₂ / σ) | no ¬σ⋆ | _ | _ = no (λ { (valid-≤a σ⋆ ℓ₁⋆ ℓ₂⋆) → ¬σ⋆ σ⋆ })
  IsValidCtxVal? Δ (ℓ₁ ≤a ℓ₂ / σ) | _ | no ¬ℓ₁ | _ = no (λ { (valid-≤a σ⋆ ℓ₁⋆ ℓ₂⋆) → ¬ℓ₁ ℓ₁⋆ })
  IsValidCtxVal? Δ (ℓ₁ ≤a ℓ₂ / σ) | _ | _ | no ¬ℓ₂ = no (λ { (valid-≤a σ⋆ ℓ₁⋆ ℓ₂⋆) → ¬ℓ₂ ℓ₂⋆ })

  IsValidStack? : ∀ Δ σ → Dec (IsValidStack Δ σ)
  IsValidStack? Δ nil = yes valid-nil
  IsValidStack? Δ (v ∷ σ) with IsValidStackVal? Δ σ v | IsValidStack? Δ σ
  IsValidStack? Δ (v ∷ σ) | yes v⋆ | yes σ⋆ = yes (valid-∷ σ⋆ v⋆)
  IsValidStack? Δ (v ∷ σ) | no ¬v⋆ | _ = no (λ { (valid-∷ σ⋆ v⋆) → ¬v⋆ v⋆ })
  IsValidStack? Δ (v ∷ σ) | _ | no ¬σ⋆ = no (λ { (valid-∷ σ⋆ v⋆) → ¬σ⋆ σ⋆ })
  IsValidStack? Δ (ρ⁼ ι) with Δ-lookup? Δ ι
  IsValidStack? Δ (ρ⁼ ι) | yes (ρ , l) = yes (valid-ρ⁼ l)
  IsValidStack? Δ (ρ⁼ ι) | yes (α σ , l) = no (λ { (valid-ρ⁼ l') → ρ≡α→⊥ (Δ-lookup-unique l' l) })
  IsValidStack? Δ (ρ⁼ ι) | yes (β σ ♯b , l) = no (λ { (valid-ρ⁼ l') → ρ≡β→⊥ (Δ-lookup-unique l' l) })
  IsValidStack? Δ (ρ⁼ ι) | yes ((ℓ₁ ≤a ℓ₂ / σ) , l) = no (λ { (valid-ρ⁼ l') → ρ≡≤a→⊥ (Δ-lookup-unique l' l) })
  IsValidStack? Δ (ρ⁼ ι) | no ¬l = no (λ { (valid-ρ⁼ l) → ¬l (ρ , l) })

  IsValidStackVal? : ∀ Δ σ v → Dec (IsValidStackVal Δ σ v)
  IsValidStackVal? Δ σ (type τ) with IsValidType? Δ σ τ
  IsValidStackVal? Δ σ (type τ) | yes τ⋆ = yes (valid-type τ⋆)
  IsValidStackVal? Δ σ (type τ) | no ¬τ⋆ = no (λ { (valid-type τ⋆) → ¬τ⋆ τ⋆ })
  IsValidStackVal? Δ σ γ = yes valid-γ

  IsValidType? : ∀ Δ σ τ → Dec (IsValidType Δ σ τ)
  IsValidType? Δ σ (β⁼ ι) with Δ-lookup? Δ ι
  IsValidType? Δ σ (β⁼ ι) | yes (ρ , l) = no (λ { (♯b , valid-β⁼ l' suf) → ρ≡β→⊥ (Δ-lookup-unique l l') })
  IsValidType? Δ σ (β⁼ ι) | yes (α σ' , l) = no (λ { (♯b , valid-β⁼ l' suf) → α≡β→⊥ (Δ-lookup-unique l l') })
  IsValidType? Δ σ (β⁼ ι) | yes (β σ' ♯b , l) with IsStackSuffix? σ' σ
  IsValidType? Δ σ (β⁼ ι) | yes (β σ' ♯b , l) | yes suf = yes (♯b , valid-β⁼ l suf)
  IsValidType? Δ σ (β⁼ ι) | yes (β σ' ♯b , l) | no ¬suf = no (help l ¬suf)
    where help : ∀ {Δ ι σ σ₁ ♯b₁} → Δ-lookup Δ ι (β σ₁ ♯b₁)
                                  → ¬ (IsStackSuffix σ₁ σ)
                                  → ∃ (IsValidTypeₙ Δ σ (β⁼ ι))
                                  → ⊥
          help l₁ ¬suf₁ (♯b₂ , valid-β⁼ l₂ suf₂) with Δ-lookup-unique l₁ l₂
          help l₁ ¬suf₁ (♯b₁ , valid-β⁼ l₂ suf₂) | refl = ¬suf₁ suf₂
  IsValidType? Δ σ (β⁼ ι) | yes ((x ≤a x₁ / x₂) , l) = no (λ { (♯b , valid-β⁼ l' suf) → β≡≤a→⊥ (Δ-lookup-unique l' l) })
  IsValidType? Δ σ (β⁼ ι) | no ¬l = no (λ { (proj₁ , valid-β⁼ l suf) → ¬l (_ , l) })
  IsValidType? Δ σ int = yes (4 , valid-int)
  IsValidType? Δ σ (void ♯b) = yes (♯b , valid-void)
  IsValidType? Δ σ (~ τ) with IsValidType? Δ σ τ
  IsValidType? Δ σ (~ τ) | yes τ⋆ = yes (4 , valid-~ τ⋆)
  IsValidType? Δ σ (~ τ) | no ¬τ⋆ = no (λ { (.4 , valid-~ τ⋆) → ¬τ⋆ τ⋆ })
  IsValidType? Δ σ (& ℓ q τ) with IsValidLifetime? Δ σ ℓ | IsValidType? Δ σ τ
  IsValidType? Δ σ (& ℓ q τ) | yes ℓ⋆ | yes τ⋆ = yes (4 , valid-& ℓ⋆ τ⋆)
  IsValidType? Δ σ (& ℓ q τ) | no ¬ℓ⋆ | _ = no (λ { (.4 , valid-& ℓ⋆ τ⋆) → ¬ℓ⋆ ℓ⋆ })
  IsValidType? Δ σ (& ℓ q τ) | _ | no ¬τ⋆ = no (λ { (.4 , valid-& ℓ⋆ τ⋆) → ¬τ⋆ τ⋆ })
  IsValidType? Δ σ (∀[ Δ' ] Γ) with IsValidCtx? Δ' | IsValidRegister? (Δ ++ Δ') Γ
  IsValidType? Δ σ (∀[ Δ' ] Γ) | yes Δ'⋆ | yes Γ⋆ = yes (4 , valid-∀ Δ'⋆ Γ⋆)
  IsValidType? Δ σ (∀[ Δ' ] Γ) | no ¬Δ'⋆ | _ = no (λ { (.4 , valid-∀ Δ'* Γ⋆) → ¬Δ'⋆ Δ'* })
  IsValidType? Δ σ (∀[ Δ' ] Γ) | _ | no ¬Γ⋆  = no (λ { (.4 , valid-∀ Δ'* Γ⋆) → ¬Γ⋆ Γ⋆ })

  IsValidTypeₙ? : ∀ Δ σ τ ♯b → Dec (IsValidTypeₙ Δ σ τ ♯b)
  IsValidTypeₙ? Δ σ τ ♯b₁ with IsValidType? Δ σ τ
  IsValidTypeₙ? Δ σ τ ♯b₁ | yes (♯b₂ , τ⋆) with ♯b₁ ≟ ♯b₂
  IsValidTypeₙ? Δ σ τ ♯b₁ | yes (.♯b₁ , τ⋆) | yes refl = yes τ⋆
  IsValidTypeₙ? Δ σ τ ♯b₁ | yes (♯b₂ , τ⋆) | no ¬eq = no (λ τ⋆' → ¬eq (IsValidTypeₙ-unique τ⋆' τ⋆))
  IsValidTypeₙ? Δ σ τ ♯b₁ | no ¬τ⋆ = no (λ {τ⋆ → ¬τ⋆ (♯b₁ , τ⋆)})

  IsValidRegister? : ∀ Δ Γ → Dec (IsValidRegister Δ Γ)
  IsValidRegister? Δ (register sp r0 r1 r2) with IsValidStack? Δ sp | IsValidTypeₙ? Δ sp r0 4 | IsValidTypeₙ? Δ sp r1 4 | IsValidTypeₙ? Δ sp r2 4
  IsValidRegister? Δ (register sp r0 r1 r2) | yes sp⋆ | yes r0⋆ | yes r1⋆ | yes r2⋆ = yes (valid-register sp⋆ r0⋆ r1⋆ r2⋆)
  IsValidRegister? Δ (register sp r0 r1 r2) | no ¬sp⋆ | _ | _ | _ = no (λ { (valid-register sp⋆ r0⋆ r1⋆ r2⋆) → ¬sp⋆ sp⋆ })
  IsValidRegister? Δ (register sp r0 r1 r2) | _ | no ¬r0⋆ | _ | _ = no (λ { (valid-register sp⋆ r0⋆ r1⋆ r2⋆) → ¬r0⋆ r0⋆ })
  IsValidRegister? Δ (register sp r0 r1 r2) | _ | _ | no ¬r1⋆ | _ = no (λ { (valid-register sp⋆ r0⋆ r1⋆ r2⋆) → ¬r1⋆ r1⋆ })
  IsValidRegister? Δ (register sp r0 r1 r2) | _ | _ | _ | no ¬r2⋆ = no (λ { (valid-register sp⋆ r0⋆ r1⋆ r2⋆) → ¬r2⋆ r2⋆ })

  IsValidLifetime? : ∀ Δ σ ℓ → Dec (IsValidLifetime Δ σ ℓ)
  IsValidLifetime? Δ σ (α⁼ ι) with Δ-lookup? Δ ι
  IsValidLifetime? Δ σ (α⁼ ι) | yes (ρ , l) = no (λ { (valid-α⁼ l' suf) → ρ≡α→⊥ (Δ-lookup-unique l l') })
  IsValidLifetime? Δ σ (α⁼ ι) | yes (α σ' , l) with IsStackSuffix? σ' σ
  IsValidLifetime? Δ σ (α⁼ ι) | yes (α σ' , l) | yes suf = yes (valid-α⁼ l suf)
  IsValidLifetime? Δ σ (α⁼ ι) | yes (α σ' , l) | no ¬suf = no (help l ¬suf)
    where help : ∀ {Δ ι σ σ₁} → Δ-lookup Δ ι (α σ₁)
                   → ¬ (IsStackSuffix σ₁ σ)
                   → IsValidLifetime Δ σ (α⁼ ι)
                   → ⊥
          help l₁ ¬suf₁ (valid-α⁼ l₂ suf₂) with Δ-lookup-unique l₁ l₂
          help l₁ ¬suf₁ (valid-α⁼ l₂ suf₂) | refl = ¬suf₁ suf₂
  IsValidLifetime? Δ σ (α⁼ ι) | yes (β σ' ♯b , l) = no (λ { (valid-α⁼ l' suf) → α≡β→⊥ (Δ-lookup-unique l' l) })
  IsValidLifetime? Δ σ (α⁼ ι) | yes ((ℓ₁ ≤a ℓ₂ / σ') , l) = no (λ { (valid-α⁼ l' suf) → α≡≤a→⊥ (Δ-lookup-unique l' l) })
  IsValidLifetime? Δ σ (α⁼ ι) | no ¬l = no (λ { (valid-α⁼ l suf) → ¬l (_ , l) })
  IsValidLifetime? Δ σ (γ⁼ ι) with σ-lookup? σ ι
  IsValidLifetime? Δ σ (γ⁼ ι) | yes (type τ , l) = no (λ { (valid-γ⁼ l') → type≡γ→⊥ (σ-lookup-unique l l') })
  IsValidLifetime? Δ σ (γ⁼ ι) | yes (γ , l) = yes (valid-γ⁼ l)
  IsValidLifetime? Δ σ (γ⁼ ι) | no ¬l = no (λ { (valid-γ⁼ l) → ¬l (γ , l) })
  IsValidLifetime? Δ σ static = yes valid-static
