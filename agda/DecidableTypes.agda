open import Types
open import ValidTypes
open import ContradictionLemmas
open import UniquenessLemmas
open import DecidabilityLemmas

open import Data.Nat using (_≟_)
open import Data.Product using (_,_ ; Σ-syntax ; ∃)

open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)

mutual
  ⊢?_Ctx : ∀ Δ → Dec (⊢ Δ Ctx)
  ⊢? Ɛ Ctx = yes valid-Ɛ
  ⊢? Δ , a Ctx with ⊢? Δ Ctx | Δ ⊢? a CtxVal
  ⊢? Δ , a Ctx | yes Δ⋆ | yes a⋆ = yes (valid-∷ Δ⋆ a⋆)
  ⊢? Δ , a Ctx | no ¬Δ⋆ | _ = no (λ { (valid-∷ Δ⋆ a⋆) → ¬Δ⋆ Δ⋆ })
  ⊢? Δ , a Ctx | _ | no ¬a⋆ = no (λ { (valid-∷ Δ⋆ a⋆) → ¬a⋆ a⋆ })

  _⊢?_CtxVal : ∀ Δ a → Dec (Δ ⊢ a CtxVal)
  Δ ⊢? ρ              CtxVal = yes valid-ρ
  Δ ⊢? α σ            CtxVal with Δ ⊢? σ Stack
  Δ ⊢? α σ            CtxVal | yes σ⋆ = yes (valid-α σ⋆)
  Δ ⊢? α σ            CtxVal | no ¬σ⋆ = no (λ { (valid-α σ⋆) → ¬σ⋆ σ⋆ })
  Δ ⊢? β σ ♯b         CtxVal with Δ ⊢? σ Stack
  Δ ⊢? β σ ♯b         CtxVal | yes σ⋆ = yes (valid-β σ⋆)
  Δ ⊢? β σ ♯b         CtxVal | no ¬σ⋆ = no (λ { (valid-β σ⋆) → ¬σ⋆ σ⋆ })
  Δ ⊢? (ℓ₁ ≤a ℓ₂ / σ) CtxVal with Δ ⊢? σ Stack | Δ , σ ⊢? ℓ₁ Lifetime | Δ , σ ⊢? ℓ₂ Lifetime
  Δ ⊢? (ℓ₁ ≤a ℓ₂ / σ) CtxVal | yes ⋆σ | yes ⋆ℓ₁ | yes ⋆ℓ₂ = yes (valid-≤a ⋆σ ⋆ℓ₁ ⋆ℓ₂)
  Δ ⊢? (ℓ₁ ≤a ℓ₂ / σ) CtxVal | no ¬σ⋆ | _ | _ = no (λ { (valid-≤a σ⋆ ℓ₁⋆ ℓ₂⋆) → ¬σ⋆ σ⋆ })
  Δ ⊢? (ℓ₁ ≤a ℓ₂ / σ) CtxVal | _ | no ¬ℓ₁ | _ = no (λ { (valid-≤a σ⋆ ℓ₁⋆ ℓ₂⋆) → ¬ℓ₁ ℓ₁⋆ })
  Δ ⊢? (ℓ₁ ≤a ℓ₂ / σ) CtxVal | _ | _ | no ¬ℓ₂ = no (λ { (valid-≤a σ⋆ ℓ₁⋆ ℓ₂⋆) → ¬ℓ₂ ℓ₂⋆ })

  _⊢?_Stack : ∀ Δ σ → Dec (Δ ⊢ σ Stack)
  Δ ⊢? nil Stack = yes valid-nil
  Δ ⊢? v ∷ σ Stack with Δ , σ ⊢? v StackVal | Δ ⊢? σ Stack
  Δ ⊢? v ∷ σ Stack | yes v⋆ | yes σ⋆ = yes (valid-∷ σ⋆ v⋆)
  Δ ⊢? v ∷ σ Stack | no ¬v⋆ | _ = no (λ { (valid-∷ σ⋆ v⋆) → ¬v⋆ v⋆ })
  Δ ⊢? v ∷ σ Stack | _ | no ¬σ⋆ = no (λ { (valid-∷ σ⋆ v⋆) → ¬σ⋆ σ⋆ })
  Δ ⊢? ρ⁼ ι  Stack with Δ ↓ₐ? ι
  Δ ⊢? ρ⁼ ι  Stack | yes (ρ , l) = yes (valid-ρ⁼ l)
  Δ ⊢? ρ⁼ ι  Stack | yes (α σ , l) = no (λ { (valid-ρ⁼ l') → ρ≢α (↓ₐ-unique l' l) })
  Δ ⊢? ρ⁼ ι  Stack | yes (β σ ♯b , l) = no (λ { (valid-ρ⁼ l') → ρ≢β (↓ₐ-unique l' l) })
  Δ ⊢? ρ⁼ ι  Stack | yes ((ℓ₁ ≤a ℓ₂ / σ) , l) = no (λ { (valid-ρ⁼ l') → ρ≢≤a (↓ₐ-unique l' l) })
  Δ ⊢? ρ⁼ ι  Stack | no ¬l = no (λ { (valid-ρ⁼ l) → ¬l (ρ , l) })

  _,_⊢?_StackVal : ∀ Δ σ v → Dec (Δ , σ ⊢ v StackVal)
  Δ , σ ⊢? type τ StackVal with Δ , σ ⊢? τ Type
  Δ , σ ⊢? type τ StackVal | yes τ⋆ = yes (valid-type τ⋆)
  Δ , σ ⊢? type τ StackVal | no ¬τ⋆ = no (λ { (valid-type τ⋆) → ¬τ⋆ τ⋆ })
  Δ , σ ⊢? γ      StackVal = yes valid-γ

  _,_⊢?_Type : ∀ Δ σ τ → Dec (Δ , σ ⊢ τ Type)
  Δ , σ ⊢? β⁼ ι Type with Δ ↓ₐ? ι
  Δ , σ ⊢? β⁼ ι Type | yes (ρ , l) = no (λ { (♯b , valid-β⁼ l' suf) → ρ≢β (↓ₐ-unique l l') })
  Δ , σ ⊢? β⁼ ι Type | yes (α σ' , l) = no (λ { (♯b , valid-β⁼ l' suf) → α≢β (↓ₐ-unique l l') })
  Δ , σ ⊢? β⁼ ι Type | yes (β σ' ♯b , l) with σ' ⊏? σ
  Δ , σ ⊢? β⁼ ι Type | yes (β σ' ♯b , l) | yes suf = yes (♯b , valid-β⁼ l suf)
  Δ , σ ⊢? β⁼ ι Type | yes (β σ' ♯b , l) | no ¬suf = no (help l ¬suf)
    where help : ∀ {Δ ι σ σ₁ ♯b₁} → Δ ↓ₐ ι ≡ β σ₁ ♯b₁
                                  → ¬ (σ₁ ⊏ σ)
                                  → ¬ (Δ , σ ⊢ β⁼ ι Type)
          help l₁ ¬suf₁ (♯b₂ , valid-β⁼ l₂ suf₂) with ↓ₐ-unique l₁ l₂
          help l₁ ¬suf₁ (♯b₁ , valid-β⁼ l₂ suf₂) | refl = ¬suf₁ suf₂
  Δ , σ ⊢? β⁼ ι Type | yes ((x ≤a x₁ / x₂) , l) = no (λ { (♯b , valid-β⁼ l' suf) → β≢≤a (↓ₐ-unique l' l) })
  Δ , σ ⊢? β⁼ ι Type | no ¬l = no (λ { (proj₁ , valid-β⁼ l suf) → ¬l (_ , l) })
  Δ , σ ⊢? int Type = yes (4 , valid-int)
  Δ , σ ⊢? void ♯b Type = yes (♯b , valid-void)
  Δ , σ ⊢? ~ τ Type with Δ , σ ⊢? τ Type
  Δ , σ ⊢? ~ τ Type | yes τ⋆ = yes (4 , valid-~ τ⋆)
  Δ , σ ⊢? ~ τ Type | no ¬τ⋆ = no (λ { (.4 , valid-~ τ⋆) → ¬τ⋆ τ⋆ })
  Δ , σ ⊢? & ℓ q τ Type with Δ , σ ⊢? ℓ Lifetime | Δ , σ ⊢? τ Type
  Δ , σ ⊢? & ℓ q τ Type | yes ℓ⋆ | yes τ⋆ = yes (4 , valid-& ℓ⋆ τ⋆)
  Δ , σ ⊢? & ℓ q τ Type | no ¬ℓ⋆ | _ = no (λ { (.4 , valid-& ℓ⋆ τ⋆) → ¬ℓ⋆ ℓ⋆ })
  Δ , σ ⊢? & ℓ q τ Type | _ | no ¬τ⋆ = no (λ { (.4 , valid-& ℓ⋆ τ⋆) → ¬τ⋆ τ⋆ })
  Δ , σ ⊢? ∀[ Δ' ] Γ Type with ⊢? Δ' Ctx | (Δ ++ Δ') ⊢? Γ Register
  Δ , σ ⊢? ∀[ Δ' ] Γ Type | yes Δ'⋆ | yes Γ⋆ = yes (4 , valid-∀ Δ'⋆ Γ⋆)
  Δ , σ ⊢? ∀[ Δ' ] Γ Type | no ¬Δ'⋆ | _ = no (λ { (.4 , valid-∀ Δ'* Γ⋆) → ¬Δ'⋆ Δ'* })
  Δ , σ ⊢? ∀[ Δ' ] Γ Type | _ | no ¬Γ⋆  = no (λ { (.4 , valid-∀ Δ'* Γ⋆) → ¬Γ⋆ Γ⋆ })

  _,_⊢?_Typeₙ_ : ∀ Δ σ τ ♯b → Dec (Δ , σ ⊢ τ Typeₙ ♯b)
  Δ , σ ⊢? τ Typeₙ ♯b₁ with Δ , σ ⊢? τ Type
  Δ , σ ⊢? τ Typeₙ ♯b₁ | yes (♯b₂ , τ⋆) with ♯b₁ ≟ ♯b₂
  Δ , σ ⊢? τ Typeₙ ♯b₁ | yes (.♯b₁ , τ⋆) | yes refl = yes τ⋆
  Δ , σ ⊢? τ Typeₙ ♯b₁ | yes (♯b₂ , τ⋆) | no ¬eq = no (λ τ⋆' → ¬eq (Typeₙ-unique τ⋆' τ⋆))
  Δ , σ ⊢? τ Typeₙ ♯b₁ | no ¬τ⋆ = no (λ {τ⋆ → ¬τ⋆ (♯b₁ , τ⋆)})

  _⊢?_Register : ∀ Δ Γ → Dec (Δ ⊢ Γ Register)
  Δ ⊢? register sp r0 r1 r2 Register with Δ ⊢? sp Stack | Δ , sp ⊢? r0 Typeₙ 4 | Δ , sp ⊢? r1 Typeₙ 4 | Δ , sp ⊢? r2 Typeₙ 4
  Δ ⊢? register sp r0 r1 r2 Register | yes sp⋆ | yes r0⋆ | yes r1⋆ | yes r2⋆ = yes (valid-register sp⋆ r0⋆ r1⋆ r2⋆)
  Δ ⊢? register sp r0 r1 r2 Register | no ¬sp⋆ | _ | _ | _ = no (λ { (valid-register sp⋆ r0⋆ r1⋆ r2⋆) → ¬sp⋆ sp⋆ })
  Δ ⊢? register sp r0 r1 r2 Register | _ | no ¬r0⋆ | _ | _ = no (λ { (valid-register sp⋆ r0⋆ r1⋆ r2⋆) → ¬r0⋆ r0⋆ })
  Δ ⊢? register sp r0 r1 r2 Register | _ | _ | no ¬r1⋆ | _ = no (λ { (valid-register sp⋆ r0⋆ r1⋆ r2⋆) → ¬r1⋆ r1⋆ })
  Δ ⊢? register sp r0 r1 r2 Register | _ | _ | _ | no ¬r2⋆ = no (λ { (valid-register sp⋆ r0⋆ r1⋆ r2⋆) → ¬r2⋆ r2⋆ })

  _,_⊢?_Lifetime : ∀ Δ σ ℓ → Dec (Δ , σ ⊢ ℓ Lifetime)
  Δ , σ ⊢? α⁼ ι Lifetime with Δ ↓ₐ? ι
  Δ , σ ⊢? α⁼ ι Lifetime | yes (ρ , l) = no (λ { (valid-α⁼ l' suf) → ρ≢α (↓ₐ-unique l l') })
  Δ , σ ⊢? α⁼ ι Lifetime | yes (α σ' , l) with σ' ⊏? σ
  Δ , σ ⊢? α⁼ ι Lifetime | yes (α σ' , l) | yes suf = yes (valid-α⁼ l suf)
  Δ , σ ⊢? α⁼ ι Lifetime | yes (α σ' , l) | no ¬suf = no (help l ¬suf)
    where help : ∀ {Δ ι σ σ₁} → Δ ↓ₐ ι ≡ α σ₁
                   → ¬ (σ₁ ⊏ σ)
                   → ¬ (Δ , σ ⊢ α⁼ ι Lifetime)
          help l₁ ¬suf₁ (valid-α⁼ l₂ suf₂) with ↓ₐ-unique l₁ l₂
          help l₁ ¬suf₁ (valid-α⁼ l₂ suf₂) | refl = ¬suf₁ suf₂
  Δ , σ ⊢? α⁼ ι Lifetime | yes (β σ' ♯b , l) = no (λ { (valid-α⁼ l' suf) → α≢β (↓ₐ-unique l' l) })
  Δ , σ ⊢? α⁼ ι Lifetime | yes ((ℓ₁ ≤a ℓ₂ / σ') , l) = no (λ { (valid-α⁼ l' suf) → α≢≤a (↓ₐ-unique l' l) })
  Δ , σ ⊢? α⁼ ι Lifetime | no ¬l = no (λ { (valid-α⁼ l suf) → ¬l (_ , l) })
  Δ , σ ⊢? γ⁼ ι Lifetime with σ ↓ᵥ? ι
  Δ , σ ⊢? γ⁼ ι Lifetime | yes (type τ , l) = no (λ { (valid-γ⁼ l') → type≢γ (↓ᵥ-unique l l') })
  Δ , σ ⊢? γ⁼ ι Lifetime | yes (γ , l) = yes (valid-γ⁼ l)
  Δ , σ ⊢? γ⁼ ι Lifetime | no ¬l = no (λ { (valid-γ⁼ l) → ¬l (γ , l) })
  Δ , σ ⊢? static Lifetime = yes valid-static
