open import Types
open import Data.Nat
open import Data.Product
open import Relation.Binary.Core
open import Relation.Nullary

,-injective : ∀ {Δ₁ Δ₂ a₁ a₂} → Δ₁ Types., a₁ ≡ Δ₂ , a₂ → Δ₁ ≡ Δ₂ × a₁ ≡ a₂
,-injective refl = refl , refl

α-injective : ∀ {σ₁ σ₂} → α σ₁ ≡ α σ₂ → σ₁ ≡ σ₂
α-injective refl = refl

β-injective : ∀ {σ₁ σ₂ ♯b₁ ♯b₂} → β σ₁ ♯b₁ ≡ β σ₂ ♯b₂ → σ₁ ≡ σ₂ × ♯b₁ ≡ ♯b₂
β-injective refl = refl , refl

≤a-injective : ∀ {ℓ₁₁ ℓ₁₂ ℓ₂₁ ℓ₂₂ σ₁ σ₂} → (ℓ₁₁ ≤a ℓ₁₂ / σ₁) ≡ (ℓ₂₁ ≤a ℓ₂₂ / σ₂) → ℓ₁₁ ≡ ℓ₂₁ × ℓ₁₂ ≡ ℓ₂₂ × σ₁ ≡ σ₂
≤a-injective refl = refl , (refl , refl)

∷-injective : ∀ {v₁ v₂ σ₁ σ₂} → (v₁ ∷ σ₁) ≡ (v₂ ∷ σ₂) → v₁ ≡ v₂ × σ₁ ≡ σ₂
∷-injective refl = refl , refl

ρ⁼-injective : ∀ {n₁ n₂} → ρ⁼ n₁ ≡ ρ⁼ n₂ → n₁ ≡ n₂
ρ⁼-injective refl = refl

type-injective : ∀ {τ₁ τ₂} → type τ₁ ≡ type τ₂ → τ₁ ≡ τ₂
type-injective refl = refl

β⁼-injective : ∀ {n₁ n₂} → β⁼ n₁ ≡ β⁼ n₂ → n₁ ≡ n₂
β⁼-injective refl = refl

void-injective : ∀ {♯b₁ ♯b₂} → void ♯b₁ ≡ void ♯b₂ → ♯b₁ ≡ ♯b₂
void-injective refl = refl

~-injective : ∀ {τ₁ τ₂} → ~ τ₁ ≡ ~ τ₂ → τ₁ ≡ τ₂
~-injective refl = refl

&-injective : ∀ {ℓ₁ ℓ₂ q₁ q₂ τ₁ τ₂} → & ℓ₁ q₁ τ₁ ≡ & ℓ₂ q₂ τ₂ → ℓ₁ ≡ ℓ₂ × q₁ ≡ q₂ × τ₁ ≡ τ₂
&-injective refl = refl , (refl , refl)

∀-injective : ∀ {Δ₁ Δ₂ Γ₁ Γ₂} → ∀[ Δ₁ ] Γ₁ ≡ ∀[ Δ₂ ] Γ₂ → Δ₁ ≡ Δ₂ × Γ₁ ≡ Γ₂
∀-injective refl = refl , refl

register-injective : ∀ {sp₁ sp₂ r0₁ r0₂ r1₁ r1₂ r2₁ r2₂} → register sp₁ r0₁ r1₁ r2₁ ≡ register sp₂ r0₂ r1₂ r2₂ →
                       sp₁ ≡ sp₂ × r0₁ ≡ r0₂ × r1₁ ≡ r1₂ × r2₁ ≡ r2₂
register-injective refl = refl , (refl , (refl , refl))

α⁼-injective : ∀ {n₁ n₂} → α⁼ n₁ ≡ α⁼ n₂ → n₁ ≡ n₂
α⁼-injective refl = refl

γ⁼-injective : ∀ {n₁ n₂} → γ⁼ n₁ ≡ γ⁼ n₂ → n₁ ≡ n₂
γ⁼-injective refl = refl

DecidableEq : ∀ {ℓ} → Set ℓ → Set ℓ
DecidableEq A = Decidable {A = A} _≡_

mutual
  _≟Δ_ : DecidableEq Ctx
  Ɛ ≟Δ Ɛ = yes refl
  Ɛ ≟Δ (Δ₂ , a₁) = no (λ ())
  (Δ₁ , a₁) ≟Δ Ɛ = no (λ ())
  (Δ₁ , a₁) ≟Δ (Δ₂ , a₂) with Δ₁ ≟Δ Δ₂ | a₁ ≟a a₂
  (Δ₁ , a₁) ≟Δ (.Δ₁ , .a₁) | yes refl | yes refl = yes refl
  (Δ₁ , a₁) ≟Δ (Δ₂ , a₂) | no ¬eq | _ = no (λ eq → ¬eq (proj₁ (,-injective eq)))
  (Δ₁ , a₁) ≟Δ (Δ₂ , a₂) | _ | no ¬eq = no (λ eq → ¬eq (proj₂ (,-injective eq)))

  _≟a_ : DecidableEq CtxVal
  ρ ≟a ρ = yes refl
  ρ ≟a α σ₂ = no (λ ())
  ρ ≟a β σ₂ ♯b₂ = no (λ ())
  ρ ≟a (ℓ₂₁ ≤a ℓ₂₂ / σ₂) = no (λ ())
  α σ₁ ≟a ρ = no (λ ())
  α σ₁ ≟a α σ₂ with σ₁ ≟σ σ₂
  α σ₁ ≟a α .σ₁ | yes refl = yes refl
  α σ₁ ≟a α σ₂ | no ¬eq = no (λ eq → ¬eq (α-injective eq))
  α σ₁ ≟a β σ₂ ♯b₂ = no (λ ())
  α σ₁ ≟a (ℓ₂₁ ≤a ℓ₂₂ / σ₂) = no (λ ())
  β σ₁ ♯b₁ ≟a ρ = no (λ ())
  β σ₁ ♯b₁ ≟a α σ₂ = no (λ ())
  β σ₁ ♯b₁ ≟a β σ₂ ♯b₂ with σ₁ ≟σ σ₂ | ♯b₁ ≟ ♯b₂
  β σ₁ ♯b₁ ≟a β .σ₁ .♯b₁ | yes refl | yes refl = yes refl
  β σ₁ ♯b₁ ≟a β σ₂ ♯b₂ | no ¬eq | _ = no (λ eq → ¬eq (proj₁ (β-injective eq)))
  β σ₁ ♯b₁ ≟a β σ₂ ♯b₂ | _ | no ¬eq = no (λ eq → ¬eq (proj₂ (β-injective eq)))
  β σ₁ ♯b₁ ≟a (ℓ₂₂ ≤a ℓ₂₁ / σ₂) = no (λ ())
  (ℓ₁₁ ≤a ℓ₁₂ / σ₁) ≟a ρ = no (λ ())
  (ℓ₁₁ ≤a ℓ₁₂ / σ₁) ≟a α σ = no (λ ())
  (ℓ₁₁ ≤a ℓ₁₂ / σ₁) ≟a β σ ♯b = no (λ ())
  (ℓ₁₁ ≤a ℓ₁₂ / σ₁) ≟a (ℓ₂₁ ≤a ℓ₂₂ / σ₂) with ℓ₁₁ ≟ℓ ℓ₂₁ | ℓ₁₂ ≟ℓ ℓ₂₂ | σ₁ ≟σ σ₂
  (ℓ₁₁ ≤a ℓ₁₂ / σ₁) ≟a (.ℓ₁₁ ≤a .ℓ₁₂ / .σ₁) | yes refl | yes refl | yes refl = yes refl
  (ℓ₁₁ ≤a ℓ₁₂ / σ₁) ≟a (ℓ₂₁ ≤a ℓ₂₂ / σ₂) | no ¬eq | _ | _ = no (λ eq → ¬eq (proj₁ (≤a-injective eq)))
  (ℓ₁₁ ≤a ℓ₁₂ / σ₁) ≟a (ℓ₂₁ ≤a ℓ₂₂ / σ₂) | _ | no ¬eq | _ = no (λ eq → ¬eq (proj₁ (proj₂ (≤a-injective eq))))
  (ℓ₁₁ ≤a ℓ₁₂ / σ₁) ≟a (ℓ₂₁ ≤a ℓ₂₂ / σ₂) | _ | _ | no ¬eq = no (λ eq → ¬eq (proj₂ (proj₂ (≤a-injective eq))))

  _≟σ_ : DecidableEq Stack
  nil ≟σ nil = yes refl
  nil ≟σ (v₂ ∷ σ₂) = no (λ ())
  nil ≟σ ρ⁼ n₂ = no (λ ())
  (v₁ ∷ σ₁) ≟σ nil = no (λ ())
  (v₁ ∷ σ₁) ≟σ (v₂ ∷ σ₂) with v₁ ≟v v₂ | σ₁ ≟σ σ₂
  (v₁ ∷ σ₁) ≟σ (.v₁ ∷ .σ₁) | yes refl | yes refl = yes refl
  (v₁ ∷ σ₁) ≟σ (v₂ ∷ σ₂) | no ¬eq | _ = no (λ eq → ¬eq (proj₁ (∷-injective eq)))
  (v₁ ∷ σ₁) ≟σ (v₂ ∷ σ₂) | _ | no ¬eq = no (λ eq → ¬eq (proj₂ (∷-injective eq)))
  (v₁ ∷ σ₁) ≟σ ρ⁼ n₂ = no (λ ())
  ρ⁼ n₁ ≟σ nil = no (λ ())
  ρ⁼ n₁ ≟σ (v₂ ∷ σ₂) = no (λ ())
  ρ⁼ n₁ ≟σ ρ⁼ n₂ with n₁ ≟ n₂
  ρ⁼ n₁ ≟σ ρ⁼ .n₁ | yes refl = yes refl
  ρ⁼ n₁ ≟σ ρ⁼ n₂ | no ¬eq = no (λ eq → ¬eq (ρ⁼-injective eq))

  _≟v_ : DecidableEq StackVal
  type τ₁ ≟v type τ₂ with τ₁ ≟τ τ₂
  type τ₁ ≟v type .τ₁ | yes refl = yes refl
  type τ₁ ≟v type τ₂ | no ¬eq = no (λ eq → ¬eq (type-injective eq))
  type τ₁ ≟v γ = no (λ ())
  γ ≟v type τ₂ = no (λ ())
  γ ≟v γ = yes refl

  _≟τ_ : DecidableEq Type
  β⁼ n₁ ≟τ β⁼ n₂ with n₁ ≟ n₂
  β⁼ n₁ ≟τ β⁼ .n₁ | yes refl = yes refl
  β⁼ n₁ ≟τ β⁼ n₂ | no ¬eq = no (λ eq → ¬eq (β⁼-injective eq))
  β⁼ n₁ ≟τ int = no (λ ())
  β⁼ n₁ ≟τ void ♯b₂ = no (λ ())
  β⁼ n₁ ≟τ ~ τ₂ = no (λ ())
  β⁼ n₁ ≟τ & ℓ₂ q₂ τ₂ = no (λ ())
  β⁼ n₁ ≟τ ∀[ Δ₂ ] Γ₂ = no (λ ())
  int ≟τ β⁼ n₂ = no (λ ())
  int ≟τ int = yes refl
  int ≟τ void ♯b₂ = no (λ ())
  int ≟τ ~ τ₂ = no (λ ())
  int ≟τ & ℓ₂ q₂ τ₂ = no (λ ())
  int ≟τ ∀[ Δ₂ ] Γ₂ = no (λ ())
  void ♯b₁ ≟τ β⁼ n₂ = no (λ ())
  void ♯b₁ ≟τ int = no (λ ())
  void ♯b₁ ≟τ void ♯b₂ with ♯b₁ ≟ ♯b₂
  void ♯b₁ ≟τ void .♯b₁ | yes refl = yes refl
  void ♯b₁ ≟τ void ♯b₂ | no ¬eq = no (λ eq → ¬eq (void-injective eq))
  void ♯b₁ ≟τ ~ τ₂ = no (λ ())
  void ♯b₁ ≟τ & ℓ₂ q₂ τ₂ = no (λ ())
  void ♯b₁ ≟τ ∀[ Δ₂ ] Γ₂ = no (λ ())
  ~ τ₁ ≟τ β⁼ n₂ = no (λ ())
  ~ τ₁ ≟τ int = no (λ ())
  ~ τ₁ ≟τ void ♯b₂ = no (λ ())
  ~ τ₁ ≟τ ~ τ₂ with τ₁ ≟τ τ₂
  ~ τ₁ ≟τ ~ .τ₁ | yes refl = yes refl
  ~ τ₁ ≟τ ~ τ₂ | no ¬eq = no (λ eq → ¬eq (~-injective eq))
  ~ τ₁ ≟τ & ℓ₂ q₂ τ₂ = no (λ ())
  ~ τ₁ ≟τ ∀[ Δ₂ ] Γ₂ = no (λ ())
  & ℓ₁ q₁ τ₁ ≟τ β⁼ n₂ = no (λ ())
  & ℓ₁ q₁ τ₁ ≟τ int = no (λ ())
  & ℓ₁ q₁ τ₁ ≟τ void ♯b₂ = no (λ ())
  & ℓ₁ q₁ τ₁ ≟τ ~ τ₂ = no (λ ())
  & ℓ₁ q₁ τ₁ ≟τ & ℓ₂ q₂ τ₂ with ℓ₁ ≟ℓ ℓ₂ | q₁ ≟q q₂ | τ₁ ≟τ τ₂
  & ℓ₁ q₁ τ₁ ≟τ & .ℓ₁ .q₁ .τ₁ | yes refl | yes refl | yes refl = yes refl
  & ℓ₁ q₁ τ₁ ≟τ & ℓ₂ q₂ τ₂ | no ¬eq | _ | _ = no (λ eq → ¬eq (proj₁ (&-injective eq)))
  & ℓ₁ q₁ τ₁ ≟τ & ℓ₂ q₂ τ₂ | _ | no ¬eq | _ = no (λ eq → ¬eq (proj₁ (proj₂ (&-injective eq))))
  & ℓ₁ q₁ τ₁ ≟τ & ℓ₂ q₂ τ₂ | _ | _ | no ¬eq = no (λ eq → ¬eq (proj₂ (proj₂ (&-injective eq))))
  & ℓ₁ q₁ τ₁ ≟τ ∀[ Δ₂ ] Γ₂ = no (λ ())
  (∀[ Δ₁ ] Γ₁) ≟τ β⁼ n₂ = no (λ ())
  (∀[ Δ₁ ] Γ₁) ≟τ int = no (λ ())
  (∀[ Δ₁ ] Γ₁) ≟τ void ♯b₂ = no (λ ())
  (∀[ Δ₁ ] Γ₁) ≟τ ~ τ₂ = no (λ ())
  (∀[ Δ₁ ] Γ₁) ≟τ & ℓ₂ q₂ τ₂ = no (λ ())
  (∀[ Δ₁ ] Γ₁) ≟τ (∀[ Δ₂ ] Γ₂) with Δ₁ ≟Δ Δ₂ | Γ₁ ≟Γ Γ₂
  (∀[ Δ₁ ] Γ₁) ≟τ (∀[ .Δ₁ ] .Γ₁) | yes refl | yes refl = yes refl
  (∀[ Δ₁ ] Γ₁) ≟τ (∀[ Δ₂ ] Γ₂) | no ¬eq | _ = no (λ eq → ¬eq (proj₁ (∀-injective eq)))
  (∀[ Δ₁ ] Γ₁) ≟τ (∀[ Δ₂ ] Γ₂) | _ | no ¬eq = no (λ eq → ¬eq (proj₂ (∀-injective eq)))

  _≟Γ_ : DecidableEq Register
  register sp₁ r0₁ r1₁ r2₁ ≟Γ register sp₂ r0₂ r1₂ r2₂ with sp₁ ≟σ sp₂ | r0₁ ≟τ r0₂ | r1₁ ≟τ r1₂ | r2₁ ≟τ r2₂
  register sp₁ r0₁ r1₁ r2₁ ≟Γ register .sp₁ .r0₁ .r1₁ .r2₁ | yes refl | yes refl | yes refl | yes refl = yes refl
  register sp₁ r0₁ r1₁ r2₁ ≟Γ register sp₂ r0₂ r1₂ r2₂ | no ¬eq | _ | _ | _ = no (λ eq → ¬eq (proj₁ (register-injective eq)))
  register sp₁ r0₁ r1₁ r2₁ ≟Γ register sp₂ r0₂ r1₂ r2₂ | _ | no ¬eq | _ | _ = no (λ eq → ¬eq (proj₁ (proj₂ (register-injective eq))))
  register sp₁ r0₁ r1₁ r2₁ ≟Γ register sp₂ r0₂ r1₂ r2₂ | _ | _ | no ¬eq | _ = no (λ eq → ¬eq (proj₁ (proj₂ (proj₂ (register-injective eq)))))
  register sp₁ r0₁ r1₁ r2₁ ≟Γ register sp₂ r0₂ r1₂ r2₂ | _ | _ | _ | no ¬eq = no (λ eq → ¬eq (proj₂ (proj₂ (proj₂ (register-injective eq)))))

  _≟ℓ_ : DecidableEq Lifetime
  α⁼ n₁ ≟ℓ α⁼ n₂ with n₁ ≟ n₂
  α⁼ n₁ ≟ℓ α⁼ .n₁ | yes refl = yes refl
  α⁼ n₁ ≟ℓ α⁼ n₂ | no ¬eq = no (λ eq → ¬eq (α⁼-injective eq))
  α⁼ n₁ ≟ℓ γ⁼ n₂ = no (λ ())
  α⁼ n₁ ≟ℓ static = no (λ ())
  γ⁼ n₁ ≟ℓ α⁼ n₂ = no (λ ())
  γ⁼ n₁ ≟ℓ γ⁼ n₂ with n₁ ≟ n₂
  γ⁼ n₁ ≟ℓ γ⁼ .n₁ | yes refl = yes refl
  γ⁼ n₁ ≟ℓ γ⁼ n₂ | no ¬eq = no (λ eq → ¬eq (γ⁼-injective eq))
  γ⁼ n₁ ≟ℓ static = no (λ ())
  static ≟ℓ α⁼ n₂ = no (λ ())
  static ≟ℓ γ⁼ n₂ = no (λ ())
  static ≟ℓ static = yes refl

  _≟q_ : DecidableEq Qualifier
  mut ≟q mut = yes refl
  mut ≟q imm = no (λ ())
  imm ≟q mut = no (λ ())
  imm ≟q imm = yes refl