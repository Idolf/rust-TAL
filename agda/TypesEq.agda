open import Types
open import Eq

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec ; [] ; _∷_)
import Data.Vec.Properties as VP
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.Core using (_≡_ ; refl ; Decidable)
open import Relation.Nullary using (yes ; no)
open import Function

,-injective : ∀ {Δ₁ Δ₂ a₁ a₂} → Δ₁ Types., a₁ ≡ Δ₂ , a₂ → Δ₁ ≡ Δ₂ × a₁ ≡ a₂
,-injective refl = refl , refl

α-injective : ∀ {σ₁ σ₂} → α σ₁ ≡ α σ₂ → σ₁ ≡ σ₂
α-injective refl = refl

β-injective : ∀ {σ₁ σ₂ ♯b₁ ♯b₂} → β σ₁ ♯b₁ ≡ β σ₂ ♯b₂ → σ₁ ≡ σ₂ × ♯b₁ ≡ ♯b₂
β-injective refl = refl , refl

≤a-injective : ∀ {ℓ₁₁ ℓ₁₂ ℓ₂₁ ℓ₂₂ σ₁ σ₂} → ℓ₁₁ ≤a ℓ₁₂ / σ₁ ≡ ℓ₂₁ ≤a ℓ₂₂ / σ₂ → ℓ₁₁ ≡ ℓ₂₁ × ℓ₁₂ ≡ ℓ₂₂ × σ₁ ≡ σ₂
≤a-injective refl = refl , (refl , refl)

∷-injective : ∀ {v₁ v₂ σ₁ σ₂} → v₁ Types.∷ σ₁ ≡ v₂ ∷ σ₂ → v₁ ≡ v₂ × σ₁ ≡ σ₂
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

register-injective : ∀ {sp₁ sp₂ regs₁ regs₂} → register sp₁ regs₁ ≡ register sp₂ regs₂ →
                       sp₁ ≡ sp₂ × regs₁ ≡ regs₂
register-injective refl = refl , refl

α⁼-injective : ∀ {n₁ n₂} → α⁼ n₁ ≡ α⁼ n₂ → n₁ ≡ n₂
α⁼-injective refl = refl

γ⁼-injective : ∀ {n₁ n₂} → γ⁼ n₁ ≡ γ⁼ n₂ → n₁ ≡ n₂
γ⁼-injective refl = refl



private
  infix 4 _≟Δ_ _≟a_ _≟σ_ _≟v_ _≟τ_ _≟Γ_ _≟ℓ_ _≟q_
  mutual
    _≟Δ_ : DecEqFun Ctx
    Ɛ ≟Δ Ɛ = yes refl
    Ɛ ≟Δ Δ₂ , a₁ = no (λ ())
    Δ₁ , a₁ ≟Δ Ɛ = no (λ ())
    Δ₁ , a₁ ≟Δ Δ₂ , a₂ with Δ₁ ≟Δ Δ₂ | a₁ ≟a a₂
    Δ  , a  ≟Δ .Δ , .a | yes refl | yes refl = yes refl
    Δ₁ , a₁ ≟Δ Δ₂ , a₂ | no ¬eq | _ = no (¬eq ∘ proj₁ ∘ ,-injective)
    Δ₁ , a₁ ≟Δ Δ₂ , a₂ | _ | no ¬eq = no (¬eq ∘ proj₂ ∘ ,-injective)

    _≟a_ : DecEqFun CtxVal
    ρ ≟a ρ = yes refl
    ρ ≟a α σ₂ = no (λ ())
    ρ ≟a β σ₂ ♯b₂ = no (λ ())
    ρ ≟a ℓ₂₁ ≤a ℓ₂₂ / σ₂ = no (λ ())
    α σ₁ ≟a ρ = no (λ ())
    α σ₁ ≟a α σ₂ with σ₁ ≟σ σ₂
    α σ  ≟a α .σ | yes refl = yes refl
    α σ₁ ≟a α σ₂ | no ¬eq = no (¬eq ∘ α-injective)
    α σ₁ ≟a β σ₂ ♯b₂ = no (λ ())
    α σ₁ ≟a ℓ₂₁ ≤a ℓ₂₂ / σ₂ = no (λ ())
    β σ₁ ♯b₁ ≟a ρ = no (λ ())
    β σ₁ ♯b₁ ≟a α σ₂ = no (λ ())
    β σ₁ ♯b₁ ≟a β σ₂ ♯b₂ with σ₁ ≟σ σ₂ | ♯b₁ ≟ ♯b₂
    β σ  ♯b  ≟a β .σ .♯b | yes refl | yes refl = yes refl
    β σ₁ ♯b₁ ≟a β σ₂ ♯b₂ | no ¬eq | _ = no (¬eq ∘ proj₁ ∘ β-injective)
    β σ₁ ♯b₁ ≟a β σ₂ ♯b₂ | _ | no ¬eq = no (¬eq ∘ proj₂ ∘ β-injective)
    β σ₁ ♯b₁ ≟a ℓ₂₂ ≤a ℓ₂₁ / σ₂ = no (λ ())
    ℓ₁₁ ≤a ℓ₁₂ / σ₁ ≟a ρ = no (λ ())
    ℓ₁₁ ≤a ℓ₁₂ / σ₁ ≟a α σ = no (λ ())
    ℓ₁₁ ≤a ℓ₁₂ / σ₁ ≟a β σ ♯b = no (λ ())
    ℓ₁₁ ≤a ℓ₁₂ / σ₁ ≟a ℓ₂₁ ≤a ℓ₂₂ / σ₂ with ℓ₁₁ ≟ℓ ℓ₂₁ | ℓ₁₂ ≟ℓ ℓ₂₂ | σ₁ ≟σ σ₂
    ℓ₁  ≤a ℓ₂  / σ  ≟a .ℓ₁ ≤a .ℓ₂ / .σ | yes refl | yes refl | yes refl = yes refl
    ℓ₁₁ ≤a ℓ₁₂ / σ₁ ≟a ℓ₂₁ ≤a ℓ₂₂ / σ₂ | no ¬eq | _ | _ = no (¬eq ∘ proj₁ ∘ ≤a-injective)
    ℓ₁₁ ≤a ℓ₁₂ / σ₁ ≟a ℓ₂₁ ≤a ℓ₂₂ / σ₂ | _ | no ¬eq | _ = no (¬eq ∘ proj₁ ∘ proj₂ ∘ ≤a-injective)
    ℓ₁₁ ≤a ℓ₁₂ / σ₁ ≟a ℓ₂₁ ≤a ℓ₂₂ / σ₂ | _ | _ | no ¬eq = no (¬eq ∘ proj₂ ∘ proj₂ ∘ ≤a-injective)

    _≟σ_ : DecEqFun Stack
    nil ≟σ nil = yes refl
    nil ≟σ v₂ ∷ σ₂ = no (λ ())
    nil ≟σ ρ⁼ n₂ = no (λ ())
    v₁ ∷ σ₁ ≟σ nil = no (λ ())
    v₁ ∷ σ₁ ≟σ v₂ ∷ σ₂ with v₁ ≟v v₂ | σ₁ ≟σ σ₂
    v  ∷ σ  ≟σ .v ∷ .σ | yes refl | yes refl = yes refl
    v₁ ∷ σ₁ ≟σ v₂ ∷ σ₂ | no ¬eq | _ = no (¬eq ∘ proj₁ ∘ ∷-injective)
    v₁ ∷ σ₁ ≟σ v₂ ∷ σ₂ | _ | no ¬eq = no (¬eq ∘ proj₂ ∘ ∷-injective)
    v₁ ∷ σ₁ ≟σ ρ⁼ n₂ = no (λ ())
    ρ⁼ n₁ ≟σ nil = no (λ ())
    ρ⁼ n₁ ≟σ v₂ ∷ σ₂ = no (λ ())
    ρ⁼ n₁ ≟σ ρ⁼ n₂ with n₁ ≟ n₂
    ρ⁼ n  ≟σ ρ⁼ .n | yes refl = yes refl
    ρ⁼ n₁ ≟σ ρ⁼ n₂ | no ¬eq = no (¬eq ∘ ρ⁼-injective)

    _≟v_ : DecEqFun StackVal
    type τ₁ ≟v type τ₂ with τ₁ ≟τ τ₂
    type τ  ≟v type .τ | yes refl = yes refl
    type τ₁ ≟v type τ₂ | no ¬eq = no (¬eq ∘ type-injective)
    type τ₁ ≟v γ = no (λ ())
    γ ≟v type τ₂ = no (λ ())
    γ ≟v γ = yes refl

    _≟τ_ : DecEqFun Type
    β⁼ n₁ ≟τ β⁼ n₂ with n₁ ≟ n₂
    β⁼ n  ≟τ β⁼ .n | yes refl = yes refl
    β⁼ n₁ ≟τ β⁼ n₂ | no ¬eq = no (¬eq ∘ β⁼-injective)
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
    void ♯b  ≟τ void .♯b | yes refl = yes refl
    void ♯b₁ ≟τ void ♯b₂ | no ¬eq = no (¬eq ∘ void-injective)
    void ♯b₁ ≟τ ~ τ₂ = no (λ ())
    void ♯b₁ ≟τ & ℓ₂ q₂ τ₂ = no (λ ())
    void ♯b₁ ≟τ ∀[ Δ₂ ] Γ₂ = no (λ ())
    ~ τ₁ ≟τ β⁼ n₂ = no (λ ())
    ~ τ₁ ≟τ int = no (λ ())
    ~ τ₁ ≟τ void ♯b₂ = no (λ ())
    ~ τ₁ ≟τ ~ τ₂ with τ₁ ≟τ τ₂
    ~ τ  ≟τ ~ .τ | yes refl = yes refl
    ~ τ₁ ≟τ ~ τ₂ | no ¬eq = no (¬eq ∘ ~-injective)
    ~ τ₁ ≟τ & ℓ₂ q₂ τ₂ = no (λ ())
    ~ τ₁ ≟τ ∀[ Δ₂ ] Γ₂ = no (λ ())
    & ℓ₁ q₁ τ₁ ≟τ β⁼ n₂ = no (λ ())
    & ℓ₁ q₁ τ₁ ≟τ int = no (λ ())
    & ℓ₁ q₁ τ₁ ≟τ void ♯b₂ = no (λ ())
    & ℓ₁ q₁ τ₁ ≟τ ~ τ₂ = no (λ ())
    & ℓ₁ q₁ τ₁ ≟τ & ℓ₂ q₂ τ₂ with ℓ₁ ≟ℓ ℓ₂ | q₁ ≟q q₂ | τ₁ ≟τ τ₂
    & ℓ  q  τ  ≟τ & .ℓ .q .τ | yes refl | yes refl | yes refl = yes refl
    & ℓ₁ q₁ τ₁ ≟τ & ℓ₂ q₂ τ₂ | no ¬eq | _ | _ = no (¬eq ∘ proj₁ ∘ &-injective)
    & ℓ₁ q₁ τ₁ ≟τ & ℓ₂ q₂ τ₂ | _ | no ¬eq | _ = no (¬eq ∘ proj₁ ∘ proj₂ ∘ &-injective)
    & ℓ₁ q₁ τ₁ ≟τ & ℓ₂ q₂ τ₂ | _ | _ | no ¬eq = no (¬eq ∘ proj₂ ∘ proj₂ ∘ &-injective)
    & ℓ₁ q₁ τ₁ ≟τ ∀[ Δ₂ ] Γ₂ = no (λ ())
    ∀[ Δ₁ ] Γ₁ ≟τ β⁼ n₂ = no (λ ())
    ∀[ Δ₁ ] Γ₁ ≟τ int = no (λ ())
    ∀[ Δ₁ ] Γ₁ ≟τ void ♯b₂ = no (λ ())
    ∀[ Δ₁ ] Γ₁ ≟τ ~ τ₂ = no (λ ())
    ∀[ Δ₁ ] Γ₁ ≟τ & ℓ₂ q₂ τ₂ = no (λ ())
    ∀[ Δ₁ ] Γ₁ ≟τ ∀[ Δ₂ ] Γ₂ with Δ₁ ≟Δ Δ₂ | Γ₁ ≟Γ Γ₂
    ∀[ Δ  ] Γ  ≟τ ∀[ .Δ ] .Γ | yes refl | yes refl = yes refl
    ∀[ Δ₁ ] Γ₁ ≟τ ∀[ Δ₂ ] Γ₂ | no ¬eq | _ = no (¬eq ∘ proj₁ ∘ ∀-injective)
    ∀[ Δ₁ ] Γ₁ ≟τ ∀[ Δ₂ ] Γ₂ | _ | no ¬eq = no (¬eq ∘ proj₂ ∘ ∀-injective)

    _≟τs_ : ∀ {m} → DecEqFun (Vec Type m)
    [] ≟τs [] = yes refl
    (τ₁ ∷ τs₁) ≟τs (τ₂ ∷ τs₂) with τ₁ ≟τ τ₂ | τs₁ ≟τs τs₂
    (τ  ∷ τs ) ≟τs (.τ ∷ .τs) | yes refl | yes refl = yes refl
    (τ₁ ∷ τs₁) ≟τs (τ₂ ∷ τs₂) | no ¬eq | _ = no (¬eq ∘ proj₁ ∘ VP.∷-injective)
    (τ₁ ∷ τs₁) ≟τs (τ₂ ∷ τs₂) | _ | no ¬eq = no (¬eq ∘ proj₂ ∘ VP.∷-injective)

    _≟Γ_ : DecEqFun Register
    register sp₁ regs₁ ≟Γ register sp₂ regs₂ with sp₁ ≟σ sp₂ | regs₁ ≟τs regs₂
    register sp  regs  ≟Γ register .sp .regs | yes refl | yes refl = yes refl
    register sp₁ regs₁ ≟Γ register sp₂ regs₂ | no ¬eq | _ = no (¬eq ∘ proj₁ ∘ register-injective)
    register sp₁ regs₁ ≟Γ register sp₂ resg₂ | _ | no ¬eq = no (¬eq ∘ proj₂ ∘ register-injective)

    _≟ℓ_ : DecEqFun Lifetime
    α⁼ n₁ ≟ℓ α⁼ n₂ with n₁ ≟ n₂
    α⁼ n  ≟ℓ α⁼ .n | yes refl = yes refl
    α⁼ n₁ ≟ℓ α⁼ n₂ | no ¬eq = no (¬eq ∘ α⁼-injective)
    α⁼ n₁ ≟ℓ γ⁼ n₂ = no (λ ())
    α⁼ n₁ ≟ℓ static = no (λ ())
    γ⁼ n₁ ≟ℓ α⁼ n₂ = no (λ ())
    γ⁼ n₁ ≟ℓ γ⁼ n₂ with n₁ ≟ n₂
    γ⁼ n  ≟ℓ γ⁼ .n | yes refl = yes refl
    γ⁼ n₁ ≟ℓ γ⁼ n₂ | no ¬eq = no (¬eq ∘ γ⁼-injective)
    γ⁼ n₁ ≟ℓ static = no (λ ())
    static ≟ℓ α⁼ n₂ = no (λ ())
    static ≟ℓ γ⁼ n₂ = no (λ ())
    static ≟ℓ static = yes refl

    _≟q_ : DecEqFun Qualifier
    mut ≟q mut = yes refl
    mut ≟q imm = no (λ ())
    imm ≟q mut = no (λ ())
    imm ≟q imm = yes refl

instance
  Ctx-dec-eq : DecEq Ctx
  Ctx-dec-eq = mkEq _≟Δ_

  CtxVal-dec-eq : DecEq CtxVal
  CtxVal-dec-eq = mkEq _≟a_

  Stack-dec-eq : DecEq Stack
  Stack-dec-eq = mkEq _≟σ_

  StackVal-dec-eq : DecEq StackVal
  StackVal-dec-eq = mkEq _≟v_

  Type-dec-eq : DecEq Type
  Type-dec-eq = mkEq _≟τ_

  Register-dec-eq : DecEq Register
  Register-dec-eq = mkEq _≟Γ_

  Lifetime-dec-eq : DecEq Lifetime
  Lifetime-dec-eq = mkEq _≟ℓ_
