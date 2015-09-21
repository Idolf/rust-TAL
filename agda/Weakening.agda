open import Types

open import Data.Nat using (ℕ ; suc ; zero ; _+_ ; _<_ ; _≥_ ; _≤_ ; z≤n ; s≤s)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)
import Data.Nat.Properties as P
import Algebra as A
module R = A.CommutativeSemiring P.commutativeSemiring
module M = A.CommutativeMonoid R.+-commutativeMonoid renaming (_∙_ to _+_ ; _≈_ to _≡_)

infix 4 _↓ₐ_≡_ _↓ᵥ_≡_ _⊏_

record Weaken {a} (A : Set a) : Set a where
  field
    weaken : A → ℕ → ℕ → A
    weaken-comp : ∀ {pos pos' e₁ e₂} a → pos' ≤ e₁ → weaken (weaken a pos e₁) (pos' + pos) e₂ ≡ weaken a pos (e₁ + e₂)
    weaken-id : ∀ {pos} a → weaken a pos 0 ≡ a
  weakenʰ : A → Ctx → Ctx → A
  weakenʰ a Δ₂ Δₑ = weaken a (length Δ₂) (length Δₑ)

  weaken¹ : A → A
  weaken¹ a = weaken a 0 1
open Weaken {{...}} public

private
  weaken-ℕ : ℕ → ℕ → ℕ → ℕ
  weaken-ℕ v zero e = v + e
  weaken-ℕ zero (suc pos) e = zero
  weaken-ℕ (suc v) (suc pos) e = suc (weaken-ℕ v pos e)

  weaken-ℕ-< : ∀ x pos e → x < pos → weaken-ℕ x pos e ≡ x
  weaken-ℕ-< x zero e ()
  weaken-ℕ-< zero (suc pos) e lt = refl
  weaken-ℕ-< (suc x) (suc pos) e (s≤s lt) = cong suc (weaken-ℕ-< x pos e lt)

  weaken-ℕ-≥ : ∀ x pos e → x ≥ pos → weaken-ℕ x pos e ≡ x + e
  weaken-ℕ-≥ x zero e ge = refl
  weaken-ℕ-≥ zero (suc pos) e ()
  weaken-ℕ-≥ (suc x) (suc pos) e (s≤s ge) = cong suc (weaken-ℕ-≥ x pos e ge)

  data foo (n m : ℕ) : Set where
    foo< : n < m → foo n m
    foo≥ : n ≥ m → foo n m

  bar : ∀ n m → foo n m
  bar n zero = foo≥ z≤n
  bar zero (suc m) = foo< (s≤s z≤n)
  bar (suc n) (suc m) with bar n m
  bar (suc n) (suc m) | foo< x = foo< (s≤s x)
  bar (suc n) (suc m) | foo≥ x = foo≥ (s≤s x)

  baz : ∀ {x y z q} → x ≤ z → y ≤ q → x + y ≤ z + q
  baz {z = z} z≤n ge₂ = P.≤-steps z ge₂
  baz (s≤s ge₁) ge₂ = s≤s (baz ge₁ ge₂)

  weaken-ℕ-comp : ∀ pos pos' e₁ e₂ x → pos' ≤ e₁ → weaken-ℕ (weaken-ℕ x pos e₁) (pos' + pos) e₂ ≡ weaken-ℕ x pos (e₁ + e₂)
  weaken-ℕ-comp pos pos' e₁ e₂ x lt with bar x pos
  weaken-ℕ-comp pos pos' e₁ e₂ x lt | foo< lt'
    rewrite weaken-ℕ-< x pos e₁ lt' |
            weaken-ℕ-< x pos (e₁ + e₂) lt' |
            weaken-ℕ-< x (pos' + pos) e₂ (P.≤-steps pos' lt') = refl
  weaken-ℕ-comp pos pos' e₁ e₂ x lt | foo≥ ge
    rewrite weaken-ℕ-≥ x pos e₁ ge |
            weaken-ℕ-≥ x pos (e₁ + e₂) ge |
            M.comm pos' pos |
            weaken-ℕ-≥ (x + e₁) (pos + pos') e₂ (baz ge lt) |
            M.assoc x e₁ e₂ = refl

  weaken-ℕ-id : ∀ pos a → weaken-ℕ a pos 0 ≡ a
  weaken-ℕ-id zero zero = refl
  weaken-ℕ-id zero (suc n) = M.comm (suc n) 0
  weaken-ℕ-id (suc pos) zero = refl
  weaken-ℕ-id (suc pos) (suc n) = cong suc (weaken-ℕ-id pos n)

instance
  Weaken-ℕ : Weaken ℕ
  Weaken-ℕ = record { weaken = weaken-ℕ ; weaken-comp = λ {pos} {pos'} {e₁} {e₂} → weaken-ℕ-comp pos pos' e₁ e₂ ; weaken-id = λ {pos} → weaken-ℕ-id pos }

mutual
  weaken-Ctx : Ctx → ℕ → Ctx
  weaken-Ctx Ɛ e = Ɛ
  weaken-Ctx (Δ , a) e = weaken-Ctx Δ e , weaken-CtxVal a (length Δ) e

  weaken-CtxVal : CtxVal → ℕ → ℕ → CtxVal
  weaken-CtxVal ρ pos e = ρ
  weaken-CtxVal (α σ) pos e = α (weaken-Stack σ pos e)
  weaken-CtxVal (β σ ♯b) pos e = β (weaken-Stack σ pos e) ♯b
  weaken-CtxVal (ℓ₁ ≤a ℓ₂ / σ) pos e = weaken-Lifetime ℓ₁ pos e ≤a weaken-Lifetime ℓ₂ pos e / weaken-Stack σ pos e

  weaken1 : CtxVal → CtxVal
  weaken1 a = weaken-CtxVal a 0 1

  weaken-Stack : Stack → ℕ → ℕ → Stack
  weaken-Stack nil pos e = nil
  weaken-Stack (v ∷ σ) pos e = weaken-StackVal v pos e ∷ weaken-Stack σ pos e
  weaken-Stack (ρ⁼ ι) pos e = ρ⁼ (weaken ι pos e)

  weaken-StackVal : StackVal → ℕ → ℕ → StackVal
  weaken-StackVal (type τ) pos e = type (weaken-Type τ pos e)
  weaken-StackVal γ pos e = γ

  weaken-Type : Type → ℕ → ℕ → Type
  weaken-Type (β⁼ ι) pos e = β⁼ (weaken ι pos e)
  weaken-Type int pos e = int
  weaken-Type (void ♯b) pos e = void ♯b
  weaken-Type (~ τ) pos e = ~ (weaken-Type τ pos e)
  weaken-Type (& ℓ q τ) pos e = & (weaken-Lifetime ℓ pos e) q (weaken-Type τ pos e)
  weaken-Type (∀[ Δ ] Γ) pos e = ∀[ Δ ] weaken-Register Γ (pos + length Δ) e

  weaken-Register : Register → ℕ → ℕ → Register
  weaken-Register (register sp r0 r1 r2) pos e = register (weaken-Stack sp pos e) (weaken-Type r0 pos e) (weaken-Type r1 pos e) (weaken-Type r2 pos e)

  weaken-Lifetime : Lifetime → ℕ → ℕ → Lifetime
  weaken-Lifetime (α⁼ ι) pos e = α⁼ (weaken ι pos e)
  weaken-Lifetime (γ⁼ ι) pos e = γ⁼ ι
  weaken-Lifetime static pos e = static

data _↓ₐ_≡_ : Ctx → ℕ → CtxVal → Set where
  here  :
        ∀ {Δ a} →
    -----------------
    Δ , a ↓ₐ zero ≡ a

  there :
          ∀ {Δ a₁ a₂ ι} →
           Δ ↓ₐ ι ≡ a₁ →
    ----------------------------
    Δ , a₂ ↓ₐ suc ι ≡ weaken1 a₁

data _↓ᵥ_≡_ : Stack → ℕ → StackVal → Set where
  here :
         ∀ {σ v} →
    -----------------
    v ∷ σ ↓ᵥ zero ≡ v

  there :
       ∀ {σ v₁ v₂ ι} →
        σ ↓ᵥ ι ≡ v₁ →
    --------------------
    v₂ ∷ σ ↓ᵥ suc ι ≡ v₁

data _⊏_ : Stack → Stack → Set where
  here  : ∀ {σ}      → σ ⊏ σ
  there : ∀ {σ σ' v} → σ ⊏ σ' → σ ⊏ v ∷ σ'
