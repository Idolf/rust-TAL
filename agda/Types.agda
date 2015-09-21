open import Data.Nat using (ℕ ; zero ; suc)

infixr 6 _,_ _∷_
infixr 5 _++_

infix 6 _≤a_/_  ∀[_]_
infix 4 _↓ₐ_≡_ _↓ᵥ_≡_ _⊏_

mutual
  -- Δ
  data Ctx : Set where
    Ɛ : Ctx
    _,_ : Ctx → CtxVal → Ctx

  -- a
  data CtxVal : Set where
    ρ      : CtxVal                               -- Assumption of a stack
    α      : Stack → CtxVal                       -- Assumption of a lifetime in a stack
    β      : Stack → ℕ → CtxVal                   -- Assumption of a type in a stack
    _≤a_/_ : Lifetime → Lifetime → Stack → CtxVal -- Assumption of a lifetime ordering

  -- σ
  data Stack : Set where
    nil  : Stack                   -- Empty stack
    _∷_ : StackVal → Stack → Stack -- Stack cons
    ρ⁼  : ℕ → Stack                -- Stack assumption

  -- v
  data StackVal : Set where
    type  : Type → StackVal
    γ     : StackVal

  -- τ
  data Type : Set where
    β⁼    : ℕ → Type
    int   : Type
    void  : ℕ → Type
    ~     : Type → Type
    &     : Lifetime → Qualifier → Type → Type
    ∀[_]_ : Ctx → Register → Type

  -- Γ
  record Register : Set where
    inductive
    constructor register
    field
      sp : Stack
      r0 r1 r2 : Type

  -- ℓ
  data Lifetime : Set where
    α⁼ : ℕ → Lifetime
    γ⁼  : ℕ → Lifetime
    static : Lifetime

  -- q
  data Qualifier : Set where
    mut : Qualifier
    imm : Qualifier

open Register public

data _↓ₐ_≡_ : Ctx → ℕ → CtxVal → Set where
  here  :
        ∀ {Δ a} →
    -----------------
    Δ , a ↓ₐ zero ≡ a

  there :
      ∀ {Δ a₁ a₂ ι} →
       Δ ↓ₐ ι ≡ a₁ →
    --------------------
    Δ , a₂ ↓ₐ suc ι ≡ a₁

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

_++_ : Ctx → Ctx → Ctx
Δ₁ ++ Ɛ = Δ₁
Δ₁ ++ Δ₂ , a = (Δ₁ ++ Δ₂) , a
