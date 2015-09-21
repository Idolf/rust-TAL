open import Data.Nat using (ℕ ; zero ; suc)

infix 7 _≤a_/_  ∀[_]_
infixr 6 _,_ _∷_
infixr 5 _++_

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

_++_ : Ctx → Ctx → Ctx
Δ₁ ++ Ɛ = Δ₁
Δ₁ ++ Δ₂ , a = (Δ₁ ++ Δ₂) , a

length : Ctx → ℕ
length Ɛ = zero
length (Δ , a) = suc (length Δ)
