module Types where

open import Data.Nat
open import Data.Unit
open import Data.Product
-- open import Data.Fin using (Fin)
-- open import Data.Vec
-- open import Data.Product
-- open import Relation.Binary.PropositionalEquality
-- -- open import Data.Graph.Acyclic


data Qualifier : Set where
  mut : Qualifier
  imm : Qualifier

mutual
  -- Contexts
  data Ctx : Set where
    Ɛ   : Ctx
    _,_ : (Δ : Ctx) → CtxVal Δ → Ctx

  data CtxVal : Ctx → Set where
    ρ    : ∀ {Δ}   → CtxVal Δ
    ℓ    : ∀ {Δ}   → ρ∈ Δ → CtxVal Δ
    α    : ∀ {Δ}   → ρ∈ Δ → ℕ → CtxVal Δ
    _≤ℓ_ : ∀ {Δ σ} → Lifetime Δ σ → Lifetime Δ σ → CtxVal Δ

  data ρ∈_ : Ctx → Set where
    here    : ∀ {Δ}          → ρ∈ (Δ , ρ)
    there   : ∀ {Δ v} → ρ∈ Δ → ρ∈ (Δ , v)

  data ℓ∈_/_ : (Δ : Ctx) → ρ∈ Δ → Set where
    here     : ∀ {Δ m}              → ℓ∈ (Δ , ℓ m) / (there m)
    there    : ∀ {Δ v m} → ℓ∈ Δ / m → ℓ∈ (Δ , v)   / (there m)

  data α∈_/_/_ : (Δ : Ctx) → ρ∈ Δ → ℕ → Set where
    here     : ∀ {Δ m n}                  → α∈ (Δ , α m n) / (there m) / n
    there    : ∀ {Δ v m n} → α∈ Δ / m / n → α∈ (Δ , v)     / (there m) / n

  _++_ : Ctx → Ctx → Ctx
  Δ ++ Ɛ = Δ
  Δ ++ (Δ' , v) = (Δ ++ Δ') , v

  -- Stacks
  data Stack : (Δ : Ctx) → Set where
    nil      : ∀ {Δ} → Stack Δ
    varstack : ∀ {Δ} → ρ∈ Δ → Stack Δ
    cons     : ∀ {Δ} → (σ : Stack Δ) → StackVal Δ σ → Stack Δ
  syntax cons σ v = v ∷ σ

  data StackVal : (Δ : Ctx) → (σ : Stack Δ) → Set where
    mark : ∀ {Δ σ} → StackVal Δ σ
    type : ∀ {Δ σ} → Type Δ σ → StackVal Δ σ

  data mark∈_ : ∀ {Δ} → Stack Δ → Set where
    here      : ∀ {Δ} {σ : Stack Δ} → mark∈ (mark ∷ σ)
    there     : ∀ {Δ} {σ : Stack Δ} {v} → mark∈ σ → mark∈ (v ∷ σ)

  -- Lifetimes
  data Lifetime : (Δ : Ctx) → (σ : Stack Δ) → Set where
    varlife  : ∀ {Δ l} → ℓ∈ Δ / l → Lifetime Δ (varstack l)
    concrete : ∀ {Δ σ} → mark∈ σ → Lifetime Δ σ
    static   : ∀ {Δ σ} → Lifetime Δ σ

  -- Types
  Type : (Δ : Ctx) → Stack Δ → Set
  Type Δ σ = Σ[ n ∈ ℕ ] Typeₙ Δ σ n

  data Typeₙ : (Δ : Ctx) → Stack Δ → ℕ → Set where
