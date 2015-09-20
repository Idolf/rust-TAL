module Types where

open import Data.Nat
open import Data.Product
open import Data.Fin hiding (_+_)
open import Data.List
open import Data.List.Properties
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Core using (_≡_; refl)

mutual
  -- Δ
  Ctx : Set
  Ctx = List CtxVal

  -- a
  data CtxVal : Set where
    ρ    : CtxVal                       -- Assumption of a stack
    α    : Stack → CtxVal               -- Assumption of a lifetime in a stack
    β    : Stack → ℕ → CtxVal           -- Assumption of a type in a stack
    _≤ℓ_ : Lifetime → Lifetime → CtxVal -- Assumption of a lifetime ordering

  -- σ
  data Stack : Set where
    []  : Stack                    -- Empty stack
    _∷ₛ_ : StackVal → Stack → Stack -- Stack cons
    ρ⁼  : ℕ → Stack                -- Stack assumption

  -- v
  data StackVal : Set where
    type  : Type → StackVal
    γ     : StackVal

  -- τ
  data Type : Set where
    β⁼   : ℕ → Type
    int  : Type
    void : ℕ → Type
    ~    : Type → Type
    &    : Lifetime → Qualifier → Type → Type

  -- ℓ
  data Lifetime : Set where
    α⁼ : ℕ → Lifetime
    γ⁼  : ℕ → Lifetime
    static : Lifetime

  -- q
  data Qualifier : Set where
    mut : Qualifier
    imm : Qualifier

data Δ-lookup : Ctx → ℕ → CtxVal → Set where
  here  : ∀ {Δ a}      → Δ-lookup (a ∷ Δ) zero a
  there : ∀ {Δ a a' n} → Δ-lookup Δ n a → Δ-lookup (a' ∷ Δ) (suc n) a

data σ-lookup : Stack → ℕ → StackVal → Set where
  here  : ∀ {σ v}      → σ-lookup (v ∷ₛ σ) zero v
  there : ∀ {σ v v' n} → σ-lookup σ n v → σ-lookup (v' ∷ₛ σ) (suc n) v

data IsStackTail : Stack → Stack → Set where
  here  : ∀ {σ}      → IsStackTail σ σ
  there : ∀ {σ σ' v} → IsStackTail σ σ' → IsStackTail σ (v ∷ₛ σ')

mutual
  data IsValidCtx : Ctx → Set where
    valid-[] : IsValidCtx []
    valid-∷  : ∀ {Δ a} → IsValidCtx Δ → IsValidCtxVal Δ a → IsValidCtx (a ∷ Δ)

  data IsValidCtxVal (Δ : Ctx) : CtxVal → Set where
    valid-ρ  : IsValidCtxVal Δ ρ
    valid-α  : ∀ {σ}   → IsValidStack Δ σ → IsValidCtxVal Δ (α σ)
    valid-β  : ∀ {σ n} → IsValidStack Δ σ → IsValidCtxVal Δ (β σ n)
    valid-≤ℓ : ∀ {σ ℓ₁ ℓ₂} → IsValidLifetime Δ σ ℓ₁ → IsValidLifetime Δ σ ℓ₂ → IsValidCtxVal Δ (ℓ₁ ≤ℓ ℓ₂)

  data IsValidStack (Δ : Ctx) : Stack → Set where
    valid-[] : IsValidStack Δ []
    valid-∷  : ∀ {σ v} → IsValidStack Δ σ → IsValidStackVal Δ σ v → IsValidStack Δ (v ∷ₛ σ)
    valid-ρ⁼ : ∀ {n} → Δ-lookup Δ n ρ → IsValidStack Δ (ρ⁼ n)

  data IsValidStackVal (Δ : Ctx) (σ : Stack) : StackVal → Set where
    valid-type  : ∀ {τ n} → IsValidType Δ σ τ n → IsValidStackVal Δ σ (type τ)
    valid-γ     : IsValidStackVal Δ σ γ

  data IsValidType (Δ : Ctx) (σ : Stack) : Type → ℕ → Set where
    valid-β⁼     : ∀ {σ' n ♯b}  → Δ-lookup Δ n (β σ' ♯b) → IsStackTail σ' σ → IsValidType Δ σ (β⁼ n) ♯b
    valid-int    : IsValidType Δ σ int 4
    valid-void   : ∀ {♯b}       → IsValidType Δ σ (void ♯b) ♯b
    valid-~      : ∀ {τ ♯b}     → IsValidType Δ σ τ ♯b → IsValidType Δ σ (~ τ) 4
    valid-&      : ∀ {ℓ q τ ♯b} → IsValidLifetime Δ σ ℓ → IsValidType Δ σ τ ♯b → IsValidType Δ σ (& ℓ q τ) 4

  data IsValidLifetime (Δ : Ctx) (σ : Stack) : Lifetime → Set where
    valid-α⁼     : ∀ {σ' n} → Δ-lookup Δ n (α σ') → IsStackTail σ' σ → IsValidLifetime Δ σ (α⁼ n)
    valid-γ⁼     : ∀ {n}    → σ-lookup σ n γ → IsValidLifetime Δ σ (γ⁼ n)

α-injective : ∀ {σ₁ σ₂} → α σ₁ ≡ α σ₂ → σ₁ ≡ σ₂
α-injective refl = refl

β-injective : ∀ {σ₁ σ₂ ♯b₁ ♯b₂} → β σ₁ ♯b₁ ≡ β σ₂ ♯b₂ → σ₁ ≡ σ₂ × ♯b₁ ≡ ♯b₂
β-injective refl = refl , refl

≤ℓ-injective : ∀ {ℓ₁₁ ℓ₁₂ ℓ₂₁ ℓ₂₂} → (ℓ₁₁ ≤ℓ ℓ₁₂) ≡ (ℓ₂₁ ≤ℓ ℓ₂₂) → ℓ₁₁ ≡ ℓ₂₁ × ℓ₁₂ ≡ ℓ₂₂
≤ℓ-injective refl = refl , refl

∷ₛ-injective : ∀ {v₁ v₂ σ₁ σ₂} → (v₁ ∷ₛ σ₁) ≡ (v₂ ∷ₛ σ₂) → v₁ ≡ v₂ × σ₁ ≡ σ₂
∷ₛ-injective refl = refl , refl

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
&-injective refl = refl , refl , refl

α⁼-injective : ∀ {n₁ n₂} → α⁼ n₁ ≡ α⁼ n₂ → n₁ ≡ n₂
α⁼-injective refl = refl

γ⁼-injective : ∀ {n₁ n₂} → γ⁼ n₁ ≡ γ⁼ n₂ → n₁ ≡ n₂
γ⁼-injective refl = refl

mutual
  _≟Δ_ : (Δ₁ Δ₂ : Ctx) → Dec (Δ₁ ≡ Δ₂)
  []        ≟Δ []        = yes refl
  []        ≟Δ (_ ∷ _)   = no (λ ())
  (_ ∷ _)   ≟Δ []        = no (λ ())
  (a₁ ∷ Δ₁) ≟Δ (a₂ ∷ Δ₂) with a₁ ≟a a₂ | Δ₁ ≟Δ Δ₂
  (a₁ ∷ Δ₁) ≟Δ (.a₁ ∷ .Δ₁) | yes refl | yes refl = yes refl
  (a₁ ∷ Δ₁) ≟Δ (a₂ ∷ Δ₂) | no ¬p | _ = no (λ p → ¬p (proj₁ (∷-injective p)))
  (a₁ ∷ Δ₁) ≟Δ (a₂ ∷ Δ₂) | _ | no ¬p = no (λ p → ¬p (proj₂ (∷-injective p)))

  _≟a_ : (a₁ a₂ : CtxVal) → Dec (a₁ ≡ a₂)
  ρ            ≟a ρ            = yes refl
  ρ            ≟a α σ₂         = no (λ ())
  ρ            ≟a β σ₂ ♯b₂     = no (λ ())
  ρ            ≟a (ℓ₂₁ ≤ℓ ℓ₂₂) = no (λ ())
  α σ₁         ≟a ρ            = no (λ ())
  α σ₁         ≟a α σ₂ with σ₁ ≟σ σ₂
  α σ₁         ≟a α .σ₁        | yes refl = yes refl
  α σ₁         ≟a α σ₂         | no ¬p = no (λ p → ¬p (α-injective p))
  α σ₁         ≟a β σ₂ ♯b₂     = no (λ ())
  α σ₁         ≟a (ℓ₂₁ ≤ℓ ℓ₂₂) = no (λ ())
  β σ₁ ♯b₁     ≟a ρ            = no (λ ())
  β σ₁ ♯b₁     ≟a α σ₂         = no (λ ())
  β σ₁ ♯b₁     ≟a β σ₂ ♯b₂ with σ₁ ≟σ σ₂ | ♯b₁ ≟ ♯b₂
  β σ₁ ♯b₁     ≟a β .σ₁ .♯b₁   | yes refl | yes refl = yes refl
  β σ₁ ♯b₁     ≟a β σ₂ ♯b₂     | no ¬p | _ = no (λ p → ¬p (proj₁ (β-injective p)))
  β σ₁ ♯b₁     ≟a β σ₂ ♯b₂     | _ | no ¬p = no (λ p → ¬p (proj₂ (β-injective p)))
  β σ₁ ♯b₁     ≟a (ℓ₂₂ ≤ℓ ℓ₂₁) = no (λ ())
  (ℓ₁₁ ≤ℓ ℓ₁₂) ≟a ρ            = no (λ ())
  (ℓ₁₁ ≤ℓ ℓ₁₂) ≟a α σ          = no (λ ())
  (ℓ₁₁ ≤ℓ ℓ₁₂) ≟a β σ ♯b       = no (λ ())
  (ℓ₁₁ ≤ℓ ℓ₁₂) ≟a (ℓ₂₁ ≤ℓ ℓ₂₂) with ℓ₁₁ ≟ℓ ℓ₂₁ | ℓ₁₂ ≟ℓ ℓ₂₂
  (ℓ₁₁ ≤ℓ ℓ₁₂) ≟a (.ℓ₁₁ ≤ℓ .ℓ₁₂) | yes refl | yes refl = yes refl
  (ℓ₁₁ ≤ℓ ℓ₁₂) ≟a (ℓ₂₁ ≤ℓ ℓ₂₂)   | no ¬p | _ = no (λ p → ¬p (proj₁ (≤ℓ-injective p)))
  (ℓ₁₁ ≤ℓ ℓ₁₂) ≟a (ℓ₂₁ ≤ℓ ℓ₂₂)   | _ | no ¬p = no (λ p → ¬p (proj₂ (≤ℓ-injective p)))

  _≟σ_ : (σ₁ σ₂ : Stack) → Dec (σ₁ ≡ σ₂)
  [] ≟σ [] = yes refl
  [] ≟σ (v₂ ∷ₛ σ₂) = no (λ ())
  [] ≟σ ρ⁼ n₂ = no (λ ())
  (v₁ ∷ₛ σ₁) ≟σ [] = no (λ ())
  (v₁ ∷ₛ σ₁) ≟σ (v₂ ∷ₛ σ₂) with v₁ ≟v v₂ | σ₁ ≟σ σ₂
  (v₁ ∷ₛ σ₁) ≟σ (.v₁ ∷ₛ .σ₁) | yes refl | yes refl = yes refl
  (v₁ ∷ₛ σ₁) ≟σ (v₂ ∷ₛ σ₂) | no ¬p | _ = no (λ p → ¬p (proj₁ (∷ₛ-injective p)))
  (v₁ ∷ₛ σ₁) ≟σ (v₂ ∷ₛ σ₂) | _ | no ¬p = no (λ p → ¬p (proj₂ (∷ₛ-injective p)))
  (v₁ ∷ₛ σ₁) ≟σ ρ⁼ n₂ = no (λ ())
  ρ⁼ n₁ ≟σ [] = no (λ ())
  ρ⁼ n₁ ≟σ (v₂ ∷ₛ σ₂) = no (λ ())
  ρ⁼ n₁ ≟σ ρ⁼ n₂ with n₁ ≟ n₂
  ρ⁼ n₁ ≟σ ρ⁼ .n₁ | yes refl = yes refl
  ρ⁼ n₁ ≟σ ρ⁼ n₂ | no ¬p = no (λ p → ¬p (ρ⁼-injective p))

  _≟v_ : (v₁ v₂ : StackVal) → Dec (v₁ ≡ v₂)
  type τ₁ ≟v type τ₂ with τ₁ ≟τ τ₂
  type τ₁ ≟v type .τ₁ | yes refl = yes refl
  type τ₁ ≟v type τ₂ | no ¬p = no (λ p → ¬p (type-injective p))
  type τ₁ ≟v γ = no (λ ())
  γ ≟v type τ₂ = no (λ ())
  γ ≟v γ = yes refl

  _≟τ_ : (τ₁ τ₂ : Type) → Dec (τ₁ ≡ τ₂)
  β⁼ n₁ ≟τ β⁼ n₂ with n₁ ≟ n₂
  β⁼ n₁ ≟τ β⁼ .n₁ | yes refl = yes refl
  β⁼ n₁ ≟τ β⁼ n₂ | no ¬p = no (λ p → ¬p (β⁼-injective p))
  β⁼ n₁ ≟τ int = no (λ ())
  β⁼ n₁ ≟τ void ♯b₂ = no (λ ())
  β⁼ n₁ ≟τ ~ τ₂ = no (λ ())
  β⁼ n₁ ≟τ & ℓ₂ q₂ τ₂ = no (λ ())
  int ≟τ β⁼ n₂ = no (λ ())
  int ≟τ int = yes refl
  int ≟τ void ♯b₂ = no (λ ())
  int ≟τ ~ τ₂ = no (λ ())
  int ≟τ & ℓ₂ q₂ τ₂ = no (λ ())
  void ♯b₁ ≟τ β⁼ n₂ = no (λ ())
  void ♯b₁ ≟τ int = no (λ ())
  void ♯b₁ ≟τ void ♯b₂ with ♯b₁ ≟ ♯b₂
  void ♯b₁ ≟τ void .♯b₁ | yes refl = yes refl
  void ♯b₁ ≟τ void ♯b₂ | no ¬p = no (λ p → ¬p (void-injective p))
  void ♯b₁ ≟τ ~ τ₂ = no (λ ())
  void ♯b₁ ≟τ & ℓ₂ q₂ τ₂ = no (λ ())
  ~ τ₁ ≟τ β⁼ n₂ = no (λ ())
  ~ τ₁ ≟τ int = no (λ ())
  ~ τ₁ ≟τ void ♯b₂ = no (λ ())
  ~ τ₁ ≟τ ~ τ₂ with τ₁ ≟τ τ₂
  ~ τ₁ ≟τ ~ .τ₁ | yes refl = yes refl
  ~ τ₁ ≟τ ~ τ₂ | no ¬p = no (λ p → ¬p (~-injective p))
  ~ τ₁ ≟τ & ℓ₂ q₂ τ₂ = no (λ ())
  & ℓ₁ q₁ τ₁ ≟τ β⁼ n₂ = no (λ ())
  & ℓ₁ q₁ τ₁ ≟τ int = no (λ ())
  & ℓ₁ q₁ τ₁ ≟τ void ♯b₂ = no (λ ())
  & ℓ₁ q₁ τ₁ ≟τ ~ τ₂ = no (λ ())
  & ℓ₁ q₁ τ₁ ≟τ & ℓ₂ q₂ τ₂ with ℓ₁ ≟ℓ ℓ₂ | q₁ ≟q q₂ | τ₁ ≟τ τ₂
  & ℓ₁ q₁ τ₁ ≟τ & .ℓ₁ .q₁ .τ₁ | yes refl | yes refl | yes refl = yes refl
  & ℓ₁ q₁ τ₁ ≟τ & ℓ₂ q₂ τ₂ | no ¬p | _ | _ = no (λ p → ¬p (proj₁ (&-injective p)))
  & ℓ₁ q₁ τ₁ ≟τ & ℓ₂ q₂ τ₂ | _ | no ¬p | _ = no (λ p → ¬p (proj₁ (proj₂ (&-injective p))))
  & ℓ₁ q₁ τ₁ ≟τ & ℓ₂ q₂ τ₂ | _ | _ | no ¬p = no (λ p → ¬p (proj₂ (proj₂ (&-injective p))))

  _≟ℓ_ : (ℓ₁ ℓ₂ : Lifetime) → Dec (ℓ₁ ≡ ℓ₂)
  α⁼ n₁ ≟ℓ α⁼ n₂ with n₁ ≟ n₂
  α⁼ n₁ ≟ℓ α⁼ .n₁ | yes refl = yes refl
  α⁼ n₁ ≟ℓ α⁼ n₂ | no ¬p = no (λ p → ¬p (α⁼-injective p))
  α⁼ n₁ ≟ℓ γ⁼ n₂ = no (λ ())
  α⁼ n₁ ≟ℓ static = no (λ ())
  γ⁼ n₁ ≟ℓ α⁼ n₂ = no (λ ())
  γ⁼ n₁ ≟ℓ γ⁼ n₂ with n₁ ≟ n₂
  γ⁼ n₁ ≟ℓ γ⁼ .n₁ | yes refl = yes refl
  γ⁼ n₁ ≟ℓ γ⁼ n₂ | no ¬p = no (λ p → ¬p (γ⁼-injective p))
  γ⁼ n₁ ≟ℓ static = no (λ ())
  static ≟ℓ α⁼ n₂ = no (λ ())
  static ≟ℓ γ⁼ n₂ = no (λ ())
  static ≟ℓ static = yes refl

  _≟q_ : (q₁ q₂ : Qualifier) → Dec (q₁ ≡ q₂)
  mut ≟q mut = yes refl
  mut ≟q imm = no (λ ())
  imm ≟q mut = no (λ ())
  imm ≟q imm = yes refl


Δ-lookup-unique : ∀ {Δ n a a'} → Δ-lookup Δ n a → Δ-lookup Δ n a' → a ≡ a'
Δ-lookup-unique here here = refl
Δ-lookup-unique (there l₁) (there l₂) = Δ-lookup-unique l₁ l₂

σ-lookup-unique : ∀ {σ n v v'} → σ-lookup σ n v → σ-lookup σ n v' → v ≡ v'
σ-lookup-unique here here = refl
σ-lookup-unique (there l₁) (there l₂) = σ-lookup-unique l₁ l₂

Δ-lookup-dec : ∀ Δ n → Dec (Σ[ a ∈ CtxVal ] Δ-lookup Δ n a)
Δ-lookup-dec [] n = no λ { (a , ()) }
Δ-lookup-dec (a ∷ Δ) zero = yes (a , here)
Δ-lookup-dec (a ∷ Δ) (suc n) with Δ-lookup-dec Δ n
Δ-lookup-dec (a ∷ Δ) (suc n) | yes (a' , l) = yes (a' , there l)
Δ-lookup-dec (a ∷ Δ) (suc n) | no ¬l = no (λ { (a , there l) → ¬l (a , l)})

σ-lookup-dec : ∀ σ n → Dec (Σ[ v ∈ StackVal ] σ-lookup σ n v)
σ-lookup-dec [] n = no λ { (v , ()) }
σ-lookup-dec (ρ⁼ _) n = no λ { (v , ()) }
σ-lookup-dec (v ∷ₛ σ) zero = yes (v , here)
σ-lookup-dec (v ∷ₛ σ) (suc n) with σ-lookup-dec σ n
σ-lookup-dec (v ∷ₛ σ) (suc n) | yes (v' , l) = yes (v' , there l)
σ-lookup-dec (v ∷ₛ σ) (suc n) | no ¬l = no (λ { (v , there l) → ¬l (v , l)})
