import Data.Nat as N
import Data.Vec as V
import Data.Vec.Properties as VP
import Relation.Binary as R
import Relation.Binary.Core as RC
open import Data.Product using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as P using (_≡_ ; refl)
open import Relation.Nullary using (Dec ; yes ; no)
open import Level using (_⊔_)
open import Function using (_∘_)

-- Decidable propositional equality
DecEqFun : ∀ {a} (A : Set a) → Set a
DecEqFun A = RC.Decidable (_≡_ {A = A})

DecEq : ∀ {a} (A : Set a) → Set a
DecEq A = R.IsDecEquivalence (_≡_ {A = A})

infix 4 _≟_
_≟_ : {a : Level.Level} {A : Set a} {{_ : DecEq A}} → DecEqFun A
_≟_ {{eq}} = R.IsDecEquivalence._≟_ eq

mkEq : ∀ {a} {A : Set a} → DecEqFun A → DecEq A
mkEq _≟_ = record { isEquivalence = P.isEquivalence ; _≟_ = _≟_ }

-- Decidable total orders
TotalOrder : ∀ {a} {ℓ} {A : Set a} (_≤_ : RC.Rel A ℓ) → Set (ℓ ⊔ a)
TotalOrder _≤_ = R.IsTotalOrder _≡_ _≤_

DecTotalOrder : ∀ {a} {ℓ} {A : Set a} (_≤_ : RC.Rel A ℓ) → Set (ℓ ⊔ a)
DecTotalOrder _≤_ = R.IsDecTotalOrder _≡_ _≤_

infix 4 _≤?_
_≤?_ : {a ℓ₂ : Level.Level} {A : Set a} {_≤_ : R.Rel A ℓ₂} {{_ : DecTotalOrder _≤_}} → R.Decidable _≤_
_≤?_ {{to}} = R.IsDecTotalOrder._≤?_ to

mkTotalOrder : ∀ {a} {ℓ} {A : Set a} {_≤_ : R.Rel A ℓ}
         {{to : TotalOrder _≤_}} {{dec-eq : DecEq A}} →
         RC.Decidable _≤_ → DecTotalOrder _≤_
mkTotalOrder {{to}} _≤?_ = record { isTotalOrder = to ; _≟_ = _≟_ ; _≤?_ = _≤?_ }

instance
  ℕ-dec-eq : DecEq N.ℕ
  ℕ-dec-eq = mkEq N._≟_

  ℕ-to : TotalOrder N._≤_
  ℕ-to = R.DecTotalOrder.isTotalOrder N.decTotalOrder

  ℕ-dec-to : DecTotalOrder N._≤_
  ℕ-dec-to = mkTotalOrder N._≤?_

  Vec-dec-eq : ∀ {a} {A : Set a} {m}
                 {{_ : DecEq A}} → DecEq (V.Vec A m)
  Vec-dec-eq = mkEq _==_
    where _==_ : ∀ {a} {A : Set a} {m}
                   {{_ : DecEq A}} →
                   (x y : V.Vec A m) → Dec (x ≡ y)
          V.[] == V.[] = yes refl
          (x V.∷ xs) == (y V.∷ ys) with x ≟ y | xs == ys
          (x₂ V.∷ xs) == (.x₂ V.∷ .xs) | yes refl | yes refl = yes refl
          (x₂ V.∷ xs) == (y V.∷ ys) | no ¬eq | _ = no (¬eq ∘ proj₁ ∘ VP.∷-injective)
          (x₂ V.∷ xs) == (y V.∷ ys) | _ | no ¬eq = no (¬eq ∘ proj₂ ∘ VP.∷-injective)

infixr 3 _∎
infixr 2 _≡⟨_⟩_ _⟨_⟩≡_ _≡⟨_∥_⟩_ _⟨_∥_⟩≡_
infixr 1 begin_
_≡⟨_⟩_ : ∀ {a} {A : Set a} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ refl ⟩ refl = refl

_⟨_⟩≡_ : ∀ {a} {A : Set a} (x : A) {y z : A} → y ≡ x → y ≡ z → x ≡ z
x ⟨ refl ⟩≡ refl = refl

_≡⟨_∥_⟩_ : ∀ {a b} {A : Set a} {B : Set b} (x : A) {x' y : B} {z : A} →
             x' ≡ y → (F : B → A) → {{_ : x ≡ F x'}} → F y ≡ z → x ≡ z
_≡⟨_∥_⟩_ x refl f {{x≡Fx'}} refl = x≡Fx'

_⟨_∥_⟩≡_ : ∀ {a b} {A : Set a} {B : Set b} (x : A) {x' y : B} {z : A} →
             y ≡ x' → (F : B → A) → {{_ : x ≡ F x'}} → F y ≡ z → x ≡ z
_⟨_∥_⟩≡_ x refl f {{x≡Fx'}} refl = x≡Fx'

_∎ : ∀ {a} {A : Set a} → (x : A) → x ≡ x
x ∎ = refl

begin_ : ∀ {a} {A : Set a} → {x y : A} → x ≡ y → x ≡ y
begin refl = refl

cong₃ : ∀ {A B C D : Set}
          {a₁ a₂ : A} {b₁ b₂ : B} {c₁ c₂ : C}
          (F : A → B → C → D) →
          a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ →
          F a₁ b₁ c₁ ≡ F a₂ b₂ c₂
cong₃ _ refl refl refl = refl
