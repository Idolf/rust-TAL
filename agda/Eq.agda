open import Relation.Binary.Core using (_≡_ ; Decidable)
open import Relation.Nullary using (Dec)
open import Level
import Data.Nat as N

DecidableEq : ∀ {a} → Set a → Set a
DecidableEq A = Decidable {A = A} _≡_

record Eq {a} (A : Set a) : Set a where
  infix 4 _≟_
  field
    _≟_ : DecidableEq A

open Eq {{...}} public

instance
  ℕ-Eq : Eq N.ℕ
  ℕ-Eq = record { _≟_ = N._≟_ }
