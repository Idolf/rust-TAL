module Util.Maybe where

-- Re-exports
open import Data.Maybe.Base using (Maybe ; just ; nothing) public

-- Local imports
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

just-injective : ∀ {a} {A : Set a} {x y : A} → just x ≡ just {A = A} y → x ≡ y
just-injective refl = refl

-- fmap and applicative specialised to the Maybe functor
infixl 4 _<$>_ _<*>_
infixl 20 _<$=>_ _<*=>_
_<$>_ : ∀ {a b} {A : Set a} {B : Set b} →
          (f : A → B) →
          Maybe A → Maybe B
f <$> nothing = nothing
f <$> just x  = just (f x)

_<*>_ : ∀ {a b} {A : Set a} {B : Set b} →
        (f : Maybe (A → B)) → Maybe A → Maybe B
_       <*> nothing = nothing
nothing <*> _       = nothing
just f  <*> just x  = just (f x)

_<$=>_ : ∀ {a b} {A : Set a} {B : Set b} →
          (f : A → B) →
          {x : A} {y : Maybe A} →
          y ≡ just x →
          f <$> y ≡ just (f x)
f <$=> refl = refl

_<*=>_ : ∀ {a b} {A : Set a} {B : Set b} →
          {f : A → B} {g : Maybe (A → B)} →
          {x : A} {y : Maybe A} →
          g ≡ just f →
          y ≡ just x →
          g <*> y ≡ just (f x)
refl <*=> refl = refl
