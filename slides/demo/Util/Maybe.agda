module Util.Maybe where

-- Local imports
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

-- I would really like to use the definition from Data.Maybe.
-- However it is not possible to import *only* the constructors
-- from the Maybe type, without importing those from Any and All
data Maybe {a} (A : Set a) : Set a where
  just    : (x : A) → Maybe A
  nothing : Maybe A

{-# IMPORT Data.FFI #-}
{-# COMPILED_DATA Maybe Data.FFI.AgdaMaybe Just Nothing #-}

just-injective : ∀ {a} {A : Set a} {x y : A} → just x ≡ just y → x ≡ y
just-injective refl = refl

-- fmap and applicative specialised to the Maybe functor
infixl 4 _<$>_ _<*>_
infixl 20 _<$=>_ _<*=>_
_<$>_ : ∀ {a b} {A : Set a} {B : Set b} →
          (f : A → B) →
          Maybe A → Maybe B
f <$> nothing = nothing
f <$> just x  = just (f x)

fmap : ∀ {a b} {A : Set a} {B : Set b} →
         (f : A → B) →
         Maybe A → Maybe B
fmap = _<$>_

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
