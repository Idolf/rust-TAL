module Util.Maybe where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

infix 2 ¿_
data ¿_ {a} (A : Set a) : Set a where
  Nothing : ¿ A
  Just : A → ¿ A

Just-injective : ∀ {a} {A : Set a} {x y : A} → Just x ≡ Just y → x ≡ y
Just-injective refl = refl

infixl 5 _<$>_ _<*>_ _<$=>_ _<*=>_
_<$>_ : ∀ {a b} {A : Set a} {B : Set b} →
          (f : A → B) →
          ¿ A → ¿ B
f <$> Nothing = Nothing
f <$> Just x  = Just (f x)

_<*>_ : ∀ {a b} {A : Set a} {B : Set b} →
        (f : ¿ (A → B)) → ¿ A → ¿ B
_       <*> Nothing = Nothing
Nothing <*> _       = Nothing
Just f  <*> Just x  = Just (f x)

_<$=>_ : ∀ {a b} {A : Set a} {B : Set b} →
          (f : A → B) →
          {x : A} {y : ¿ A} →
          y ≡ Just x →
          f <$> y ≡ Just (f x)
f <$=> refl = refl

_<*=>_ : ∀ {a b} {A : Set a} {B : Set b} →
          {f : A → B} {g : ¿ (A → B)} →
          {x : A} {y : ¿ A} →
          g ≡ Just f →
          y ≡ Just x →
          g <*> y ≡ Just (f x)
refl <*=> refl = refl
