module Util.List where

-- Re-exports
open import Data.List
  using (List ; [] ; _∷_ ; _∷ʳ_ ; [_] ; map ;
        length ; zip ; _++_ ; replicate)
  public
open import Data.List.All using (All ; [] ; _∷_)
                          renaming (all to All-dec) public
open import Data.List.Properties using ()
  renaming ( ∷-injective to List-∷-injective
           ; length-++ to List-length-++) public

-- Local imports
open import Util.Maybe
open import Util.Function
open import Util.Dec
open import Util.Tree
open import Data.Nat hiding (_≟_ ; _⊔_)
open import Data.Product using (_,_ ; proj₁ ; proj₂ ; _×_ ; ∃)
open import Relation.Binary.PropositionalEquality
open import Level using (_⊔_)
import Algebra as A
import Data.List as L
import Data.Nat.Properties as NP
open A.CommutativeSemiring NP.commutativeSemiring using (+-comm ; +-assoc)
infixr 5 _∷_
data AllZip {a b p} {A : Set a} {B : Set b} (P : A → B → Set p) :
            List A → List B → Set (p ⊔ a ⊔ b) where
  [] : AllZip P [] []
  _∷_ : ∀ {x y xs ys} → P x y → AllZip P xs ys → AllZip P (x ∷ xs) (y ∷ ys)

AllZip-++ : ∀ {a b p} {A : Set a} {B : Set b} {P : A → B → Set p}
              {xs₁ xs₂ ys₁ ys₂} →
              AllZip P xs₁ ys₁ → AllZip P xs₂ ys₂ →
              AllZip P (xs₁ ++ xs₂) (ys₁ ++ ys₂)
AllZip-++ [] ps₂ = ps₂
AllZip-++ (p₁ ∷ ps₁) ps₂ = p₁ ∷ AllZip-++ ps₁ ps₂

AllZip-length : ∀ {a b p} {A : Set a} {B : Set b} {P : A → B → Set p}
                  {xs ys} →
                  AllZip P xs ys → length xs ≡ length ys
AllZip-length [] = refl
AllZip-length (p ∷ ps) rewrite AllZip-length ps = refl

List-++-assoc : ∀ {ℓ} {A : Set ℓ} (xs₁ xs₂ xs₃ : List A) →
                  (xs₁ ++ xs₂) ++ xs₃ ≡ xs₁ ++ xs₂ ++ xs₃
List-++-assoc {A = A} = A.Monoid.assoc (L.monoid A)

List-++-right-identity : ∀ {ℓ} {A : Set ℓ} xs →
                           xs ++ [] ≡ xs
List-++-right-identity {A = A} = proj₂ (A.Monoid.identity (L.monoid A))

infix 4 _↓_⇒_
data _↓_⇒_ {ℓ} {A : Set ℓ} : List A → ℕ → A → Set ℓ where
  here  : ∀ {x xs} →
            x ∷ xs ↓ 0 ⇒ x
  there : ∀ {x r xs i} →
            xs ↓ i ⇒ r →
            x ∷ xs ↓ suc i ⇒ r

<-to-↓ : ∀ {ℓ} {A : Set ℓ} →
           (xs : List A) →
           {i : ℕ} → i < length xs →
           ∃ λ v → xs ↓ i ⇒ v
<-to-↓ [] ()
<-to-↓ (x ∷ xs) {zero} i<len = x , here
<-to-↓ (x ∷ xs) {suc i} (s≤s i<len) with <-to-↓ xs {i} i<len
... | v , l = v , there l

↓-to-< : ∀ {ℓ} {A : Set ℓ}
           {i x} →
           {xs : List A} →
           xs ↓ i ⇒ x →
           i < length xs
↓-to-< here = s≤s z≤n
↓-to-< (there l) = s≤s (↓-to-< l)

↓-unique : ∀ {ℓ} {A : Set ℓ} {xs i} {v₁ v₂ : A} →
             xs ↓ i ⇒ v₁ →
             xs ↓ i ⇒ v₂ →
             v₁ ≡ v₂
↓-unique here here = refl
↓-unique (there l₁) (there l₂) = ↓-unique l₁ l₂

↓-dec : ∀ {ℓ} {A : Set ℓ} xs i →
          Dec (∃ λ (v : A) → xs ↓ i ⇒ v)
↓-dec [] i = no (λ { (_ , ()) })
↓-dec (x ∷ xs) zero = yes (x , here)
↓-dec (x ∷ xs) (suc i) with ↓-dec xs i
... | yes (v , l) = yes (v , there l)
... | no  ¬l = no (λ { (v , there l) → ¬l (v , l)})

↓-decᵥ : ∀ {ℓ} {A : Set ℓ} {{_ : DecEq A}} xs i (v : A) →
          Dec (xs ↓ i ⇒ v)
↓-decᵥ xs i v₁ with ↓-dec xs i
↓-decᵥ xs i v₁ | yes (v₂ , l) with v₁ ≟ v₂
↓-decᵥ xs i v  | yes (.v , l) | yes refl = yes l
↓-decᵥ xs i v₁ | yes (v₂ , l) | no v₁≢v₂ = no (λ l' → v₁≢v₂ (↓-unique l' l))
↓-decᵥ xs i v₁ | no ¬l = no (λ l' → ¬l (v₁ , l'))

↓-length : ∀ {ℓ} {A : Set ℓ} xs (x : A) →
             xs ∷ʳ x ↓ length xs ⇒ x
↓-length [] x = here
↓-length (x' ∷ xs) x = there (↓-length xs x)

↓-add-right : ∀ {ℓ} {A : Set ℓ} {xs₁} xs₂ {i} {v : A} →
                   xs₁ ↓ i ⇒ v →
                   xs₁ ++ xs₂ ↓ i ⇒ v
↓-add-right {xs₁ = []} xs₂ ()
↓-add-right {xs₁ = x₁ ∷ xs₁} xs₂ here = here
↓-add-right {xs₁ = x₁ ∷ xs₁} xs₂ (there l) = there (↓-add-right xs₂ l)

↓-add-left : ∀ {ℓ} {A : Set ℓ} xs₁ {xs₂ i} {v : A} →
                   xs₂ ↓ i ⇒ v →
                   xs₁ ++ xs₂ ↓ length xs₁ + i ⇒ v
↓-add-left [] l = l
↓-add-left (x₁ ∷ xs₁) l = there (↓-add-left xs₁ l)

↓-remove-left : ∀ {ℓ} {A : Set ℓ} xs₁ {xs₂ i} {v : A} →
                  i ≥ length xs₁ →
                  xs₁ ++ xs₂ ↓ i ⇒ v →
                  xs₂ ↓ i ∸ length xs₁ ⇒ v
↓-remove-left [] i≥len l = l
↓-remove-left (x₁ ∷ xs₁) () here
↓-remove-left (x ∷ xs₁) (s≤s i≥len) (there l) = ↓-remove-left xs₁ i≥len l

↓-remove-right : ∀ {ℓ} {A : Set ℓ} xs₁ {xs₂} {i} {v : A} →
                      i < length xs₁ →
                      xs₁ ++ xs₂ ↓ i ⇒ v →
                      xs₁ ↓ i ⇒ v
↓-remove-right [] () l
↓-remove-right (x ∷ xs₁) i<len here = here
↓-remove-right (x ∷ xs₁) (s≤s i<len) (there l) =
  there (↓-remove-right xs₁ i<len l)

↓-last : ∀ {ℓ} {A : Set ℓ} xs {x : A} →
           xs ∷ʳ x ↓ length xs ⇒ x
↓-last [] = here
↓-last (x ∷ xs) = there (↓-last xs)

infix 4 _⟦_⟧←_⇒_
data _⟦_⟧←_⇒_ {ℓ} {A : Set ℓ} : List A → ℕ → A → List A → Set ℓ where
  here : ∀ {x xᵥ xs} →
           x ∷ xs ⟦ 0 ⟧← xᵥ ⇒ xᵥ ∷ xs
  there : ∀ {x xᵥ xs xs' i} →
          xs ⟦ i ⟧← xᵥ ⇒ xs' →
          x ∷ xs ⟦ suc i ⟧← xᵥ ⇒ x ∷ xs'

←-unique : ∀ {ℓ} {A : Set ℓ} {xs xs₁ xs₂ i} {v : A} →
             xs ⟦ i ⟧← v ⇒ xs₁ →
             xs ⟦ i ⟧← v ⇒ xs₂ →
             xs₁ ≡ xs₂
←-unique here here = refl
←-unique {xs = v ∷ xs} (there up₁) (there up₂) =
  cong (_∷_ v) (←-unique up₁ up₂)

←-dec : ∀ {ℓ} {A : Set ℓ} xs i (v : A) → Dec (∃ λ xs' → xs ⟦ i ⟧← v ⇒ xs')
←-dec [] i v = no (λ { (_ , ()) })
←-dec (x ∷ xs) zero v = yes (v ∷ xs , here)
←-dec (x ∷ xs) (suc i) v with ←-dec xs i v
... | yes (xs' , up) = yes (x ∷ xs' , there up)
... | no ¬up = no (λ { (._ , there up) → ¬up (_ , up)} )

<-to-← : ∀ {ℓ} {A : Set ℓ} xs (x : A) {i} →
           i < length xs →
           ∃ λ xs' →
             xs ⟦ i ⟧← x ⇒ xs'
<-to-← [] xᵥ ()
<-to-← (x ∷ xs) xᵥ {zero} (s≤s i<len) = xᵥ ∷ xs , here
<-to-← (x ∷ xs) xᵥ {suc i} (s≤s i<len)
  with <-to-← xs xᵥ i<len
... | xs' , up = x ∷ xs' , there up

←-to-< : ∀ {ℓ} {A : Set ℓ}
           {i x} →
           {xs xs' : List A} →
           xs ⟦ i ⟧← x ⇒ xs' →
           i < length xs
←-to-< here = s≤s z≤n
←-to-< (there l) = s≤s (←-to-< l)

←-to-↓ : ∀ {ℓ} {A : Set ℓ}
           {i x} →
           {xs xs' : List A} →
           xs ⟦ i ⟧← x ⇒ xs' →
           xs' ↓ i ⇒ x
←-to-↓ here = here
←-to-↓ (there up) = there (←-to-↓ up)

allzip-lookup : ∀ {a b p} {A : Set a} {B : Set b} {P : A → B → Set p}
                  {xs : List A} {ys : List B}
                  {i x y} →
                  xs ↓ i ⇒ x →
                  ys ↓ i ⇒ y →
                  AllZip P xs ys →
                  P x y
allzip-lookup here here (p ∷ ps) = p
allzip-lookup (there l₁) (there l₂) (p ∷ ps) = allzip-lookup l₁ l₂ ps

allzip-lookup₁ : ∀ {a b p} {A : Set a} {B : Set b} {P : A → B → Set p}
                   {xs : List A} {ys : List B}
                   {i x} →
                   xs ↓ i ⇒ x →
                   AllZip P xs ys →
                   ∃ λ y →
                     ys ↓ i ⇒ y ×
                     P x y
allzip-lookup₁ here (p ∷ ps) = _ , here , p
allzip-lookup₁ (there l) (p ∷ ps) with allzip-lookup₁ l ps
... | y , l' , p' = y , there l' , p'

allzip-lookup₂ : ∀ {a b p} {A : Set a} {B : Set b} {P : A → B → Set p}
                   {xs : List A} {ys : List B}
                   {i y} →
                   ys ↓ i ⇒ y →
                   AllZip P xs ys →
                   ∃ λ x →
                     xs ↓ i ⇒ x ×
                     P x y
allzip-lookup₂ here (p ∷ ps) = _ , here , p
allzip-lookup₂ (there l) (p ∷ ps) with allzip-lookup₂ l ps
... | x , l' , p' = x , there l' , p'

allzip-update : ∀ {a b p} {A : Set a} {B : Set b} {P : A → B → Set p}
                  {xs xs' : List A} {ys ys' : List B}
                  {i x y} →
                  xs ⟦ i ⟧← x ⇒ xs' →
                  ys ⟦ i ⟧← y ⇒ ys' →
                  P x y →
                  AllZip P xs ys →
                  AllZip P xs' ys'
allzip-update here here p (p' ∷ ps) = p ∷ ps
allzip-update (there up₁) (there up₂) p₁ (p' ∷ ps) =
  p' ∷ allzip-update up₁ up₂ p₁ ps

allzip-update₁ : ∀ {a b p} {A : Set a} {B : Set b} {P : A → B → Set p}
                  {xs xs' : List A} {ys : List B}
                  {i x y} →
                  xs ⟦ i ⟧← x ⇒ xs' →
                  P x y →
                  AllZip P xs ys →
                  ∃ λ ys' →
                    ys ⟦ i ⟧← y ⇒ ys' ×
                    AllZip P xs' ys'
allzip-update₁ here p (p' ∷ ps) = _ , here , p ∷ ps
allzip-update₁ (there up) p (p' ∷ ps)
  with allzip-update₁ up p ps
... | ys' , up' , ps' = _ , there up' , p' ∷ ps'

allzip-update₂ : ∀ {a b p} {A : Set a} {B : Set b} {P : A → B → Set p}
                  {xs : List A} {ys ys' : List B}
                  {i x y} →
                  ys ⟦ i ⟧← y ⇒ ys' →
                  P x y →
                  AllZip P xs ys →
                  ∃ λ xs' →
                    xs ⟦ i ⟧← x ⇒ xs' ×
                    AllZip P xs' ys'
allzip-update₂ here p (p' ∷ ps) = _ , here , p ∷ ps
allzip-update₂ (there up) p (p' ∷ ps)
  with allzip-update₂ up p ps
... | ys' , up' , ps' = _ , there up' , p' ∷ ps'

All-lookup : ∀ {a p} {A : Set a} {P : A → Set p}
               {x} {xs : List A} {i} →
               xs ↓ i ⇒ x →
               All P xs →
               P x
All-lookup here (x⋆ ∷ xs⋆) = x⋆
All-lookup (there l) (x⋆ ∷ xs⋆) = All-lookup l xs⋆

All-update : ∀ {a p} {A : Set a} {P : A → Set p}
               {x} {xs xs' : List A} {i} →
               P x →
               xs ⟦ i ⟧← x ⇒ xs' →
               All P xs →
               All P xs'
All-update x⋆ here (x'⋆ ∷ xs⋆) = x⋆ ∷ xs⋆
All-update x⋆ (there up) (x'⋆ ∷ xs⋆) = x'⋆ ∷ All-update x⋆ up xs⋆

data Drop {a} {A : Set a} : ℕ → List A → List A → Set a where
  here : ∀ {xs} → Drop 0 xs xs
  there : ∀ {x xs xs' i} → Drop i xs xs' → Drop (suc i) (x ∷ xs) xs'

drop-dec : ∀ {a} {A : Set a} i (xs : List A) →
             Dec (∃ λ xs' → Drop i xs xs')
drop-dec zero xs = yes (xs , here)
drop-dec (suc i) [] = no (λ { (_ , ()) })
drop-dec (suc i) (x ∷ xs)
  with drop-dec i xs
... | yes (xs' , drop) = yes (xs' , there drop)
... | no ¬drop = no (λ { (xs' , there drop) → ¬drop (xs' , drop)})

drop-unique : ∀ {a} {A : Set a} {i} {xs xs₁ xs₂ : List A} →
                Drop i xs xs₁ →
                Drop i xs xs₂ →
                xs₁ ≡ xs₂
drop-unique here here = refl
drop-unique (there drop₁) (there drop₂) = drop-unique drop₁ drop₂

instance
  List-Tree : ∀ {ℓ} {A : Set ℓ} {{t : ToTree A}} → ToTree (List A)
  List-Tree {A = A} = tree⋆ (λ { (node _ xs) → from xs })
                            (λ x → node 0 (proj₁ (sur x)) , proj₂ (sur x))
    where from : List Tree → Maybe (List A)
          from [] = just []
          from (x ∷ xs) = _∷_ <$> fromTree x <*> from xs
          sur : IsSurjective from
          sur [] = [] , refl
          sur (x ∷ xs) = toTree x ∷ proj₁ (sur xs) ,
            _∷_ <$=> invTree x <*=> proj₂ (sur xs)
