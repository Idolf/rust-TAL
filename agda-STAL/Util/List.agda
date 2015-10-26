module Util.List where

-- Re-exports
open import Data.List
  using (List ; [] ; _∷_ ; _∷ʳ_ ; [_] ; map ; length ; zip ; _++_) public
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

↓-remove-right : ∀ {ℓ} {A : Set ℓ} {xs₁} xs₂ {i} {v : A} →
                      i < length xs₁ →
                      xs₁ ++ xs₂ ↓ i ⇒ v →
                      xs₁ ↓ i ⇒ v
↓-remove-right {xs₁ = []} xs₂ () l
↓-remove-right {xs₁ = x ∷ xs₁} xs₂ i<len here = here
↓-remove-right {xs₁ = x ∷ xs₁} xs₂ (s≤s i<len) (there l) =
  there (↓-remove-right xs₂ i<len l)

↓-replace-left : ∀ {ℓ} {A : Set ℓ} xs₁ xs₁' {xs₂ i} {v : A} →
                   length xs₁ ≡ length xs₁' →
                   i ≥ length xs₁ →
                   xs₁ ++ xs₂ ↓ i ⇒ v →
                   xs₁' ++ xs₂ ↓ i ⇒ v
↓-replace-left xs₁ xs₁' eq i≥len l
  with ↓-add-left xs₁' (↓-remove-left xs₁ i≥len l)
... | l' rewrite eq | NP.m+n∸m≡n i≥len = l'

↓-add-middle : ∀ {ℓ} {A : Set ℓ} xs₁ xs⁺ {xs₂} {i} {v : A} →
                 i ≥ length xs₁ →
                 xs₁ ++ xs₂ ↓ i ⇒ v →
                 xs₁ ++ xs⁺ ++ xs₂ ↓ length xs⁺ + i ⇒ v
↓-add-middle xs₁ xs⁺ {i = i} i≥len l
  with ↓-add-left xs₁ (↓-add-left xs⁺ (↓-remove-left xs₁ i≥len l))
... | l'
  rewrite sym (+-assoc (length xs₁) (length xs⁺) (i ∸ length xs₁))
        | +-comm (length xs₁) (length xs⁺)
        | +-assoc (length xs⁺) (length xs₁) (i ∸ length xs₁)
        | NP.m+n∸m≡n i≥len
  = l'

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
