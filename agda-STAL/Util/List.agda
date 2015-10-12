module Util.List where

-- Re-exports
open import Data.List
  using (List ; [] ; _∷_ ; [_] ; map ; length ; zip ; _++_) public
open import Data.List.All
  using (All ; [] ; _∷_) renaming (map to All-map ; all to All-dec) public
open import Data.List.Properties using ()
  renaming ( ∷-injective to List-∷-injective
           ; length-++ to List-length-++) public

-- Local imports
open import Util.Maybe
open import Util.Function
open import Util.Dec
open import Util.Tree
open import Data.Nat hiding (_≟_)
open import Data.Product using (_,_ ; proj₁ ; proj₂ ; _×_ ; ∃)
open import Relation.Binary.PropositionalEquality
import Algebra as A
import Data.List as L
import Data.Nat.Properties as NP

foo : ∀ x y → x + suc y ≡ suc x + y
foo zero y = refl
foo (suc x) y = cong suc (foo x y)

List-++-assoc : ∀ {ℓ} {A : Set ℓ} (xs₁ xs₂ xs₃ : List A) →
                  (xs₁ ++ xs₂) ++ xs₃ ≡ xs₁ ++ xs₂ ++ xs₃
List-++-assoc {A = A} = A.Monoid.assoc (L.monoid A)

List-++-right-identity : ∀ {ℓ} {A : Set ℓ} xs →
                           xs ++ [] ≡ xs
List-++-right-identity {A = A} = proj₂ (A.Monoid.identity (L.monoid A))

infix 4 _↓_⇒_
data _↓_⇒_ {ℓ} {A : Set ℓ} : List A → ℕ → A → Set ℓ where
  here  : ∀ {x xs} →
            x ∷ xs ↓ zero ⇒ x
  there : ∀ {x r xs i} →
            xs ↓ i ⇒ r →
            x ∷ xs ↓ suc i ⇒ r

<-to-↓ : ∀ {ℓ} {A : Set ℓ} →
           (xs : List A) →
           {i : ℕ} → i < length xs →
           ∃ λ v → xs ↓ i ⇒ v
<-to-↓ [] ()
<-to-↓ (x ∷ xs) {zero} 0<len = x , here
<-to-↓ (x ∷ xs) {suc i} (s≤s i<len) = _ , there (proj₂ (<-to-↓ xs i<len))

↓-to-< : ∀ {ℓ} {A : Set ℓ} {xs i} {v : A} →
           xs ↓ i ⇒ v →
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
↓-dec xs i with suc i ≤? length xs
↓-dec xs i | yes i<len = yes (<-to-↓ xs i<len)
↓-dec xs i | no  i≮len = no (i≮len ∘ ↓-to-< ∘ proj₂)

↓-decᵥ : ∀ {ℓ} {A : Set ℓ} {{_ : DecEq A}} xs i (v : A) →
          Dec (xs ↓ i ⇒ v)
↓-decᵥ xs i v₁ with ↓-dec xs i
↓-decᵥ xs i v₁ | yes (v₂ , l) with v₁ ≟ v₂
↓-decᵥ xs i v  | yes (.v , l) | yes refl = yes l
↓-decᵥ xs i v₁ | yes (v₂ , l) | no v₁≢v₂ = no (λ l' → v₁≢v₂ (↓-unique l' l))
↓-decᵥ xs i v₁ | no ¬l = no (λ l' → ¬l (v₁ , l'))

↓-add-left : ∀ {ℓ} {A : Set ℓ} xs₁ {xs₂ i} {v : A} →
                   xs₂ ↓ i ⇒ v →
                   xs₁ ++ xs₂ ↓ length xs₁ + i ⇒ v
↓-add-left [] l = l
↓-add-left (x ∷ xs₁) l = there (↓-add-left xs₁ l)

↓-add-right : ∀ {ℓ} {A : Set ℓ} xs₁ {xs₂ i} {v : A} →
                   xs₁ ↓ i ⇒ v →
                   xs₁ ++ xs₂ ↓ i ⇒ v
↓-add-right (x ∷ xs₁) here = here
↓-add-right (x ∷ xs₁) (there l) = there (↓-add-right xs₁ l)

↓-remove-right : ∀ {ℓ} {A : Set ℓ} xs₁ {xs₂ i} {v : A} →
                      i < length xs₁ →
                      xs₁ ++ xs₂ ↓ i ⇒ v →
                      xs₁ ↓ i ⇒ v
↓-remove-right [] () l
↓-remove-right (x ∷ xs) i<len here = here
↓-remove-right (x ∷ xs) (s≤s i<len) (there l) =
  there (↓-remove-right xs i<len l)

↓-remove-left : ∀ {ℓ} {A : Set ℓ} xs₁ {xs₂ i} {v : A} →
                      i ≥ length xs₁ →
                      xs₁ ++ xs₂ ↓ i ⇒ v →
                      xs₂ ↓ i ∸ length xs₁ ⇒ v
↓-remove-left [] z≤n l = l
↓-remove-left (x ∷ xs₁) (s≤s i≥len) (there l) = ↓-remove-left xs₁ i≥len l

↓-replace-left : ∀ {ℓ} {A : Set ℓ} xs₁ xs₁' {xs₂ i} {v : A} →
                      length xs₁ ≡ length xs₁' →
                      i ≥ length xs₁ →
                      xs₁ ++ xs₂ ↓ i ⇒ v →
                      xs₁' ++ xs₂ ↓ i ⇒ v
↓-replace-left [] [] refl z≤n l = l
↓-replace-left [] (x₁' ∷ xs₁') () z≤n l
↓-replace-left (x₁ ∷ xs₁) (x₁' ∷ xs₁') eq (s≤s i≥len) (there l) =
  there (↓-replace-left xs₁ xs₁' (cong pred eq) i≥len l)
↓-replace-left (x₁ ∷ xs₁) [] () (s≤s i≥len) l

↓-add-middle : ∀ {ℓ} {A : Set ℓ} xs₁ xs₂ {xs₃ i} {v : A} →
                    i ≥ length xs₁ →
                    xs₁ ++ xs₃ ↓ i ⇒ v →
                    xs₁ ++ xs₂ ++ xs₃ ↓ length xs₂ + i ⇒ v
↓-add-middle [] [] z≤n l = l
↓-add-middle [] (x ∷ xs₂) z≤n l = there {x = x} (↓-add-middle [] xs₂ z≤n l)
↓-add-middle (x ∷ xs₁) xs₂ () here
↓-add-middle (x ∷ xs₁) xs₂ {i = suc i} (s≤s i≥len) (there l)
  rewrite foo (length xs₂) i
    = there (↓-add-middle xs₁ xs₂ i≥len l)

↓-remove-middle : ∀ {ℓ} {A : Set ℓ} xs₁ xs₂ {xs₃ i} {v : A} →
                       i ≥ length (xs₁ ++ xs₂) →
                       xs₁ ++ xs₂ ++ xs₃ ↓ i ⇒ v →
                       xs₁ ++ xs₃ ↓ i ∸ length xs₂ ⇒ v
↓-remove-middle (x₁ ∷ xs₁) xs₂ {xs₃} {suc i} {v} (s≤s i≥len) (there l) with
  begin
    length xs₂
  ≤⟨ NP.n≤m+n (length xs₁) _ ⟩
    length xs₁ + length xs₂
  ≡⟨ sym (List-length-++ xs₁) ⟩
    length (xs₁ ++ xs₂)
  ≤⟨ i≥len ⟩
    i
  ∎ where open ≤-Reasoning
... | i≥len' with
  ↓-remove-middle xs₁ xs₂ i≥len l | NP.+-∸-assoc 1 {i} {length xs₂} i≥len'
... | q | eq = subst₂ (λ xs i → xs ↓ i ⇒ v) refl (sym eq) (there q)
↓-remove-middle []         []         i≥len       l = l
↓-remove-middle []         (x₂ ∷ xs₂) (s≤s i≥len) (there l) =
  ↓-remove-middle [] xs₂ i≥len l

All-zip : ∀ {a p} {A : Set a} {P : A × A → Set p} {L : List A} →
            All (λ x → P (x , x)) L →
            All P (zip L L)
All-zip [] = []
All-zip (p ∷ ps) = p ∷ All-zip ps

instance
  List-Tree : ∀ {ℓ} {A : Set ℓ} {{t : ToTree A}} → ToTree (List A)
  List-Tree = tree⋆ (λ { (node _ xs) → from xs })
                    (λ x → node 0 (proj₁ (sur x)) , proj₂ (sur x))
    where from : ∀ {ℓ} {A : Set ℓ} {{t : ToTree A}} → List Tree → ¿ List A
          from [] = Just []
          from (x ∷ xs) = _∷_ <$> fromTree x <*> from xs
          sur : ∀ {ℓ} {A : Set ℓ} {{t : ToTree A}} → IsSurjective (from {{t}})
          sur [] = [] , refl
          sur (x ∷ xs) = toTree x ∷ proj₁ (sur xs) ,
            _∷_ <$=> invTree x <*=> proj₂ (sur xs)
