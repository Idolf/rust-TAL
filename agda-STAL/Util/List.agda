module Util.List where

-- Re-exports
open import Data.List
  using (List ; [] ; _∷_ ; [_] ; map ; length ; zip ; _++_) public
open import Data.List.All
  using (All ; [] ; _∷_) renaming (map to All-map ; all to All-dec) public
open import Data.List.Properties using ()
  renaming (∷-injective to List-∷-injective) public

-- Local imports
open import Util.Maybe
open import Util.Eq
open import Util.Function
open import Util.Dec
open import Util.Tree
open import Data.Nat using (ℕ ; zero ; suc ; _<_ ; s≤s ; z≤n ; _≤?_)
open import Data.Product using (_,_ ; proj₁ ; proj₂ ; _×_ ; ∃)

infix 4 _↓_⇒_
data _↓_⇒_ {ℓ} {A : Set ℓ} : (xs : List A) → ℕ → A → Set ℓ where
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

All-zip : ∀ {a p} {A : Set a} {P : A × A → Set p} {L : List A} →
            All (λ x → P (x , x)) L →
            All P (zip L L)
All-zip [] = []
All-zip (p ∷ ps) = p ∷ All-zip ps

All-unzip : ∀ {a p} {A : Set a} {P : A × A → Set p} {L : List A} →
              All P (zip L L) →
              All (λ x → P (x , x)) L
All-unzip {L = []} [] = []
All-unzip {L = x ∷ L} (p ∷ ps) = p ∷ All-unzip ps

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
