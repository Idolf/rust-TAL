module Util.Vec where

-- Re-exports
open import Data.Vec
  using (Vec ; [] ; _∷_ ; toList ; fromList ; lookup)
  renaming (map to Vec-map ; zip to Vec-zip) public
open import Data.Vec.Properties
  using () renaming (∷-injective to Vec-∷-injective) public

-- Local imports
open import Util.Maybe
open import Util.Eq
open import Util.Function
open import Util.Dec
open import Util.Tree
open import Data.Product using (_,_ ; proj₁ ; proj₂ ; _×_)
open import Data.Nat using (zero ; suc)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.List using (List ; map ; [] ; _∷_)
open import Level using (_⊔_)

repeat : ∀ {a} {A : Set a} {m} → A → Vec A m
repeat {m = zero}  x = []
repeat {m = suc i} x = x ∷ repeat x

update : ∀ {a} {A : Set a} {m} →
           Fin m → A → Vec A m → Vec A m
update zero    xᵥ (_ ∷ xs) = xᵥ ∷ xs
update (suc i) xᵥ (x ∷ xs) = x ∷ update i xᵥ xs

infixr 5 _∷_
data Allᵥ {a p} {A : Set a} (P : A → Set p) :
          ∀ {m} (L : Vec A m) → Set (a ⊔ p) where
  [] : Allᵥ P []
  _∷_ : ∀ {m x xs} → P x → Allᵥ P {m} xs → Allᵥ P (x ∷ xs)

tabulate : ∀ {a p} {A : Set a} {P : A → Set p} {m xs} →
             (∀ x → P x) → Allᵥ P {m} xs
tabulate {xs = []}     hyp = []
tabulate {xs = x ∷ xs} hyp = hyp x ∷ tabulate hyp

Allᵥ-map : ∀ {a p} {A : Set a} {P Q : A → Set p} {m} {L : Vec A m} →
             (f : ∀ {x} → P x → Q x) →
             Allᵥ P L →
             Allᵥ Q L
Allᵥ-map f [] = []
Allᵥ-map f (p ∷ ps) = f p ∷ Allᵥ-map f ps

Allᵥ-zip : ∀ {a p} {A : Set a} {P : A × A → Set p} {m} {L : Vec A m} →
             Allᵥ (λ x → P (x , x)) L →
             Allᵥ P (Vec-zip L L)
Allᵥ-zip [] = []
Allᵥ-zip (p ∷ ps) = p ∷ Allᵥ-zip ps

Allᵥ-dec : ∀ {a p} {A : Set a} {P : A → Set p} {m} →
             (f : (a : A) → Dec (P a)) →
             (L : Vec A m) →
             Dec (Allᵥ P L)
Allᵥ-dec f [] = yes []
Allᵥ-dec f (x ∷ L) with f x | Allᵥ-dec f L
Allᵥ-dec f (x ∷ L) | yes x⋆ | yes xs⋆ = yes (x⋆ ∷ xs⋆)
Allᵥ-dec f (x ∷ L) | no ¬x⋆ | _  = no (λ { (x⋆ ∷ xs⋆) → ¬x⋆ x⋆ })
Allᵥ-dec f (x ∷ L) | _ | no ¬xs⋆ = no (λ { (x⋆ ∷ xs⋆) → ¬xs⋆ xs⋆ })

instance
  Vec-Tree : ∀ {ℓ} {A : Set ℓ} {{t : ToTree A}} {m} → ToTree (Vec A m)
  Vec-Tree = tree⋆ (λ { (node _ xs) → from xs })
                   (λ x → node 0 (proj₁ (sur x)) , proj₂ (sur x))
    where from : ∀ {ℓ} {A : Set ℓ} {{t : ToTree A}} {m} →
                   List Tree → ¿ Vec A m
          from {m = zero} [] = Just []
          from {m = zero} (x ∷ xs) = Nothing
          from {m = suc m} [] = Nothing
          from {m = suc m} (x ∷ xs) = _∷_ <$> fromTree x <*> from {m = m} xs
          sur : ∀ {ℓ} {A : Set ℓ} {{t : ToTree A}} {m} →
                  IsSurjective (from {{t}} {m})
          sur [] = [] , refl
          sur (x ∷ xs) = toTree x ∷ proj₁ (sur xs) ,
            _∷_ <$=> invTree x <*=> proj₂ (sur xs)
