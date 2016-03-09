module Util.Vec where

-- Re-exports
open import Data.Vec
  using (Vec ; [] ; _∷_ ; toList ; fromList ; lookup ; _[_]≔_ )
  renaming (map to Vec-map ; zip to Vec-zip) public
open import Data.Vec.Properties
  using ([]≔-lookup ; map-[]≔)
  renaming (∷-injective to Vec-∷-injective) public

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
update i x xs = xs [ i ]≔ x

infixr 5 _∷_
data AllZipᵥ {a b p} {A : Set a} {B : Set b} (P : A → B → Set p) :
             ∀ {m} → Vec A m → Vec B m → Set (p ⊔ a ⊔ b) where
  [] : AllZipᵥ P [] []
  _∷_ : ∀ {x y m xs ys} → P x y →
                          AllZipᵥ P {m} xs ys →
                          AllZipᵥ P (x ∷ xs) (y ∷ ys)

AllZipᵥ-trans : ∀ {a b c p₁ p₂ q} {A : Set a} {B : Set b} {C : Set c}
                  {P₁ : A → B → Set p₁}
                  {P₂ : B → C → Set p₂}
                  {Q : A → C → Set q}
                  {m xs ys zs} →
                  (f : ∀ {x y z} → P₁ x y → P₂ y z → Q x z) →
                  AllZipᵥ P₁ xs ys →
                  AllZipᵥ P₂ ys zs →
                  AllZipᵥ Q {m} xs zs
AllZipᵥ-trans f [] [] = []
AllZipᵥ-trans f (p₁ ∷ ps₁) (p₂ ∷ ps₂) = f p₁ p₂ ∷ AllZipᵥ-trans f ps₁ ps₂

AllZipᵥ-map : ∀ {a b p q} {A : Set a} {B : Set b}
                {P : A → B → Set p} {Q : A → B → Set q}
                {m xs ys} →
                (f : ∀ {x y} → P x y → Q x y) →
                AllZipᵥ P {m} xs ys → AllZipᵥ Q xs ys
AllZipᵥ-map f [] = []
AllZipᵥ-map f (p ∷ ps) = f p ∷ AllZipᵥ-map f ps

allzipᵥ-lookup : ∀ {a b p} {A : Set a} {B : Set b} {P : A → B → Set p}
                  {m} {xs : Vec A m} {ys : Vec B m} →
                  (i : Fin m) →
                  AllZipᵥ P xs ys →
                  P (lookup i xs) (lookup i ys)
allzipᵥ-lookup () []
allzipᵥ-lookup zero (p ∷ ps) = p
allzipᵥ-lookup (suc i) (p ∷ ps) = allzipᵥ-lookup i ps

allzipᵥ-update : ∀ {a b p} {A : Set a} {B : Set b} {P : A → B → Set p}
                  {m} {xs : Vec A m} {ys : Vec B m} →
                  {x : A} → {y : B} →
                  (i : Fin m) →
                  P x y →
                  AllZipᵥ P xs ys →
                  AllZipᵥ P (update i x xs) (update i y ys)
allzipᵥ-update () p []
allzipᵥ-update zero p (p' ∷ ps) = p ∷ ps
allzipᵥ-update (suc i) p (p' ∷ ps) = p' ∷ allzipᵥ-update i p ps

data Allᵥ {a p} {A : Set a} (P : A → Set p) :
          ∀ {m} (L : Vec A m) → Set (a ⊔ p) where
  [] : Allᵥ P []
  _∷_ : ∀ {m x xs} → P x → Allᵥ P {m} xs → Allᵥ P (x ∷ xs)

AllZipᵥ-extract← : ∀ {a b p q} {A : Set a} {B : Set b}
                     {P : A → B → Set p} {Q : A → Set q}
                     {m xs ys} →
                     (f : ∀ {x y} → P x y → Q x) →
                     AllZipᵥ P {m} xs ys → Allᵥ Q xs
AllZipᵥ-extract← f [] = []
AllZipᵥ-extract← f (p ∷ ps) = f p ∷ AllZipᵥ-extract← f ps

AllZipᵥ-extract→ : ∀ {a b p q} {A : Set a} {B : Set b}
                     {P : A → B → Set p} {Q : B → Set q}
                     {m xs ys} →
                     (f : ∀ {x y} → P x y → Q y) →
                     AllZipᵥ P {m} xs ys → Allᵥ Q ys
AllZipᵥ-extract→ f [] = []
AllZipᵥ-extract→ f (p ∷ ps) = f p ∷ AllZipᵥ-extract→ f ps

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

Allᵥ-update : ∀ {a p} {A : Set a} {P : A → Set p} {m}
                {x} {xs : Vec A m} →
                (i : Fin m) →
                P x →
                Allᵥ P xs →
                Allᵥ P (update i x xs)
Allᵥ-update zero x⋆ (x'⋆ ∷ xs⋆) = x⋆ ∷ xs⋆
Allᵥ-update (suc i) x⋆ (x'⋆ ∷ xs⋆) = x'⋆ ∷ Allᵥ-update i x⋆ xs⋆

Allᵥ-lookup : ∀ {a p} {A : Set a} {P : A → Set p} {m}
                {xs : Vec A m} →
                (i : Fin m) →
                Allᵥ P xs →
                P (lookup i xs)
Allᵥ-lookup zero (x⋆ ∷ xs⋆) = x⋆
Allᵥ-lookup (suc i) (x⋆ ∷ xs⋆) = Allᵥ-lookup i xs⋆

Allᵥ-dec : ∀ {a p} {A : Set a} {P : A → Set p} {m} →
             (f : (a : A) → Dec (P a)) →
             (L : Vec A m) →
             Dec (Allᵥ P L)
Allᵥ-dec f [] = yes []
Allᵥ-dec f (x ∷ L) with f x | Allᵥ-dec f L
Allᵥ-dec f (x ∷ L) | yes x⋆ | yes xs⋆ = yes (x⋆ ∷ xs⋆)
Allᵥ-dec f (x ∷ L) | no ¬x⋆ | _  = no (λ { (x⋆ ∷ xs⋆) → ¬x⋆ x⋆ })
Allᵥ-dec f (x ∷ L) | _ | no ¬xs⋆ = no (λ { (x⋆ ∷ xs⋆) → ¬xs⋆ xs⋆ })

AllZipᵥ-dec : ∀ {a b p} {A : Set a} {B : Set b}
                {m} →
                {P : A → B → Set p} →
                (f : ∀ x y → Dec (P x y)) →
                (xs : Vec A m) →
                (ys : Vec B m) →
                Dec (AllZipᵥ P xs ys)
AllZipᵥ-dec f [] [] = yes []
AllZipᵥ-dec f (x ∷ xs) (y ∷ ys)
  with f x y | AllZipᵥ-dec f xs ys
... | yes p | yes ps = yes (p ∷ ps)
... | no ¬p | _ = no (λ { (p ∷ ps) → ¬p p})
... | _ | no ¬ps = no (λ { (p ∷ ps) → ¬ps ps})

instance
  Vec-Tree : ∀ {ℓ} {A : Set ℓ} {{t : ToTree A}} {m} → ToTree (Vec A m)
  Vec-Tree {A = A} = tree⋆ (λ { (node _ xs) → from xs })
                           (λ x → node 0 (proj₁ (sur x)) , proj₂ (sur x))
    where from : ∀ {m} → List Tree → Maybe (Vec A m)
          from {m = zero} [] = just []
          from {m = zero} (x ∷ xs) = nothing
          from {m = suc m} [] = nothing
          from {m = suc m} (x ∷ xs) = _∷_ <$> fromTree x <*> from {m = m} xs
          sur : ∀ {m} → IsSurjective (from {m})
          sur [] = [] , refl
          sur (x ∷ xs) = toTree x ∷ proj₁ (sur xs) ,
            _∷_ <$=> invTree x <*=> proj₂ (sur xs)
