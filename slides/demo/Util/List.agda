module Util.List where

-- Re-exports
open import Data.List
  using (List ; [] ; _∷_ ; _∷ʳ_ ; [_] ; map ;
        length ; zip ; _++_ ; replicate ; drop)
  public
open import Data.List.All
  using (All ; [] ; _∷_)
  renaming (all to All-dec ; map to All-map) public
open import Data.List.Properties using ()
  renaming ( ∷-injective to List-∷-injective
           ; length-++ to List-length-++
           ; length-map to List-length-map
           ; map-++-commute to List-map-++-commute) public

-- Local imports
open import Util.Maybe
open import Util.Function
open import Util.Dec
open import Util.Tree
open import Data.Nat hiding (_≟_ ; _⊔_)
open import Data.Product using (_,_ ; proj₁ ; proj₂ ; _×_ ; ∃ ; ∃₂)
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

All→AllZip : ∀ {p a} {A : Set a} {P : A → A → Set p}
               {xs} →
               All (λ x → P x x) xs → AllZip P xs xs
All→AllZip [] = []
All→AllZip (p ∷ ps) = p ∷ All→AllZip ps

All→AllZip' : ∀ {a b c p} {A : Set a}
                {B : Set b} {C : Set c}
                {P : B → C → Set p}
                {xs : List A} f g →
                All (λ x → P (f x) (g x)) xs →
                AllZip P (map f xs) (map g xs)
All→AllZip' f g [] = []
All→AllZip' f g (p ∷ ps) = p ∷ All→AllZip' f g ps

All-≡-left : ∀ {a} {A : Set a}
               (f : A → A) {xs} →
               All (λ x → f x ≡ x) xs →
               map f xs ≡ xs
All-≡-left f [] = refl
All-≡-left f (eq ∷ eqs) = cong₂ _∷_ eq (All-≡-left f eqs)

All-∃→ : ∀ {a b p} {A : Set a} {B : Set b} {P : A → B → Set p}
           {xs} →
           All (λ x → ∃ λ y → P x y) xs →
           ∃ λ ys → AllZip P xs ys
All-∃→ [] = [] , []
All-∃→ ((y , p) ∷ ps)
  with All-∃→ ps
... | ys , ps'
  = y ∷ ys , p ∷ ps'

AllZip-∃→ : ∀ {a b c p₁ p₂}
              {A : Set a} {B : Set b} {C : Set c}
              {P₁ : A → C → Set p₁}
              {P₂ : B → C → Set p₂}
              {xs₁ xs₂} →
              AllZip (λ x₁ x₂ → ∃ λ y → P₁ x₁ y × P₂ x₂ y) xs₁ xs₂ →
              ∃ λ ys → AllZip P₁ xs₁ ys × AllZip P₂ xs₂ ys
AllZip-∃→ [] = [] , [] , []
AllZip-∃→ ((y , p₁ , p₂) ∷ ps)
  with AllZip-∃→ ps
... | ys , ps₁ , ps₂ = y ∷ ys , p₁ ∷ ps₁ , p₂ ∷ ps₂

AllZip-∃₂→ : ∀ {a b c d p₁ p₂ p₃}
               {A : Set a} {B : Set b} {C : Set c} {D : Set d}
               {P₁ : A → C → Set p₁}
               {P₂ : B → D → Set p₂}
               {P₃ : C → D → Set p₃}
               {xs₁ xs₂} →
               AllZip (λ x₁ x₂ → ∃₂ λ y₁ y₂ → P₁ x₁ y₁ × P₂ x₂ y₂ × P₃ y₁ y₂) xs₁ xs₂ →
               ∃₂ λ ys₁ ys₂ → AllZip P₁ xs₁ ys₁ × AllZip P₂ xs₂ ys₂ × AllZip P₃ ys₁ ys₂
AllZip-∃₂→ [] = [] , [] , [] , [] , []
AllZip-∃₂→ ((y₁ , y₂ , p₁ , p₂ , p₃) ∷ ps)
  with AllZip-∃₂→ ps
... | ys₁ , ys₂ , ps₁ , ps₂ , ps₃
  = y₁ ∷ ys₁ , y₂ ∷ ys₂ , p₁ ∷ ps₁ , p₂ ∷ ps₂ , p₃ ∷ ps₃

AllZip-split : ∀ {a b p₁ p₂}
                 {A : Set a} {B : Set b}
                 {P₁ : A → B → Set p₁}
                 {P₂ : A → B → Set p₂}
                 {xs ys} →
                 AllZip (λ x y → P₁ x y × P₂ x y) xs ys →
                 AllZip P₁ xs ys × AllZip P₂ xs ys
AllZip-split [] = [] , []
AllZip-split ((p₁ , p₂) ∷ ps)
  with AllZip-split ps
... | ps₁ , ps₂ = p₁ ∷ ps₁ , p₂ ∷ ps₂

AllZip-split' : ∀ {a b p₁ p₂}
                  {A : Set a} {B : Set b}
                  {P₁ : A → Set p₁}
                  {P₂ : B → Set p₂}
                  {xs ys} →
                  AllZip (λ x y → P₁ x × P₂ y) xs ys →
                  All P₁ xs × All P₂ ys
AllZip-split' [] = [] , []
AllZip-split' ((p₁ , p₂) ∷ ps)
  with AllZip-split' ps
... | ps₁ , ps₂ = p₁ ∷ ps₁ , p₂ ∷ ps₂

All-∃← : ∀ {a b p} {A : Set a} {B : Set b} {P : A → B → Set p}
           {xs} →
           (∃ λ ys → AllZip P xs ys) →
           All (λ x → ∃ λ y → P x y) xs
All-∃← ([] , []) = []
All-∃← (y ∷ ys , p ∷ ps) = (y , p) ∷ All-∃← (ys , ps)

AllZip-map : ∀ {a b p q} {A : Set a} {B : Set b}
               {P : A → B → Set p} {Q : A → B → Set q}
               {xs ys} →
               (f : ∀ {x y} → P x y → Q x y) →
               AllZip P xs ys → AllZip Q xs ys
AllZip-map f [] = []
AllZip-map f (p ∷ ps) = f p ∷ AllZip-map f ps

AllZip-map' : ∀ {a₁ a₂ b₁ b₂ p q}
                {A₁ : Set a₁} {B₁ : Set b₁}
                {A₂ : Set a₂} {B₂ : Set b₂}
                {P : A₁ → B₁ → Set p} {Q : A₂ → B₂ → Set q}
                (f₁ : A₁ → A₂) (f₂ : B₁ → B₂)
                {xs ys} →
                (f : ∀ {x y} → P x y → Q (f₁ x) (f₂ y)) →
                AllZip P xs ys → AllZip Q (map f₁ xs) (map f₂ ys)
AllZip-map' f₁ f₂ f [] = []
AllZip-map' f₁ f₂ f (p ∷ ps) = f p ∷ AllZip-map' f₁ f₂ f ps

AllZip-zip : ∀ {a b c p₁ p₂ q} {A : Set a} {B : Set b} {C : Set c}
               {P₁ : A → B → Set p₁}
               {P₂ : A → C → Set p₂}
               {Q : B → C → Set q}
               {xs ys zs} →
               (f : ∀ {x y z} → P₁ x y → P₂ x z → Q y z) →
               AllZip P₁ xs ys →
               AllZip P₂ xs zs →
               AllZip Q ys zs
AllZip-zip f [] [] = []
AllZip-zip f (p₁ ∷ ps₁) (p₂ ∷ ps₂) = f p₁ p₂ ∷ AllZip-zip f ps₁ ps₂

AllZip-trans : ∀ {a b c p₁ p₂ q} {A : Set a} {B : Set b} {C : Set c}
                 {P₁ : A → B → Set p₁}
                 {P₂ : B → C → Set p₂}
                 {Q : A → C → Set q}
                 {xs ys zs} →
                 (f : ∀ {x y z} → P₁ x y → P₂ y z → Q x z) →
                 AllZip P₁ xs ys →
                 AllZip P₂ ys zs →
                 AllZip Q xs zs
AllZip-trans f [] [] = []
AllZip-trans f (p₁ ∷ ps₁) (p₂ ∷ ps₂) = f p₁ p₂ ∷ AllZip-trans f ps₁ ps₂

AllZip-swap : ∀ {a b p} {A : Set a} {B : Set b} {P : A → B → Set p}
                {xs ys} →
                AllZip P xs ys →
                AllZip (flip P) ys xs
AllZip-swap [] = []
AllZip-swap (p ∷ ps) = p ∷ AllZip-swap ps

AllZip-≡ : ∀ {a} {A : Set a} →
             {xs xs' : List A} →
             AllZip _≡_ xs xs' →
             xs ≡ xs'
AllZip-≡ [] = refl
AllZip-≡ (p ∷ ps) = cong₂ _∷_ p (AllZip-≡ ps)

AllZip-dec : ∀ {a b p} {A : Set a} {B : Set b}
               {P : A → B → Set p} →
               (f : ∀ x y → Dec (P x y)) →
               (xs : List A) →
               (ys : List B) →
               Dec (AllZip P xs ys)
AllZip-dec f [] [] = yes []
AllZip-dec f [] (y ∷ ys) = no (λ ())
AllZip-dec f (x ∷ xs) [] = no (λ ())
AllZip-dec f (x ∷ xs) (y ∷ ys)
  with f x y | AllZip-dec f xs ys
... | yes p | yes ps = yes (p ∷ ps)
... | no ¬p | _ = no (λ { (p ∷ ps) → ¬p p})
... | _ | no ¬ps = no (λ { (p ∷ ps) → ¬ps ps})

AllZip-extract← : ∀ {a b p q} {A : Set a} {B : Set b}
                    {P : A → B → Set p} {Q : A → Set q}
                    {xs ys} →
                    (f : ∀ {x y} → P x y → Q x) →
                    AllZip P xs ys → All Q xs
AllZip-extract← f [] = []
AllZip-extract← f (p ∷ ps) = f p ∷ AllZip-extract← f ps

AllZip-extract→ : ∀ {a b p q} {A : Set a} {B : Set b}
                    {P : A → B → Set p} {Q : B → Set q}
                    {xs ys} →
                    (f : ∀ {x y} → P x y → Q y) →
                    AllZip P xs ys → All Q ys
AllZip-extract→ f [] = []
AllZip-extract→ f (p ∷ ps) = f p ∷ AllZip-extract→ f ps

All-map' : ∀ {a b p q}
             {A : Set a} {P : A → Set p}
             {B : Set b} {Q : B → Set q}
             {xs}
             {f : A → B} →
             (g : ∀ {x} → P x → Q (f x)) →
             All P xs →
             All Q (map f xs)
All-map' g [] = []
All-map' g (p ∷ ps) = g p ∷ All-map' g ps

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
... | no ¬up = no (λ { (._ , there up) → ¬up (_ , up)})

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
