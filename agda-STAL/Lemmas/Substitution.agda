module Lemmas.Substitution where

open import Util
open import Judgments
import Data.Nat.Properties as NP

-- The purpose of this file is
-- to include instances of this record,
-- along with a few additional functions
-- at the bottom of the file
record Substitution⁺ (A : Set) {{S : Substitution A}} : Set1 where
  constructor substitution⁺
  infix 3 _⟦_/_⟧?
  field
    subst-unique : ∀ {v v₁ v₂ : A} {i ι} →
                     v ⟦ i / ι ⟧≡ v₁ →
                     v ⟦ i / ι ⟧≡ v₂ →
                     v₁ ≡ v₂
    _⟦_/_⟧? : ∀ (v : A) i ι → Dec (∃ λ v' → v ⟦ i / ι ⟧≡ v')
    weaken-0 :
      ∀ pos (v : A) →
        weaken pos 0 v ≡ v
  subst-unique-many : ∀ {v v₁ v₂ : A} {is ι} →
                        v ⟦ is / ι ⟧many≡ v₁ →
                        v ⟦ is / ι ⟧many≡ v₂ →
                        v₁ ≡ v₂
  subst-unique-many [] [] = refl
  subst-unique-many (sub-v₁ ∷ subs-v₁) (sub-v₂ ∷ subs-v₂)
    with subst-unique sub-v₁ sub-v₂
  subst-unique-many (sub-v₁ ∷ subs-v₁) (sub-v₂ ∷ subs-v₂)
      | refl with subst-unique-many subs-v₁ subs-v₂
  subst-unique-many (sub-v₁ ∷ subs-v₁) (sub-v₂ ∷ subs-v₂)
      | refl | refl = refl

  _⟦_/_⟧many? : ∀ (v : A) is ι → Dec (∃ λ v' → v ⟦ is / ι ⟧many≡ v')
  v ⟦ [] / ι ⟧many? = yes (v , [])
  v ⟦ i ∷ is / ι ⟧many?
    with v ⟦ i / ι ⟧?
  ... | no ¬sub-v = no (λ { (vₑ , sub-v ∷ subs-v) → ¬sub-v (_ , sub-v)})
  ... | yes (v' , sub-v)
    with v' ⟦ is / ι ⟧many?
  ... | yes (vₑ , subs-v) = yes (vₑ , sub-v ∷ subs-v)
  ... | no ¬subs-v = no help
    where help : ¬ (∃ λ vₑ → v ⟦ i ∷ is / ι ⟧many≡ vₑ)
          help (vₑ , sub-v' ∷ subs-v)
            with subst-unique sub-v sub-v'
          help (vₑ , sub-v' ∷ subs-v)
              | refl = ¬subs-v (vₑ , subs-v)
open Substitution⁺ {{...}} public

match-weaken : ∀ {i a} pos inc → InstantiationMatch i a → InstantiationMatch (weaken pos inc i) a
match-weaken pos inc match-α = match-α
match-weaken pos inc match-ρ = match-ρ

private
  mutual
    subst-uniqueᵗ : ∀ A {{S : Substitution A}} → Set
    subst-uniqueᵗ A = ∀ {v v₁ v₂ : A} {i ι} →
                        v ⟦ i / ι ⟧≡ v₁ →
                        v ⟦ i / ι ⟧≡ v₂ →
                        v₁ ≡ v₂

    subst-τ-unique : subst-uniqueᵗ Type
    subst-τ-unique (subst-α-> ι>ι) subst-α-≡
      with NP.1+n≰n ι>ι
    ... | ()
    subst-τ-unique (subst-α-> ι₁>ι₂) (subst-α-> ι₁>ι₂') = refl
    subst-τ-unique (subst-α-> ι₁>ι₂) (subst-α-< ι₁<ι₂)
      with NP.1+n≰n (NP.<-trans ι₁<ι₂ ι₁>ι₂)
    ... | ()
    subst-τ-unique subst-α-≡ subst-α-≡ = refl
    subst-τ-unique subst-α-≡ (subst-α-> ι>ι)
      with NP.1+n≰n ι>ι
    ... | ()
    subst-τ-unique subst-α-≡ (subst-α-< ι<ι)
      with NP.1+n≰n ι<ι
    ... | ()
    subst-τ-unique (subst-α-< ι<ι) subst-α-≡
      with NP.1+n≰n ι<ι
    ... | ()
    subst-τ-unique (subst-α-< ι₁<ι₂) (subst-α-> ι₁>ι₂)
      with NP.1+n≰n (NP.<-trans ι₁<ι₂ ι₁>ι₂)
    ... | ()
    subst-τ-unique (subst-α-< ι₁<ι₂) (subst-α-< ι₁<ι₂') = refl
    subst-τ-unique subst-int subst-int = refl
    subst-τ-unique subst-ns subst-ns = refl
    subst-τ-unique (subst-∀ sub-Γ₁) (subst-∀ sub-Γ₂)
      rewrite subst-Γ-unique sub-Γ₁ sub-Γ₂ = refl
    subst-τ-unique (subst-tuple sub-τs⁻₁) (subst-tuple sub-τs⁻₂)
      rewrite subst-τs⁻-unique sub-τs⁻₁ sub-τs⁻₂ = refl

    subst-τ⁻-unique : subst-uniqueᵗ InitType
    subst-τ⁻-unique (subst-τ⁻ {φ = φ} sub-τ₁) (subst-τ⁻ sub-τ₂) =
      cong₂ _,_ (subst-τ-unique sub-τ₁ sub-τ₂) refl

    subst-τs⁻-unique : subst-uniqueᵗ (List InitType)
    subst-τs⁻-unique [] [] = refl
    subst-τs⁻-unique (sub-τ⁻₁ ∷ sub-τs⁻₁) (sub-τ⁻₂ ∷ sub-τs⁻₂) =
        cong₂ _∷_ (subst-τ⁻-unique sub-τ⁻₁ sub-τ⁻₂)
                  (subst-τs⁻-unique sub-τs⁻₁ sub-τs⁻₂)

    subst-σ-unique : subst-uniqueᵗ StackType
    subst-σ-unique (subst-ρ-> ι>ι) subst-ρ-≡
      with NP.1+n≰n ι>ι
    ... | ()
    subst-σ-unique (subst-ρ-> ι₁>ι₂) (subst-ρ-> ι₁>ι₂') = refl
    subst-σ-unique (subst-ρ-> ι₁>ι₂) (subst-ρ-< ι₁<ι₂)
      with NP.1+n≰n (NP.<-trans ι₁<ι₂ ι₁>ι₂)
    ... | ()
    subst-σ-unique subst-ρ-≡ subst-ρ-≡ = refl
    subst-σ-unique subst-ρ-≡ (subst-ρ-> ι>ι)
      with NP.1+n≰n ι>ι
    ... | ()
    subst-σ-unique subst-ρ-≡ (subst-ρ-< ι<ι)
      with NP.1+n≰n ι<ι
    ... | ()
    subst-σ-unique (subst-ρ-< ι<ι) subst-ρ-≡
      with NP.1+n≰n ι<ι
    ... | ()
    subst-σ-unique (subst-ρ-< ι₁<ι₂) (subst-ρ-> ι₁>ι₂)
      with NP.1+n≰n (NP.<-trans ι₁<ι₂ ι₁>ι₂)
    ... | ()
    subst-σ-unique (subst-ρ-< ι₁<ι₂) (subst-ρ-< ι₁<ι₂') = refl
    subst-σ-unique [] [] = refl
    subst-σ-unique (sub-τ₁ ∷ sub-σ₁) (sub-τ₂ ∷ sub-σ₂)
      rewrite subst-τ-unique sub-τ₁ sub-τ₂
            | subst-σ-unique sub-σ₁ sub-σ₂ = refl

    subst-Γ-unique : subst-uniqueᵗ RegisterAssignment
    subst-Γ-unique (subst-registerₐ sub-sp₁ sub-regs₁)
                   (subst-registerₐ sub-sp₂ sub-regs₂) =
      cong₂ registerₐ (subst-σ-unique sub-sp₁ sub-sp₂)
                      (subst-regs-unique sub-regs₁ sub-regs₂)

    subst-regs-unique : ∀ {m} → subst-uniqueᵗ (Vec Type m)
    subst-regs-unique {v = []} {[]} {[]} [] [] = refl
    subst-regs-unique {v = τ ∷ τs} {τ₁ ∷ τs₁} {τ₂ ∷ τs₂}
      (sub-τ₁ ∷ sub-τs₁) (sub-τ₂ ∷ sub-τs₂) =
        cong₂ _∷_ (subst-τ-unique sub-τ₁ sub-τ₂)
                  (subst-regs-unique sub-τs₁ sub-τs₂)

  mutual
    _⟦_/_⟧τ? : ∀ τ i ι → Dec (∃ λ τ' → τ ⟦ i / ι ⟧τ≡ τ')
    α⁼ ι₁ ⟦ i / ι₂ ⟧τ? with Nat-cmp ι₁ ι₂
    ... | tri< ι₁<ι₂ _ _ = yes (α⁼ ι₁ , subst-α-< ι₁<ι₂)
    α⁼ ι ⟦ α τ / .ι ⟧τ?
        | tri≈ _ refl _ = yes (weaken 0 ι τ , subst-α-≡)
    α⁼ ι ⟦ ρ σ / .ι ⟧τ?
        | tri≈ _ refl _ =
      no (λ { (._ , subst-α-> ι>ι) → NP.1+n≰n ι>ι
            ; (._ , subst-α-< ι<ι) → NP.1+n≰n ι<ι })
    ... | tri> _ _ ι₁>ι₂ = yes (α⁼ (pred ι₁) , subst-α-> ι₁>ι₂)
    int ⟦ i / ι ⟧τ? = yes (int , subst-int)
    ns ⟦ i / ι ⟧τ? = yes (ns , subst-ns)
    (∀[ Δ ] Γ) ⟦ i / ι ⟧τ? with Γ ⟦ i / length Δ + ι ⟧Γ?
    ... | yes (Γ' , sub-Γ) = yes (∀[ Δ ] Γ' , subst-∀ sub-Γ)
    ... | no ¬sub-Γ = no (λ { (._ , subst-∀ sub-Γ) → ¬sub-Γ (_ , sub-Γ)})
    tuple τs ⟦ i / ι ⟧τ? with τs ⟦ i / ι ⟧τs⁻?
    tuple τs ⟦ i / ι ⟧τ? | yes (τs' , sub-τs) =
      yes (tuple τs' , subst-tuple sub-τs)
    tuple τs ⟦ i / ι ⟧τ? | no ¬sub-τs =
      no (λ { (._ , subst-tuple sub-τs) → ¬sub-τs (_ , sub-τs) })

    _⟦_/_⟧τ⁻? : ∀ τ⁻ i ι → Dec (∃ λ τ⁻' → τ⁻ ⟦ i / ι ⟧τ⁻≡ τ⁻')
    (τ , φ) ⟦ i / ι ⟧τ⁻? with τ ⟦ i / ι ⟧τ?
    (τ , φ) ⟦ i / ι ⟧τ⁻? | yes (τ' , sub-τ) =
      yes ((τ' , φ) , subst-τ⁻ sub-τ)
    (τ , φ) ⟦ i / ι ⟧τ⁻? | no ¬sub-τ =
      no (λ { (._ , subst-τ⁻ sub-τ) → ¬sub-τ (_ , sub-τ) })

    _⟦_/_⟧τs⁻? : ∀ τs⁻ i ι → Dec (∃ λ τs⁻' → τs⁻ ⟦ i / ι ⟧τs⁻≡ τs⁻')
    [] ⟦ i / ι ⟧τs⁻? = yes ([] , [])
    (τ⁻ ∷ τs⁻) ⟦ i / ι ⟧τs⁻? with τ⁻ ⟦ i / ι ⟧τ⁻? | τs⁻ ⟦ i / ι ⟧τs⁻?
    ... | yes (τ⁻' , sub-τ⁻) | yes (τs⁻' , sub-τs⁻) =
      yes (τ⁻' ∷ τs⁻' , sub-τ⁻ ∷ sub-τs⁻)
    ... | no ¬sub-τ⁻ | _ =
      no (λ { (τ⁻' ∷ τs⁻' , sub-τ⁻ ∷ sub-τs⁻) → ¬sub-τ⁻ (τ⁻' , sub-τ⁻) })
    ... | _ | no ¬sub-τs⁻ =
      no (λ { (τ⁻' ∷ τs⁻' , sub-τ⁻ ∷ sub-τs⁻) → ¬sub-τs⁻ (τs⁻' , sub-τs⁻) })

    _⟦_/_⟧σ? : ∀ σ i ι → Dec (∃ λ σ' → σ ⟦ i / ι ⟧σ≡ σ')
    ρ⁼ ι₁ ⟦ i / ι₂ ⟧σ? with Nat-cmp ι₁ ι₂
    ... | tri< ι₁<ι₂ _ _ = yes (ρ⁼ ι₁ , subst-ρ-< ι₁<ι₂)
    ρ⁼ ι ⟦ α τ / .ι ⟧σ?
        | tri≈ _ refl _ =
      no (λ { (._ , subst-ρ-> ι>ι) → NP.1+n≰n ι>ι
            ; (._ , subst-ρ-< ι<ι) → NP.1+n≰n ι<ι })
    ρ⁼ ι ⟦ ρ σ / .ι ⟧σ?
        | tri≈ _ refl _ = yes (weaken 0 ι σ , subst-ρ-≡)
    ... | tri> _ _ ι₁>ι₂ = yes (ρ⁼ (pred ι₁) , subst-ρ-> ι₁>ι₂)
    [] ⟦ i / ι ⟧σ? = yes ([] , [])
    (τ ∷ σ) ⟦ i / ι ⟧σ? with τ ⟦ i / ι ⟧τ? | σ ⟦ i / ι ⟧σ?
    ... | yes (τ' , sub-τ) | yes (σ' , sub-σ) =
      yes (τ' ∷ σ' , sub-τ ∷ sub-σ)
    ... | no ¬sub-τ | _ =
      no (λ { (._ , sub-τ ∷ sub-σ) → ¬sub-τ (_ , sub-τ) })
    ... | _ | no ¬sub-σ =
      no (λ { (._ , sub-τ ∷ sub-σ) → ¬sub-σ (_ , sub-σ) })

    _⟦_/_⟧Γ? : ∀ Γ i ι → Dec (∃ λ Γ' → Γ ⟦ i / ι ⟧Γ≡ Γ')
    registerₐ sp regs ⟦ i / ι ⟧Γ? with sp ⟦ i / ι ⟧σ? | regs ⟦ i / ι ⟧regs?
    ... | yes (sp' , sub-sp) | yes (regs' , sub-regs) =
      yes (registerₐ sp' regs' , subst-registerₐ sub-sp sub-regs)
    ... | no ¬sub-sp | _ =
      no (λ { (._ , subst-registerₐ sub-sp sub-regs) → ¬sub-sp (_ , sub-sp) })
    ... | _ | no ¬sub-regs = no
      (λ { (._ , subst-registerₐ sub-sp sub-regs) →
         ¬sub-regs (_ , sub-regs) })

    _⟦_/_⟧regs? : ∀ {m} (regs : Vec Type m) i ι →
                    Dec (∃ λ regs' → regs ⟦ i / ι ⟧regs≡ regs')
    [] ⟦ i / ι ⟧regs? = yes ([] , [])
    (τ ∷ τs) ⟦ i / ι ⟧regs? with τ ⟦ i / ι ⟧τ? | τs ⟦ i / ι ⟧regs?
    ... | yes (τ' , sub-τ) | yes (τs' , sub-τs) =
      yes (τ' ∷ τs' , sub-τ ∷ sub-τs)
    ... | no ¬sub-τ | _ =
      no (λ { (τ' ∷ τs' , sub-τ ∷ sub-τs) → ¬sub-τ (τ' , sub-τ) })
    ... | _ | no ¬sub-τs =
      no (λ { (τ' ∷ τs' , sub-τ ∷ sub-τs) → ¬sub-τs (τs' , sub-τs) })

  mutual
    weaken-0ᵗ : ∀ A {{_ : Substitution A}} → Set
    weaken-0ᵗ A = ∀ pos (v : A) →
                        weaken pos 0 v ≡ v

    τ-weaken-0 : weaken-0ᵗ Type
    τ-weaken-0 pos (α⁼ ι) with pos ≤? ι
    ... | yes pos≤ι = refl
    ... | no pos≰ι = refl
    τ-weaken-0 pos int = refl
    τ-weaken-0 pos ns = refl
    τ-weaken-0 pos (∀[ Δ ] Γ)
      rewrite Γ-weaken-0 (length Δ + pos) Γ = refl
    τ-weaken-0 pos (tuple τs⁻)
      rewrite τs⁻-weaken-0 pos τs⁻ = refl

    τ⁻-weaken-0 : weaken-0ᵗ InitType
    τ⁻-weaken-0 pos (τ , φ)
      rewrite τ-weaken-0 pos τ = refl

    τs⁻-weaken-0 : weaken-0ᵗ (List InitType)
    τs⁻-weaken-0 pos [] = refl
    τs⁻-weaken-0 pos (τ⁻ ∷ τs⁻)
      rewrite τ⁻-weaken-0 pos τ⁻
            | τs⁻-weaken-0 pos τs⁻ = refl

    σ-weaken-0 : weaken-0ᵗ StackType
    σ-weaken-0 pos (ρ⁼ ι) with pos ≤? ι
    ... | yes pos≤ι = refl
    ... | no pos≰ι = refl
    σ-weaken-0 pos [] = refl
    σ-weaken-0 pos (τ ∷ σ)
      rewrite τ-weaken-0 pos τ
            | σ-weaken-0 pos σ = refl

    Γ-weaken-0 : weaken-0ᵗ RegisterAssignment
    Γ-weaken-0 pos (registerₐ sp regs)
      rewrite σ-weaken-0 pos sp
            | regs-weaken-0 pos regs = refl

    regs-weaken-0 : ∀ {n} → weaken-0ᵗ (Vec Type n)
    regs-weaken-0 pos [] = refl
    regs-weaken-0 pos (τ ∷ τs)
      rewrite τ-weaken-0 pos τ
            | regs-weaken-0 pos τs = refl

Vec-Substitution⁺ : ∀ A {S} {{S⁺ : Substitution⁺ A {{S}}}} m →
                      Substitution⁺ (Vec A m) {{Vec-Substitution A m}}
Vec-Substitution⁺ A {S} {{S⁺}} m = substitution⁺
    unique
    dec
    xs-weaken-0

  where _⟦_/_⟧xs≡_ : ∀ {m} → Vec A m → Instantiation → ℕ → Vec A m → Set
        xs ⟦ i / ι ⟧xs≡ xs' =
          AllZipᵥ (λ x x' → x ⟦ i / ι ⟧≡ x') xs xs'

        unique : ∀ {m i ι} {xs xs₁ xs₂ : Vec A m} →
                   xs ⟦ i / ι ⟧xs≡ xs₁ →
                   xs ⟦ i / ι ⟧xs≡ xs₂ →
                   xs₁ ≡ xs₂
        unique {xs = []} {[]} {[]} [] [] = refl
        unique {xs = x ∷ xs} {x₁ ∷ xs₁} {x₂ ∷ xs₂}
               (sub-x₁ ∷ sub-xs₁) (sub-x₂ ∷ sub-xs₂) =
          cong₂ _∷_ (subst-unique {{S⁺}} sub-x₁ sub-x₂) (unique sub-xs₁ sub-xs₂)

        dec : ∀ {m} (xs : Vec A m) i ι → Dec (∃ λ xs' → xs ⟦ i / ι ⟧xs≡ xs')
        dec [] i ι = yes ([] , [])
        dec (x ∷ xs) i ι with x ⟦ i / ι ⟧? | dec xs i ι
        dec (x ∷ xs) i ι | yes (x' , sub-x) | yes (xs' , sub-xs) =
          yes ((x' ∷ xs') , sub-x ∷ sub-xs)
        dec (x ∷ xs) i ι | no ¬sub-x | _ =
          no (λ { (x' ∷ xs' , sub-x ∷ sub-xs) → ¬sub-x (x' , sub-x)})
        dec (x ∷ xs) i ι | _ | no ¬sub-xs =
          no (λ { (x' ∷ xs' , sub-x ∷ sub-xs) → ¬sub-xs (xs' , sub-xs)})

        xs-weaken-0 : ∀ {n} → weaken-0ᵗ (Vec A n) {{Vec-Substitution A n}}
        xs-weaken-0 pos [] = refl
        xs-weaken-0 pos (x ∷ xs) = cong₂ _∷_ (weaken-0 {{S⁺}} pos x) (xs-weaken-0 pos xs)

List-Substitution⁺ : ∀ A {S} {{S⁺ : Substitution⁺ A {{S}}}} →
                       Substitution⁺ (List A) {{List-Substitution A}}
List-Substitution⁺ A {S} {{S⁺}} = substitution⁺
    unique
    dec
    xs-weaken-0

  where _⟦_/_⟧xs≡_ : List A → Instantiation → ℕ → List A → Set
        xs ⟦ i / ι ⟧xs≡ xs' = AllZip (λ x x' → x ⟦ i / ι ⟧≡ x') xs xs'

        unique : ∀ {i ι} {xs xs₁ xs₂ : List A} →
                   xs ⟦ i / ι ⟧xs≡ xs₁ →
                   xs ⟦ i / ι ⟧xs≡ xs₂ →
                   xs₁ ≡ xs₂
        unique [] [] = refl
        unique (sub-x₁ ∷ sub-xs₁) (sub-x₂ ∷ sub-xs₂)
          = cong₂ _∷_ (subst-unique {{S⁺}} sub-x₁ sub-x₂)
                      (unique sub-xs₁ sub-xs₂)

        dec : ∀ (xs : List A) i ι → Dec (∃ λ xs' → xs ⟦ i / ι ⟧xs≡ xs')
        dec [] i ι = yes ([] , [])
        dec (x ∷ xs) i ι with x ⟦ i / ι ⟧? | dec xs i ι
        dec (x ∷ xs) i ι | yes (x' , sub-x) | yes (xs' , sub-xs) =
          yes (x' ∷ xs' , sub-x ∷ sub-xs)
        dec (x ∷ xs) i ι | no ¬sub-x | _ =
          no (λ { (x' ∷ xs' , sub-x ∷ sub-xs) → ¬sub-x (x' , sub-x)})
        dec (x ∷ xs) i ι | _ | no ¬sub-xs =
          no (λ { (x' ∷ xs' , sub-x ∷ sub-xs) → ¬sub-xs (xs' , sub-xs)})

        xs-weaken-0 : weaken-0ᵗ (List A) {{List-Substitution A}}
        xs-weaken-0 pos [] = refl
        xs-weaken-0 pos (x ∷ xs) = cong₂ _∷_ (weaken-0 {{S⁺}} pos x) (xs-weaken-0 pos xs)

instance
  Type-Substitution⁺ : Substitution⁺ Type
  Type-Substitution⁺ =
    substitution⁺ subst-τ-unique _⟦_/_⟧τ? τ-weaken-0

  TypeVec-Substitution⁺ : ∀ {m} → Substitution⁺ (Vec Type m)
  TypeVec-Substitution⁺ = substitution⁺ subst-regs-unique _⟦_/_⟧regs? regs-weaken-0

  TypeList-Substitution⁺  : Substitution⁺ (List Type)
  TypeList-Substitution⁺ = List-Substitution⁺ Type

  InitType-Substitution⁺  : Substitution⁺ InitType
  InitType-Substitution⁺ =
    substitution⁺ subst-τ⁻-unique  _⟦_/_⟧τ⁻? τ⁻-weaken-0

  InitTypeVec-Substitution⁺ : ∀ {m} → Substitution⁺ (Vec InitType m)
  InitTypeVec-Substitution⁺ = Vec-Substitution⁺ InitType _

  InitTypeList-Substitution⁺  : Substitution⁺ (List InitType)
  InitTypeList-Substitution⁺ = substitution⁺ subst-τs⁻-unique _⟦_/_⟧τs⁻? τs⁻-weaken-0

  StackType-Substitution⁺  : Substitution⁺ StackType
  StackType-Substitution⁺ =
    substitution⁺ subst-σ-unique  _⟦_/_⟧σ? σ-weaken-0

  RegisterAssignment-Substitution⁺  : Substitution⁺ RegisterAssignment
  RegisterAssignment-Substitution⁺ =
    substitution⁺ subst-Γ-unique _⟦_/_⟧Γ? Γ-weaken-0

  Instantiation-Substitution⁺  : Substitution⁺ Instantiation
  Instantiation-Substitution⁺ = substitution⁺ unique dec i-weaken-0
    where unique : ∀ {iₚ ι} {i i₁ i₂} →
                     i ⟦ iₚ / ι ⟧i≡ i₁ →
                     i ⟦ iₚ / ι ⟧i≡ i₂ →
                     i₁ ≡ i₂
          unique (subst-α sub-τ₁) (subst-α sub-τ₂) =
            cong α (subst-unique sub-τ₁ sub-τ₂)
          unique (subst-ρ sub-σ₁) (subst-ρ sub-σ₂) =
            cong ρ (subst-unique sub-σ₁ sub-σ₂)

          dec : ∀ i iₚ ι → Dec (∃ λ i' → i ⟦ iₚ / ι ⟧i≡ i')
          dec (α τ) iₚ ι with τ ⟦ iₚ / ι ⟧?
          ... | yes (τ' , sub-τ) = yes (α τ' , subst-α sub-τ)
          ... | no ¬sub-τ =
            no (λ { (α τ' , subst-α sub-τ) → ¬sub-τ (τ' , sub-τ) })
          dec (ρ σ) iₚ ι with σ ⟦ iₚ / ι ⟧?
          ... | yes (σ' , sub-σ) = yes (ρ σ' , subst-ρ sub-σ)
          ... | no ¬sub-σ =
            no (λ { (ρ σ' , subst-ρ sub-σ) → ¬sub-σ (σ' , sub-σ) })

          i-weaken-0 : weaken-0ᵗ Instantiation
          i-weaken-0 pos (α τ)
            rewrite τ-weaken-0 pos τ = refl
          i-weaken-0 pos (ρ σ)
            rewrite σ-weaken-0 pos σ = refl

  Instantiations-Substitution⁺ : Substitution⁺ Instantiations
  Instantiations-Substitution⁺ = substitution⁺ unique dec is-weaken-0
    where unique : ∀ {i ι} {is is₁ is₂} →
                     is ⟦ i / ι ⟧is≡ is₁ →
                     is ⟦ i / ι ⟧is≡ is₂ →
                     is₁ ≡ is₂
          unique [] [] = refl
          unique (sub-i₁ ∷ sub-is₁) (sub-i₂ ∷ sub-is₂)
            rewrite subst-unique sub-i₁ sub-i₂
                  | unique sub-is₁ sub-is₂ = refl

          dec : ∀ is i ι → Dec (∃ λ is' → is ⟦ i / ι ⟧is≡ is')
          dec [] i ι = yes ([] , [])
          dec (i₁ ∷ is₁) i ι
            with i₁ ⟦ i / length is₁ + ι ⟧? | dec is₁ i ι
          ... | yes (i₂ , sub-i) | yes (is₂ , sub-is) = yes (i₂ ∷ is₂ , sub-i ∷ sub-is)
          ... | no ¬sub-i | _ = no ( λ { (._ , sub-i ∷ sub-is) → ¬sub-i (_ , sub-i) })
          ... | _ | no ¬sub-is = no ( λ { (._ , sub-i ∷ sub-is) → ¬sub-is (_ , sub-is) })

          is-weaken-0 : weaken-0ᵗ Instantiations
          is-weaken-0 pos [] = refl
          is-weaken-0 pos (i ∷ is)
            rewrite weaken-0 (length is + pos) i
                  | is-weaken-0 pos is = refl

  SmallValue-Substitution⁺  : Substitution⁺ SmallValue
  SmallValue-Substitution⁺ = substitution⁺ unique dec v-weaken-0
    where unique : ∀ {i ι} {v v₁ v₂} →
                     v ⟦ i / ι ⟧v≡ v₁ →
                     v ⟦ i / ι ⟧v≡ v₂ →
                     v₁ ≡ v₂
          unique subst-reg subst-reg = refl
          unique subst-globval subst-globval = refl
          unique subst-int subst-int = refl
          unique subst-ns subst-ns = refl
          unique (subst-uninit sub-τ₁) (subst-uninit sub-τ₂)
            rewrite subst-unique sub-τ₁ sub-τ₂ = refl
          unique (subst-Λ sub-v₁ sub-is₁) (subst-Λ sub-v₂ sub-is₂)
            rewrite unique sub-v₁ sub-v₂
                  | subst-unique sub-is₁ sub-is₂ = refl

          dec : ∀ v i ι → Dec (∃ λ v' → v ⟦ i / ι ⟧v≡ v')
          dec (reg ♯r) i ι = yes (reg ♯r , subst-reg)
          dec (globval l) i ι = yes (globval l , subst-globval)
          dec (int i) iₚ ι = yes (int i , subst-int)
          dec ns i ι = yes (ns , subst-ns)
          dec (uninit τ) i ι
            with τ ⟦ i / ι ⟧?
          ... | yes (τ' , sub-τ) = yes (uninit τ' , subst-uninit sub-τ)
          ... | no ¬sub-τ = no (λ { (._ , subst-uninit sub-τ) → ¬sub-τ (_ , sub-τ)})
          dec Λ Δ ∙ v ⟦ is ⟧ i ι
            with dec v i ι | is ⟦ i / length Δ + ι ⟧?
          ... | yes (v' , sub-v) | yes (is' , sub-is) = yes (Λ Δ ∙ v' ⟦ is' ⟧ , subst-Λ sub-v sub-is)
          ... | no ¬sub-v | _ = no (λ { (._ , subst-Λ sub-v sub-is) → ¬sub-v (_ , sub-v) })
          ... | _ | no ¬sub-is = no (λ { (._ , subst-Λ sub-v sub-is) → ¬sub-is (_ , sub-is) })

          v-weaken-0 : weaken-0ᵗ SmallValue
          v-weaken-0 pos (reg ♯r) = refl
          v-weaken-0 pos (globval l) = refl
          v-weaken-0 pos (int i) = refl
          v-weaken-0 pos ns = refl
          v-weaken-0 pos (uninit τs) rewrite weaken-0 pos τs = refl
          v-weaken-0 pos Λ Δ ∙ v ⟦ is ⟧
            rewrite v-weaken-0 (length Δ + pos) v
                  | weaken-0 (length Δ + pos) is = refl

  Instruction-Substitution⁺  : Substitution⁺ Instruction
  Instruction-Substitution⁺ = substitution⁺ unique dec ι-weaken-0
    where unique : ∀ {i ιₚ} {ι ι₁ ι₂} →
                     ι ⟦ i / ιₚ ⟧ι≡ ι₁ →
                     ι ⟦ i / ιₚ ⟧ι≡ ι₂ →
                     ι₁ ≡ ι₂
          unique (subst-add sub-v₁) (subst-add sub-v₂)
            rewrite subst-unique sub-v₁ sub-v₂ = refl
          unique (subst-sub sub-v₁) (subst-sub sub-v₂)
            rewrite subst-unique sub-v₁ sub-v₂ = refl
          unique subst-salloc subst-salloc = refl
          unique subst-sfree subst-sfree = refl
          unique subst-sld subst-sld = refl
          unique subst-sst subst-sst = refl
          unique subst-ld subst-ld = refl
          unique subst-st subst-st = refl
          unique (subst-malloc sub-τs₁) (subst-malloc sub-τs₂)
            rewrite subst-unique sub-τs₁ sub-τs₂ = refl
          unique (subst-mov sub-v₁) (subst-mov sub-v₂)
            rewrite subst-unique sub-v₁ sub-v₂ = refl
          unique (subst-beq sub-v₁) (subst-beq sub-v₂)
            rewrite subst-unique sub-v₁ sub-v₂ = refl

          dec : ∀ ι i ιₚ → Dec (∃ λ ι' → ι ⟦ i / ιₚ ⟧ι≡ ι')
          dec (add ♯rd ♯rs v) i ιₚ
            with v ⟦ i / ιₚ ⟧?
          ... | yes (v' , sub-v) = yes (add ♯rd ♯rs v' , subst-add sub-v)
          ... | no ¬sub-v =
            no (λ { (add .♯rd .♯rs v' , subst-add sub-v) →
              ¬sub-v (v' , sub-v) })
          dec (sub ♯rd ♯rs v) i ιₚ
            with v ⟦ i / ιₚ ⟧?
          ... | yes (v' , sub-v) = yes (sub ♯rd ♯rs v' , subst-sub sub-v)
          ... | no ¬sub-v =
            no (λ { (sub .♯rd .♯rs v' , subst-sub sub-v) →
              ¬sub-v (v' , sub-v) })
          dec (sfree n) i ιₚ = yes (sfree n , subst-sfree)
          dec (salloc n) i ιₚ = yes (salloc n , subst-salloc)
          dec (sld ♯rd i) iₚ ιₚ = yes (sld ♯rd i , subst-sld)
          dec (sst i ♯rs) iₚ ιₚ = yes (sst i ♯rs , subst-sst)
          dec (ld ♯rd ♯rs i) iₚ ιₚ = yes (ld ♯rd ♯rs i , subst-ld)
          dec (st ♯rd i ♯rs) iₚ ιₚ = yes (st ♯rd i ♯rs , subst-st)
          dec (malloc ♯rd τs) i ιₚ
            with τs ⟦ i / ιₚ ⟧?
          ... | yes (τs' , sub-τs) =
            yes (malloc ♯rd τs' , subst-malloc sub-τs)
          ... | no ¬sub-τs =
            no (λ { (malloc .♯rd τs' , subst-malloc sub-τs) →
              ¬sub-τs (τs' , sub-τs) })
          dec (mov ♯rd v) i ιₚ
            with v ⟦ i / ιₚ ⟧?
          ... | yes (v' , sub-v) = yes (mov ♯rd v' , subst-mov sub-v)
          ... | no ¬sub-v =
            no (λ { (mov .♯rd v' , subst-mov sub-v) →
              ¬sub-v (v' , sub-v) })
          dec (beq ♯r v) i ιₚ
            with v ⟦ i / ιₚ ⟧?
          ... | yes (v' , sub-v) = yes (beq ♯r v' , subst-beq sub-v)
          ... | no ¬sub-v =
            no (λ { (beq .♯r v' , subst-beq sub-v) →
              ¬sub-v (v' , sub-v) })

          ι-weaken-0 : weaken-0ᵗ Instruction
          ι-weaken-0 pos (add ♯rd ♯rs v)
            rewrite weaken-0 pos v = refl
          ι-weaken-0 pos (sub ♯rd ♯rs v)
            rewrite weaken-0 pos v = refl
          ι-weaken-0 pos (salloc i) = refl
          ι-weaken-0 pos (sfree i) = refl
          ι-weaken-0 pos (sld ♯rd i) = refl
          ι-weaken-0 pos (sst i ♯rs) = refl
          ι-weaken-0 pos (ld ♯rd ♯rs i) = refl
          ι-weaken-0 pos (st ♯rd i ♯rs) = refl
          ι-weaken-0 pos (malloc ♯rd τs)
            rewrite weaken-0 pos τs = refl
          ι-weaken-0 pos (mov ♯rd v)
            rewrite weaken-0 pos v = refl
          ι-weaken-0 pos (beq ♯r v)
            rewrite weaken-0 pos v = refl

  InstructionSequence-Substitution⁺  : Substitution⁺ InstructionSequence
  InstructionSequence-Substitution⁺ = substitution⁺ unique dec I-weaken-0
    where unique : ∀ {i ι} {I I₁ I₂} →
                     I ⟦ i / ι ⟧I≡ I₁ →
                     I ⟦ i / ι ⟧I≡ I₂ →
                     I₁ ≡ I₂
          unique (subst-~> sub-ι₁ sub-I₁) (subst-~> sub-ι₂ sub-I₂)
            = cong₂ _~>_ (subst-unique sub-ι₁ sub-ι₂) (unique sub-I₁ sub-I₂)
          unique (subst-jmp sub-v₁) (subst-jmp sub-v₂)
            = cong jmp (subst-unique sub-v₁ sub-v₂)

          dec : ∀ I i ι → Dec (∃ λ I' → I ⟦ i / ι ⟧I≡ I')
          dec (ι ~> I) i ιₚ with ι ⟦ i / ιₚ ⟧? | dec I i ιₚ
          ... | yes (ι' , sub-ι) | yes (I' , sub-I) =
            yes (ι' ~> I' , subst-~> sub-ι sub-I)
          ... | no ¬sub-ι | _ =
            no (λ { (ι' ~> I' , subst-~> sub-ι sub-I) → ¬sub-ι (ι' , sub-ι)})
          ... | _ | no ¬sub-I =
            no (λ { (ι' ~> I' , subst-~> sub-ι sub-I) → ¬sub-I (I' , sub-I)})
          dec (jmp v) i ι with v ⟦ i / ι ⟧?
          ... | yes (v' , sub-v) = yes (jmp v' , subst-jmp sub-v)
          ... | no ¬sub-v =
            no (λ { (jmp v' , subst-jmp sub-v) → ¬sub-v (v' , sub-v)})

          I-weaken-0 : weaken-0ᵗ InstructionSequence
          I-weaken-0 pos (ι ~> I)
            rewrite weaken-0 pos ι
                  | I-weaken-0 pos I = refl
          I-weaken-0 pos (jmp v)
            rewrite weaken-0 pos v = refl
