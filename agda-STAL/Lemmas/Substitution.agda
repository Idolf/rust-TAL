module Lemmas.Substitution where

open import Util
open import Judgments
import Data.Nat as N
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
    weaken-weaken :
      ∀ {pos₁ pos₂} inc₁ inc₂ →
        pos₁ ≤ pos₂ →
        pos₂ ≤ pos₁ + inc₁ →
        (v : A) →
        weaken pos₂ inc₂ (weaken pos₁ inc₁ v) ≡ weaken pos₁ (inc₂ + inc₁) v
    weaken-subst :
      ∀ {pos₁ pos₂} inc →
        pos₂ ≤ pos₁ →
        ∀ {i} {v₁ v₂ : A} →
        v₁ ⟦ i / pos₁ ⟧≡ v₂ →
        weaken pos₂ inc v₁ ⟦ i / pos₁ + inc ⟧≡ weaken pos₂ inc v₂
    subst-weaken :
      ∀ {pos₁ pos₂} inc →
        pos₁ ≤ pos₂ →
        pos₂ ≤ inc + pos₁ →
        ∀ {i} (v : A) →
        weaken pos₁ (suc inc) v ⟦ i / pos₂ ⟧≡ weaken pos₁ inc v
    subst-subst :
      ∀ {pos₁ pos₂ i₁ i₁' i₂} →
        i₁ ⟦ i₂ / pos₂ ⟧≡ i₁' →
        {v₁ v₂ v₁' : A}  →
        v₁ ⟦ i₂ / suc pos₁ + pos₂ ⟧≡ v₁' →
        v₁ ⟦ i₁ / pos₁ ⟧≡ v₂ →
        ∃ λ v₂' →
        v₂  ⟦ i₂ / pos₁ + pos₂ ⟧≡ v₂' ×
        v₁' ⟦ i₁' / pos₁ ⟧≡ v₂'
    weaken-exchange :
      ∀ {pos₁ pos₂} inc₁ inc₂ →
        pos₂ ≤ pos₁ →
        (v : A) →
        weaken pos₂ inc₂ (weaken pos₁ inc₁ v) ≡
        weaken (inc₂ + pos₁) inc₁ (weaken pos₂ inc₂ v)
    subst-weaken-inside :
      ∀ pos₁ pos₂ inc {v₁ v₂ : A} {i} →
        v₁ ⟦ i / pos₁ ⟧≡ v₂ →
        weaken (suc (pos₁ + pos₂)) inc v₁ ⟦ weaken pos₂ inc i / pos₁ ⟧≡ weaken (pos₁ + pos₂) inc v₂

  subst-unique-many : ∀ {v v₁ v₂ : A} {is ι} →
                        v ⟦ is / ι ⟧many≡ v₁ →
                        v ⟦ is / ι ⟧many≡ v₂ →
                        v₁ ≡ v₂
  subst-unique-many [] [] = refl
  subst-unique-many (sub-v₁ ∷ subs-v₁) (sub-v₂ ∷ subs-v₂)
    with subst-unique sub-v₁ sub-v₂
  subst-unique-many (sub-v₁ ∷ subs-v₁) (sub-v₂ ∷ subs-v₂)
      | refl
    with subst-unique-many subs-v₁ subs-v₂
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

  subst-subst-many : ∀ {vᵢ₁ vᵢ₂ vₒ₁ : A}
                       {i is₁ is₂ pos₁ pos₂} →
                       is₁ ⟦ i / pos₁ ⟧≡ is₂ →
                       vᵢ₁ ⟦ i / pos₂ + length is₁ + pos₁ ⟧≡ vᵢ₂ →
                       vᵢ₁ ⟦ is₁ / pos₂ ⟧many≡ vₒ₁ →
                       ∃ λ vₒ₂ →
                         vₒ₁ ⟦ i / pos₂ + pos₁ ⟧≡ vₒ₂ ×
                         vᵢ₂ ⟦ is₂ / pos₂ ⟧many≡ vₒ₂
  subst-subst-many {pos₂ = pos₂} [] sub-vᵢ []
    rewrite +-comm pos₂ 0
    = _ , sub-vᵢ , []
  subst-subst-many {is₁ = i₁ ∷ is₁} {is₂ = i₂ ∷ is₂} {pos₁} {pos₂} (sub-i ∷ sub-is) sub-vᵢ (sub₁-v ∷ subs₁-v)
    with begin
      (pos₂ + suc (length is₁)) + pos₁
    ≡⟨ +-comm pos₂ (suc (length is₁)) ∥ (λ v → v + pos₁) ⟩
      (suc (length is₁) + pos₂) + pos₁
    ≡⟨ +-comm (length is₁) pos₂ ∥ (λ v → suc v + pos₁) ⟩
      (suc pos₂ + length is₁) + pos₁
    ≡⟨ +-assoc (suc pos₂) (length is₁) pos₁ ⟩
      suc pos₂ + (length is₁ + pos₁)
    ∎ where open Eq-Reasoning
  ... | eq
    rewrite eq
    with subst-subst {pos₁ = pos₂} {pos₂ = length is₁ + pos₁}  sub-i sub-vᵢ sub₁-v
  ... | vₘ₂ , sub-vₘ , sub₂-v
    rewrite sym (+-assoc pos₂ (length is₁) pos₁)
    with subst-subst-many sub-is sub-vₘ subs₁-v
  ... | vₒ₂ , sub-vₒ , subs₂-v
    = vₒ₂ , sub-vₒ , sub₂-v ∷ subs₂-v

  subst-weaken-inside-many :
    ∀ pos₁ pos₂ inc {v₁ v₂ : A} {is} →
      v₁ ⟦ is / pos₁ ⟧many≡ v₂ →
      weaken (length is + pos₁ + pos₂) inc v₁ ⟦ weaken pos₂ inc is / pos₁ ⟧many≡ weaken (pos₁ + pos₂) inc v₂
  subst-weaken-inside-many pos₁ pos₂ inc [] = []
  subst-weaken-inside-many pos₁ pos₂ inc {is = i ∷ is} (sub-v ∷ subs-v)
    with subst-weaken-inside pos₁ (length is + pos₂) inc sub-v
  ... | sub-v'
    with begin
      pos₁ + (length is + pos₂)
    ⟨ +-assoc pos₁ (length is) pos₂ ⟩≡
      (pos₁ + length is) + pos₂
    ≡⟨ +-comm pos₁ (length is) ∥ (λ v → v + pos₂) ⟩
      (length is + pos₁) + pos₂
    ∎ where open Eq-Reasoning
  ... | eq
    rewrite eq
    = sub-v' ∷ subst-weaken-inside-many pos₁ pos₂ inc subs-v

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

  mutual
    weaken-weakenᵗ : ∀ A {{_ : Substitution A}} → Set
    weaken-weakenᵗ A = ∀ {pos₁ pos₂} inc₁ inc₂ →
                          pos₁ ≤ pos₂ →
                          pos₂ ≤ pos₁ + inc₁ →
                          (v : A) →
                          weaken pos₂ inc₂ (weaken pos₁ inc₁ v) ≡ weaken pos₁ (inc₂ + inc₁) v

    τ-weaken-weaken : weaken-weakenᵗ Type
    τ-weaken-weaken {pos₁} {pos₂} inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (α⁼ ι)
      with pos₁ ≤? ι
    ... | yes pos₁≤ι
      with pos₂ ≤? inc₁ + ι
    ... | no pos₂≰inc₁+ι
      rewrite +-comm pos₁ inc₁
      with pos₂≰inc₁+ι (Nat-≤-trans pos₂≤pos₁+inc₁ (l+m≤l+n inc₁ pos₁≤ι))
    ... | ()
    τ-weaken-weaken {pos₁} {pos₂} inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (α⁼ ι)
        | yes pos₁≤ι | yes pos₂≤inc₁+ι
      rewrite +-assoc inc₂ inc₁ ι = refl
    τ-weaken-weaken {pos₁} {pos₂} inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (α⁼ ι)
        | no pos₁≰ι
      with pos₂ ≤? ι
    ... | no pos₂≰ι = refl
    ... | yes pos₂≤ι
      with pos₁≰ι (Nat-≤-trans pos₁≤pos₂ pos₂≤ι)
    ... | ()
    τ-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ int = refl
    τ-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ ns = refl
    τ-weaken-weaken {pos₁} {pos₂} inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (∀[ Δ ] Γ)
      with l+m≤l+n (length Δ) pos₂≤pos₁+inc₁
    ... | pos≤pos
      rewrite sym (+-assoc (length Δ) pos₁ inc₁)
            | Γ-weaken-weaken {length Δ + pos₁} {length Δ + pos₂} inc₁ inc₂ (l+m≤l+n (length Δ) pos₁≤pos₂) pos≤pos Γ
      = refl
    τ-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (tuple τs⁻)
      rewrite τs⁻-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ τs⁻ = refl

    τ⁻-weaken-weaken : weaken-weakenᵗ InitType
    τ⁻-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (τ , φ)
      rewrite τ-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ τ = refl

    τs⁻-weaken-weaken : weaken-weakenᵗ (List InitType)
    τs⁻-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ [] = refl
    τs⁻-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (τ⁻ ∷ τs⁻)
      rewrite τ⁻-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ τ⁻
            | τs⁻-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ τs⁻ = refl

    σ-weaken-weaken : weaken-weakenᵗ StackType
    σ-weaken-weaken {pos₁} {pos₂} inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (ρ⁼ ι)
      with pos₁ ≤? ι
    ... | yes pos₁≤ι
      with pos₂ ≤? inc₁ + ι
    ... | no pos₂≰inc₁+ι
      rewrite +-comm pos₁ inc₁
      with pos₂≰inc₁+ι (Nat-≤-trans pos₂≤pos₁+inc₁ (l+m≤l+n inc₁ pos₁≤ι))
    ... | ()
    σ-weaken-weaken {pos₁} {pos₂} inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (ρ⁼ ι)
        | yes pos₁≤ι | yes pos₂≤inc₁+ι
      rewrite +-assoc inc₂ inc₁ ι = refl
    σ-weaken-weaken {pos₁} {pos₂} inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (ρ⁼ ι)
        | no pos₁≰ι
      with pos₂ ≤? ι
    ... | no pos₂≰ι = refl
    ... | yes pos₂≤ι
      with pos₁≰ι (Nat-≤-trans pos₁≤pos₂ pos₂≤ι)
    ... | ()
    σ-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ [] = refl
    σ-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (τ ∷ τs)
      rewrite τ-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ τ
            | σ-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ τs = refl

    Γ-weaken-weaken : weaken-weakenᵗ RegisterAssignment
    Γ-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (registerₐ sp regs)
      rewrite σ-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ sp
            | regs-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ regs = refl

    regs-weaken-weaken : ∀ {n} → weaken-weakenᵗ (Vec Type n)
    regs-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ [] = refl
    regs-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (τ ∷ τs)
      rewrite τ-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ τ
            | regs-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ τs = refl

  >-help₁ : ∀ inc pos {ι} →
              ι > inc →
              pos + ι > inc + pos
  >-help₁ inc pos ι>inc
    rewrite +-comm (suc inc) pos = l+m≤l+n pos ι>inc

  pred-helper : ∀ a b {n} → b > n → pred (a + b) ≡ a + pred b
  pred-helper a (suc b) (s≤s b>n)
    rewrite +-comm a (suc b)
          | +-comm b a = refl

  mutual
    weaken-substᵗ : ∀ A {{S : Substitution A}} → Set
    weaken-substᵗ A = ∀ {pos₁ pos₂} inc →
                        pos₂ ≤ pos₁ →
                        ∀ {i} {v₁ v₂ : A} →
                        v₁ ⟦ i / pos₁ ⟧≡ v₂ →
                        weaken pos₂ inc v₁ ⟦ i / pos₁ + inc ⟧≡ weaken pos₂ inc v₂
    τ-weaken-subst : weaken-substᵗ Type
    τ-weaken-subst {pos₁} {pos₂} inc pos₂≤pos₁ {v₁ = α⁼ ι} (subst-α-> ι>pos₁)
      with pos₂ ≤? ι | pos₂ ≤? pred ι
    ... | no pos₂≰ι | _
      with pos₂≰ι (Nat-≤-trans pos₂≤pos₁ (NP.≤⇒pred≤ _ _ ι>pos₁))
    ... | ()
    τ-weaken-subst inc pos₂≤pos₁ {v₁ = α⁼ ι} (subst-α-> ι>pos₁)
        | _ | no pos₂≰ι'
      with pos₂≰ι' (Nat-≤-trans pos₂≤pos₁ (NP.pred-mono ι>pos₁))
    ... | ()
    τ-weaken-subst {pos₁} inc pos₂≤pos₁ {v₁ = α⁼ ι} (subst-α-> ι>pos₁)
        | yes pos₂≤ι | yes pos₂≤ι'
      with subst-α-> (>-help₁ pos₁ inc ι>pos₁)
    ... | sub-τ'
      rewrite pred-helper inc ι ι>pos₁
        = sub-τ'
    τ-weaken-subst {pos₁} {pos₂} inc pos₂≤pos₁ {α τ} subst-α-≡
      rewrite τ-weaken-weaken pos₁ inc z≤n pos₂≤pos₁ τ
      with pos₂ ≤? pos₁
    ... | yes pos₂≤pos₁'
      rewrite +-comm pos₁ inc
        = subst-α-≡
    ... | no pos₂≰pos₁
      with pos₂≰pos₁ pos₂≤pos₁
    ... | ()
    τ-weaken-subst {pos₁} {pos₂} inc pos₂≤pos₁ {v₁ = α⁼ ι} (subst-α-< ι<pos₁)
      with pos₂ ≤? ι
    ... | no pos₂≰ι
      = subst-α-< (Nat-≤-trans ι<pos₁ (NP.m≤m+n pos₁ inc))
    ... | yes pos₂≤ι
      rewrite +-comm pos₁ inc
      = subst-α-< (l+m<l+n inc ι<pos₁)
    τ-weaken-subst inc pos₂≤pos₁ subst-int = subst-int
    τ-weaken-subst inc pos₂≤pos₁ subst-ns = subst-ns
    τ-weaken-subst {pos₁} {pos₂} inc pos₂≤pos₁ {v₁ = ∀[ Δ ] Γ} (subst-∀ sub-Γ)
      with Γ-weaken-subst inc (l+m≤l+n (length Δ) pos₂≤pos₁) sub-Γ
    ... | sub-Γ'
      rewrite +-assoc (length Δ) pos₁ inc
        = subst-∀ sub-Γ'
    τ-weaken-subst inc pos₂≤pos₁ (subst-tuple sub-τs⁻)
      = subst-tuple (τs⁻-weaken-subst inc pos₂≤pos₁ sub-τs⁻)

    τ⁻-weaken-subst : weaken-substᵗ InitType
    τ⁻-weaken-subst inc pos₂≤pos₁ (subst-τ⁻ sub-τ)
      = subst-τ⁻ (τ-weaken-subst inc pos₂≤pos₁ sub-τ)

    τs⁻-weaken-subst : weaken-substᵗ (List InitType)
    τs⁻-weaken-subst inc pos₂≤pos₁ [] = []
    τs⁻-weaken-subst inc pos₂≤pos₁ (sub-τ⁻ ∷ sub-τs⁻) = τ⁻-weaken-subst inc pos₂≤pos₁ sub-τ⁻ ∷ τs⁻-weaken-subst inc pos₂≤pos₁ sub-τs⁻

    σ-weaken-subst : weaken-substᵗ StackType
    σ-weaken-subst {pos₁} {pos₂} inc pos₂≤pos₁ {v₁ = ρ⁼ ι} (subst-ρ-> ι>pos₁)
      with pos₂ ≤? ι | pos₂ ≤? pred ι
    ... | no pos₂≰ι | _
      with pos₂≰ι (Nat-≤-trans pos₂≤pos₁ (NP.≤⇒pred≤ _ _ ι>pos₁))
    ... | ()
    σ-weaken-subst inc pos₂≤pos₁ {v₁ = ρ⁼ ι} (subst-ρ-> ι>pos₁)
        | _ | no pos₂≰ι'
      with pos₂≰ι' (Nat-≤-trans pos₂≤pos₁ (NP.pred-mono ι>pos₁))
    ... | ()
    σ-weaken-subst {pos₁} inc pos₂≤pos₁ {v₁ = ρ⁼ ι} (subst-ρ-> ι>pos₁)
        | yes pos₂≤ι | yes pos₂≤ι'
      with subst-ρ-> (>-help₁ pos₁ inc ι>pos₁)
    ... | sub-σ'
      rewrite pred-helper inc ι ι>pos₁
        = sub-σ'
    σ-weaken-subst {pos₁} {pos₂} inc pos₂≤pos₁ {ρ σ} subst-ρ-≡
      rewrite σ-weaken-weaken pos₁ inc z≤n pos₂≤pos₁ σ
      with pos₂ ≤? pos₁
    ... | yes pos₂≤pos₁'
      rewrite +-comm pos₁ inc
        = subst-ρ-≡
    ... | no pos₂≰pos₁
      with pos₂≰pos₁ pos₂≤pos₁
    ... | ()
    σ-weaken-subst {pos₁} {pos₂} inc pos₂≤pos₁ {v₁ = ρ⁼ ι} (subst-ρ-< ι<pos₁)
      with pos₂ ≤? ι
    ... | no pos₂≰ι
      = subst-ρ-< (Nat-≤-trans ι<pos₁ (NP.m≤m+n pos₁ inc))
    ... | yes pos₂≤ι
      rewrite +-comm pos₁ inc
      = subst-ρ-< (l+m<l+n inc ι<pos₁)
    σ-weaken-subst inc pos₂≤pos₁ [] = []
    σ-weaken-subst inc pos₂≤pos₁ (sub-τ ∷ sub-σ) = τ-weaken-subst inc pos₂≤pos₁ sub-τ ∷ σ-weaken-subst inc pos₂≤pos₁ sub-σ

    Γ-weaken-subst : weaken-substᵗ RegisterAssignment
    Γ-weaken-subst inc pos₂≤pos₁ (subst-registerₐ sub-sp sub-regs)
      = subst-registerₐ (σ-weaken-subst inc pos₂≤pos₁ sub-sp) (regs-weaken-subst inc pos₂≤pos₁ sub-regs)

    regs-weaken-subst : ∀ {n} → weaken-substᵗ (Vec Type n)
    regs-weaken-subst inc pos₂≤pos₁ [] = []
    regs-weaken-subst inc pos₂≤pos₁ (sub-τ ∷ sub-τs)
      = τ-weaken-subst inc pos₂≤pos₁ sub-τ ∷ regs-weaken-subst inc pos₂≤pos₁ sub-τs

  mutual
    subst-weakenᵗ : ∀ A {{S : Substitution A}} → Set
    subst-weakenᵗ A = ∀ {pos₁ pos₂} inc →
                        pos₁ ≤ pos₂ →
                        pos₂ ≤ inc + pos₁ →
                        ∀ {i} (v : A) →
                        weaken pos₁ (suc inc) v ⟦ i / pos₂ ⟧≡ weaken pos₁ inc v

    τ-subst-weaken : subst-weakenᵗ Type
    τ-subst-weaken {pos₁} inc pos₁≤pos₂ pos₂≤inc+pos₁ (α⁼ ι)
      with pos₁ ≤? ι
    ... | yes pos₁≤ι = subst-α-> (s≤s (Nat-≤-trans pos₂≤inc+pos₁ (l+m≤l+n inc pos₁≤ι)))
    ... | no pos₁≰ι = subst-α-< (Nat-≤-trans (NP.≰⇒> pos₁≰ι) pos₁≤pos₂)
    τ-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ int = subst-int
    τ-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ ns = subst-ns
    τ-subst-weaken {pos₁} {pos₂} inc pos₁≤pos₂ pos₂≤inc+pos₁ (∀[ Δ ] Γ)
      with begin
        length Δ + pos₂
      ≤⟨ l+m≤l+n (length Δ) pos₂≤inc+pos₁ ⟩
        length Δ + (inc + pos₁)
      ≡⟨ +-comm (length Δ) (inc + pos₁) ⟩
        (inc + pos₁) + length Δ
      ≡⟨ +-assoc inc pos₁ (length Δ) ⟩
        inc + (pos₁ + length Δ)
      ≡⟨ cong (λ v → inc + v) (+-comm pos₁ (length Δ)) ⟩
        inc + (length Δ + pos₁)
      ∎ where open N.≤-Reasoning
    ... | len-≤
      = subst-∀ (Γ-subst-weaken inc (l+m≤l+n (length Δ) pos₁≤pos₂) len-≤ Γ)
    τ-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ (tuple τs⁻)
      = subst-tuple (τs⁻-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ τs⁻)

    τ⁻-subst-weaken : subst-weakenᵗ InitType
    τ⁻-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ (τ , φ)
      = subst-τ⁻ (τ-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ τ)

    τs⁻-subst-weaken : subst-weakenᵗ (List InitType)
    τs⁻-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ [] = []
    τs⁻-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ (τ⁻ ∷ τs⁻)
      = τ⁻-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ τ⁻ ∷ τs⁻-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ τs⁻

    σ-subst-weaken : subst-weakenᵗ StackType
    σ-subst-weaken {pos₁} inc pos₁≤pos₂ pos₂≤inc+pos₁ (ρ⁼ ι)
      with pos₁ ≤? ι
    ... | yes pos₁≤ι = subst-ρ-> (s≤s (Nat-≤-trans pos₂≤inc+pos₁ (l+m≤l+n inc pos₁≤ι)))
    ... | no pos₁≰ι = subst-ρ-< (Nat-≤-trans (NP.≰⇒> pos₁≰ι) pos₁≤pos₂)
    σ-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ [] = []
    σ-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ (τ ∷ τs)
      = τ-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ τ ∷ σ-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ τs

    Γ-subst-weaken : subst-weakenᵗ RegisterAssignment
    Γ-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ (registerₐ sp regs)
      = subst-registerₐ (σ-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ sp) (regs-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ regs)

    regs-subst-weaken : ∀ {n} → subst-weakenᵗ (Vec Type n)
    regs-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ [] = []
    regs-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ (τ ∷ τs)
      = τ-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ τ ∷ regs-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ τs

  sub-α-helper :
    ∀ {ι pos i τ} →
      ι > pos →
      α⁼ ι ⟦ i / pos ⟧≡ τ →
      ∃ λ ι' →
        ι ≡ suc ι' ×
        τ ≡ α⁼ ι'
  sub-α-helper (s≤s ι≥pos) (subst-α-> (s≤s ι≥pos')) = _ , refl , refl
  sub-α-helper ι>pos subst-α-≡
    with NP.1+n≰n ι>pos
  ... | ()
  sub-α-helper ι>pos (subst-α-< ι<pos)
    with NP.1+n≰n (NP.<-trans ι<pos ι>pos)
  ... | ()

  sub-ρ-helper :
    ∀ {ι pos i σ} →
      ι > pos →
      ρ⁼ ι ⟦ i / pos ⟧≡ σ →
      ∃ λ ι' →
        ι ≡ suc ι' ×
        σ ≡ ρ⁼ ι'
  sub-ρ-helper (s≤s ι≥pos) (subst-ρ-> (s≤s ι≥pos')) = _ , refl , refl
  sub-ρ-helper ι>pos subst-ρ-≡
    with NP.1+n≰n ι>pos
  ... | ()
  sub-ρ-helper ι>pos (subst-ρ-< ι<pos)
    with NP.1+n≰n (NP.<-trans ι<pos ι>pos)
  ... | ()

  mutual
    subst-substᵗ : ∀ A {{_ : Substitution A}} → Set
    subst-substᵗ A = ∀ {pos₁ pos₂ i₁ i₁' i₂} →
                       i₁ ⟦ i₂ / pos₂ ⟧≡ i₁' →
                       {v₁ v₂ v₁' : A}  →
                       v₁ ⟦ i₂ / suc pos₁ + pos₂ ⟧≡ v₁' →
                       v₁ ⟦ i₁ / pos₁ ⟧≡ v₂ →
                       ∃ λ v₂' →
                         v₂  ⟦ i₂ / pos₁ + pos₂ ⟧≡ v₂' ×
                         v₁' ⟦ i₁' / pos₁ ⟧≡ v₂'

    τ-subst-subst : subst-substᵗ Type
    τ-subst-subst {pos₁} {pos₂} sub-i (subst-α-> (s≤s ι>pos)) (subst-α-> (s≤s ι>pos'))
      rewrite +-comm pos₁ (suc pos₂)
            | +-comm pos₂ pos₁
      = _ , subst-α-> ι>pos , subst-α-> (Nat-≤-trans (s≤s (NP.m≤m+n pos₁ pos₂)) ι>pos)
    τ-subst-subst {pos₁} {pos₂} sub-i (subst-α-> ι>pos) subst-α-≡
      with NP.1+n≰n (Nat-≤-trans (s≤s (NP.≤-step (NP.m≤m+n pos₁ pos₂))) ι>pos)
    ... | ()
    τ-subst-subst {pos₁} {pos₂} sub-i (subst-α-> ι>pos) (subst-α-< ι<pos)
      with NP.1+n≰n (Nat-≤-trans ι<pos (Nat-≤-trans (NP.≤-steps 2 (NP.m≤m+n pos₁ pos₂)) ι>pos))
    ... | ()
    τ-subst-subst {pos₁} {pos₂} {i₂ = α τ} sub-i subst-α-≡ sub-τ₁'
      with sub-α-helper (s≤s (NP.m≤m+n pos₁ pos₂)) sub-τ₁'
    ... | ι' , eq₁ , eq₂
      rewrite sym (cong pred eq₁)
            | eq₂
        = _ , subst-α-≡ , τ-subst-weaken (pos₁ + pos₂) z≤n (Nat-≤-trans (NP.m≤m+n pos₁ pos₂) (NP.m≤m+n (pos₁ + pos₂) zero)) τ
    τ-subst-subst {pos₁} {pos₂} sub-i (subst-α-< (s≤s ι≤pos)) (subst-α-> (s≤s ι≥pos'))
        = _ , subst-α-< ι≤pos , subst-α-> (s≤s ι≥pos')
    τ-subst-subst {pos₁} {pos₂} (subst-α sub-τ) (subst-α-< ι<pos) subst-α-≡
      rewrite +-comm pos₁ pos₂
        = _ , τ-weaken-subst pos₁ z≤n sub-τ , subst-α-≡
    τ-subst-subst {pos₁} {pos₂} sub-i (subst-α-< ι<pos) (subst-α-< ι<pos')
      = _ , subst-α-< (Nat-≤-trans ι<pos' (NP.m≤m+n pos₁ pos₂)) , subst-α-< ι<pos'
    τ-subst-subst sub-i subst-int subst-int = int , subst-int , subst-int
    τ-subst-subst sub-i subst-ns subst-ns = ns , subst-ns , subst-ns
    τ-subst-subst {pos₁} {pos₂} sub-i {∀[ Δ ] Γ₁} (subst-∀ sub-Γ₁) (subst-∀ sub-Γ₁')
      with begin
        length Δ + suc (pos₁ + pos₂)
      ⟨ +-assoc (length Δ) 1 (pos₁ + pos₂) ⟩≡
        (length Δ + 1) + (pos₁ + pos₂)
      ≡⟨ +-comm (length Δ) 1 ∥ (λ v → v + (pos₁ + pos₂)) ⟩
        suc (length Δ) + (pos₁ + pos₂)
      ≡⟨ refl ⟩
        suc (length Δ + (pos₁ + pos₂))
      ⟨ cong suc (+-assoc (length Δ) pos₁ pos₂) ⟩≡
        suc (length Δ + pos₁ + pos₂)
      ∎ where open Eq-Reasoning
    ... | eq
      rewrite eq
      with Γ-subst-subst sub-i sub-Γ₁ sub-Γ₁'
    ... | Γ₂' , sub-Γ₂ , sub-Γ₂'
      rewrite +-assoc (length Δ) pos₁ pos₂
      = ∀[ Δ ] Γ₂' , subst-∀ sub-Γ₂ , subst-∀ sub-Γ₂'
    τ-subst-subst sub-i (subst-tuple sub-τs⁻₁) (subst-tuple sub-τs⁻₁')
      with τs⁻-subst-subst sub-i sub-τs⁻₁ sub-τs⁻₁'
    ... | τs⁻₂ , sub-τs⁻₂ , sub-τs⁻₂'
      = _ , subst-tuple sub-τs⁻₂ , subst-tuple sub-τs⁻₂'

    τ⁻-subst-subst : subst-substᵗ InitType
    τ⁻-subst-subst sub-i (subst-τ⁻ sub-τ₁) (subst-τ⁻ sub-τ₁')
      with τ-subst-subst sub-i sub-τ₁ sub-τ₁'
    ... | τ⁻₂ , sub-τ⁻₂ , sub-τ⁻₂'
      = _ , subst-τ⁻ sub-τ⁻₂ , subst-τ⁻ sub-τ⁻₂'

    τs⁻-subst-subst : subst-substᵗ (List InitType)
    τs⁻-subst-subst sub-i [] [] = [] , [] , []
    τs⁻-subst-subst sub-i (sub-τ₁⁻ ∷ sub-τs₁⁻) (sub-τ₁⁻' ∷ sub-τs₁⁻')
      with τ⁻-subst-subst sub-i sub-τ₁⁻ sub-τ₁⁻'
    ... | τ⁻₂ , sub-τ⁻₂ , sub-τ⁻₂'
      with τs⁻-subst-subst sub-i sub-τs₁⁻ sub-τs₁⁻'
    ... | τs⁻₂ , sub-τs⁻₂ , sub-τs⁻₂'
      = _ , sub-τ⁻₂ ∷ sub-τs⁻₂ , sub-τ⁻₂' ∷ sub-τs⁻₂'

    σ-subst-subst : subst-substᵗ StackType
    σ-subst-subst {pos₁} {pos₂} sub-i (subst-ρ-> (s≤s ι>pos)) (subst-ρ-> (s≤s ι>pos'))
      rewrite +-comm pos₁ (suc pos₂)
            | +-comm pos₂ pos₁
      = _ , subst-ρ-> ι>pos , subst-ρ-> (Nat-≤-trans (s≤s (NP.m≤m+n pos₁ pos₂)) ι>pos)
    σ-subst-subst {pos₁} {pos₂} sub-i (subst-ρ-> ι>pos) subst-ρ-≡
      with NP.1+n≰n (Nat-≤-trans (s≤s (NP.≤-step (NP.m≤m+n pos₁ pos₂))) ι>pos)
    ... | ()
    σ-subst-subst {pos₁} {pos₂} sub-i (subst-ρ-> ι>pos) (subst-ρ-< ι<pos)
      with NP.1+n≰n (Nat-≤-trans ι<pos (Nat-≤-trans (NP.≤-steps 2 (NP.m≤m+n pos₁ pos₂)) ι>pos))
    ... | ()
    σ-subst-subst {pos₁} {pos₂} {i₂ = ρ σ} sub-i subst-ρ-≡ sub-σ₁'
      with sub-ρ-helper (s≤s (NP.m≤m+n pos₁ pos₂)) sub-σ₁'
    ... | ι' , eq₁ , eq₂
      rewrite sym (cong pred eq₁)
            | eq₂
        = _ , subst-ρ-≡ , σ-subst-weaken (pos₁ + pos₂) z≤n (Nat-≤-trans (NP.m≤m+n pos₁ pos₂) (NP.m≤m+n (pos₁ + pos₂) zero)) σ
    σ-subst-subst {pos₁} {pos₂} sub-i (subst-ρ-< (s≤s ι≤pos)) (subst-ρ-> (s≤s ι≥pos'))
        = _ , subst-ρ-< ι≤pos , subst-ρ-> (s≤s ι≥pos')
    σ-subst-subst {pos₁} {pos₂} (subst-ρ sub-σ) (subst-ρ-< ι<pos) subst-ρ-≡
      rewrite +-comm pos₁ pos₂
        = _ , σ-weaken-subst pos₁ z≤n sub-σ , subst-ρ-≡
    σ-subst-subst {pos₁} {pos₂} sub-i (subst-ρ-< ι<pos) (subst-ρ-< ι<pos')
      = _ , subst-ρ-< (Nat-≤-trans ι<pos' (NP.m≤m+n pos₁ pos₂)) , subst-ρ-< ι<pos'
    σ-subst-subst sub-i [] [] = [] , [] , []
    σ-subst-subst sub-i (sub-τ₁ ∷ sub-σ₁) (sub-τ₁' ∷ sub-σ₁')
      with τ-subst-subst sub-i sub-τ₁ sub-τ₁'
    ... | τ₂ , sub-τ₂ , sub-τ₂'
      with σ-subst-subst sub-i sub-σ₁ sub-σ₁'
    ... | σ₂ , sub-σ₂ , sub-σ₂'
      = _ , sub-τ₂ ∷ sub-σ₂ , sub-τ₂' ∷ sub-σ₂'

    Γ-subst-subst : subst-substᵗ RegisterAssignment
    Γ-subst-subst sub-i (subst-registerₐ sub-σ₁ sub-τs₁) (subst-registerₐ sub-σ₁' sub-τs₁')
      with σ-subst-subst sub-i sub-σ₁ sub-σ₁'
    ... | σ₂ , sub-σ₂ , sub-σ₂'
      with regs-subst-subst sub-i sub-τs₁ sub-τs₁'
    ... | τs₂ , sub-τs₂ , sub-τs₂'
      = _ , subst-registerₐ sub-σ₂ sub-τs₂ , subst-registerₐ sub-σ₂' sub-τs₂'

    regs-subst-subst : ∀ {n} → subst-substᵗ (Vec Type n)
    regs-subst-subst sub-i [] [] = [] , [] , []
    regs-subst-subst sub-i (sub-τ₁ ∷ sub-τs₁) (sub-τ₁' ∷ sub-τs₁')
      with τ-subst-subst sub-i sub-τ₁ sub-τ₁'
    ... | τ₂ , sub-τ₂ , sub-τ₂'
      with regs-subst-subst sub-i sub-τs₁ sub-τs₁'
    ... | τs₂ , sub-τs₂ , sub-τs₂'
      = _ , sub-τ₂ ∷ sub-τs₂ , sub-τ₂' ∷ sub-τs₂'

  mutual
    weaken-exchangeᵗ : ∀ A {{_ : Substitution A}} → Set
    weaken-exchangeᵗ A = ∀ {pos₁ pos₂} inc₁ inc₂ →
                           pos₂ ≤ pos₁ →
                           (v : A) →
                           weaken pos₂ inc₂ (weaken pos₁ inc₁ v) ≡
                           weaken (inc₂ + pos₁) inc₁ (weaken pos₂ inc₂ v)

    τ-weaken-exchange : weaken-exchangeᵗ Type
    τ-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (α⁼ ι)
      with pos₁ ≤? ι | pos₂ ≤? ι
    τ-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (α⁼ ι)
        | yes pos₁≤ι | yes pos₂≤ι
      with pos₂ ≤? (inc₁ + ι) | (inc₂ + pos₁) ≤? (inc₂ + ι)
    τ-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (α⁼ ι)
        | yes pos₁≤ι | yes pos₂≤ι | yes pos₂≤inc₁+ι | yes inc₂+pos₁≤inc₂+ι
      with begin
        inc₂ + (inc₁ + ι)
      ⟨ +-assoc inc₂ inc₁ ι ⟩≡
        (inc₂ + inc₁) + ι
      ≡⟨ +-comm inc₂ inc₁ ∥ (λ v → v + ι) ⟩
        (inc₁ + inc₂) + ι
      ≡⟨ +-assoc inc₁ inc₂ ι ⟩
        inc₁ + (inc₂ + ι)
      ∎ where open Eq-Reasoning
    ... | eq = cong α⁼ eq
    τ-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (α⁼ ι)
        | yes pos₁≤ι | yes pos₂≤ι | no pos₂≰inc₁+ι | _
      with pos₂≰inc₁+ι (NP.≤-steps inc₁ pos₂≤ι)
    ... | ()
    τ-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (α⁼ ι)
        | yes pos₁≤ι | yes pos₂≤ι | _ | no inc₂+pos₁≰inc₂+ι
      with inc₂+pos₁≰inc₂+ι (l+m≤l+n inc₂ pos₁≤ι)
    ... | ()
    τ-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (α⁼ ι)
        | yes pos₁≤ι | no pos₂≰ι
      with pos₂≰ι (Nat-≤-trans pos₂≤pos₁ pos₁≤ι)
    ... | ()
    τ-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (α⁼ ι)
        | no pos₁≰ι | yes pos₂≤ι
      with pos₂ ≤? ι | (inc₂ + pos₁) ≤? (inc₂ + ι)
    τ-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (α⁼ ι)
        | no pos₁≰ι | yes pos₂≤ι | yes pos₂≤ι' | no inc₂+pos₁≰inc₂+ι
        = refl
    τ-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (α⁼ ι)
        | no pos₁≰ι | yes pos₂≤ι | no pos₂≰ι | _
      with pos₂≰ι pos₂≤ι
    ... | ()
    τ-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (α⁼ ι)
        | no pos₁≰ι | yes pos₂≤ι | _ | yes inc₂+pos₁≤inc₂+ι
      with pos₁≰ι (l+m≤l+n⁻¹ inc₂ inc₂+pos₁≤inc₂+ι)
    ... | ()
    τ-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (α⁼ ι)
        | no pos₁≰ι | no pos₂≰ι
      with pos₂ ≤? ι | inc₂ + pos₁ ≤? ι
    τ-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (α⁼ ι)
        | no pos₁≰ι | no pos₂≰ι | no pos₂≰ι' | no inc₂+pos₁≰ι' = refl
    τ-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (α⁼ ι)
        | no pos₁≰ι | no pos₂≰ι | yes pos₂≤ι | _
      with pos₂≰ι pos₂≤ι
    ... | ()
    τ-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (α⁼ ι)
        | no pos₁≰ι | no pos₂≰ι | _ | yes inc₂+pos₁≤ι
      with pos₁≰ι (Nat-≤-trans (NP.n≤m+n inc₂ pos₁) inc₂+pos₁≤ι)
    ... | ()
    τ-weaken-exchange inc₁ inc₂ pos₂≤pos₁ int = refl
    τ-weaken-exchange inc₁ inc₂ pos₂≤pos₁ ns = refl
    τ-weaken-exchange {pos₁} inc₁ inc₂ pos₂≤pos₁ (∀[ Δ ] Γ)
      with Γ-weaken-exchange inc₁ inc₂ (l+m≤l+n (length Δ) pos₂≤pos₁) Γ
    ... | eq₁
      with begin
        inc₂ + (length Δ + pos₁)
      ⟨ +-assoc inc₂ (length Δ) pos₁ ⟩≡
        (inc₂ + length Δ) + pos₁
      ≡⟨ +-comm inc₂ (length Δ) ∥ (λ v → v + pos₁) ⟩
        (length Δ + inc₂) + pos₁
      ≡⟨ +-assoc (length Δ) inc₂ pos₁ ⟩
        length Δ + (inc₂ + pos₁)
      ∎ where open Eq-Reasoning
    ... | eq₂
      rewrite eq₂ | eq₁ = refl
    τ-weaken-exchange inc₁ inc₂ pos₂≤pos₁ (tuple τs⁻)
      rewrite τs⁻-weaken-exchange inc₁ inc₂ pos₂≤pos₁ τs⁻ = refl

    τ⁻-weaken-exchange : weaken-exchangeᵗ InitType
    τ⁻-weaken-exchange inc₁ inc₂ pos₂≤pos₁ (τ , φ)
      rewrite τ-weaken-exchange inc₁ inc₂ pos₂≤pos₁ τ = refl

    τs⁻-weaken-exchange : weaken-exchangeᵗ (List InitType)
    τs⁻-weaken-exchange inc₁ inc₂ pos₂≤pos₁ [] = refl
    τs⁻-weaken-exchange inc₁ inc₂ pos₂≤pos₁ (τ⁻ ∷ τs⁻)
      rewrite τ⁻-weaken-exchange inc₁ inc₂ pos₂≤pos₁ τ⁻
            | τs⁻-weaken-exchange inc₁ inc₂ pos₂≤pos₁ τs⁻ = refl

    σ-weaken-exchange : weaken-exchangeᵗ StackType
    σ-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (ρ⁼ ι)
      with pos₁ ≤? ι | pos₂ ≤? ι
    σ-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (ρ⁼ ι)
        | yes pos₁≤ι | yes pos₂≤ι
      with pos₂ ≤? (inc₁ + ι) | (inc₂ + pos₁) ≤? (inc₂ + ι)
    σ-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (ρ⁼ ι)
        | yes pos₁≤ι | yes pos₂≤ι | yes pos₂≤inc₁+ι | yes inc₂+pos₁≤inc₂+ι
      with begin
        inc₂ + (inc₁ + ι)
      ⟨ +-assoc inc₂ inc₁ ι ⟩≡
        (inc₂ + inc₁) + ι
      ≡⟨ +-comm inc₂ inc₁ ∥ (λ v → v + ι) ⟩
        (inc₁ + inc₂) + ι
      ≡⟨ +-assoc inc₁ inc₂ ι ⟩
        inc₁ + (inc₂ + ι)
      ∎ where open Eq-Reasoning
    ... | eq = cong ρ⁼ eq
    σ-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (ρ⁼ ι)
        | yes pos₁≤ι | yes pos₂≤ι | no pos₂≰inc₁+ι | _
      with pos₂≰inc₁+ι (NP.≤-steps inc₁ pos₂≤ι)
    ... | ()
    σ-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (ρ⁼ ι)
        | yes pos₁≤ι | yes pos₂≤ι | _ | no inc₂+pos₁≰inc₂+ι
      with inc₂+pos₁≰inc₂+ι (l+m≤l+n inc₂ pos₁≤ι)
    ... | ()
    σ-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (ρ⁼ ι)
        | yes pos₁≤ι | no pos₂≰ι
      with pos₂≰ι (Nat-≤-trans pos₂≤pos₁ pos₁≤ι)
    ... | ()
    σ-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (ρ⁼ ι)
        | no pos₁≰ι | yes pos₂≤ι
      with pos₂ ≤? ι | (inc₂ + pos₁) ≤? (inc₂ + ι)
    σ-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (ρ⁼ ι)
        | no pos₁≰ι | yes pos₂≤ι | yes pos₂≤ι' | no inc₂+pos₁≰inc₂+ι
        = refl
    σ-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (ρ⁼ ι)
        | no pos₁≰ι | yes pos₂≤ι | no pos₂≰ι | _
      with pos₂≰ι pos₂≤ι
    ... | ()
    σ-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (ρ⁼ ι)
        | no pos₁≰ι | yes pos₂≤ι | _ | yes inc₂+pos₁≤inc₂+ι
      with pos₁≰ι (l+m≤l+n⁻¹ inc₂ inc₂+pos₁≤inc₂+ι)
    ... | ()
    σ-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (ρ⁼ ι)
        | no pos₁≰ι | no pos₂≰ι
      with pos₂ ≤? ι | inc₂ + pos₁ ≤? ι
    σ-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (ρ⁼ ι)
        | no pos₁≰ι | no pos₂≰ι | no pos₂≰ι' | no inc₂+pos₁≰ι' = refl
    σ-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (ρ⁼ ι)
        | no pos₁≰ι | no pos₂≰ι | yes pos₂≤ι | _
      with pos₂≰ι pos₂≤ι
    ... | ()
    σ-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (ρ⁼ ι)
        | no pos₁≰ι | no pos₂≰ι | _ | yes inc₂+pos₁≤ι
      with pos₁≰ι (Nat-≤-trans (NP.n≤m+n inc₂ pos₁) inc₂+pos₁≤ι)
    ... | ()
    σ-weaken-exchange inc₁ inc₂ pos₂≤pos₁ [] = refl
    σ-weaken-exchange inc₁ inc₂ pos₂≤pos₁ (τ ∷ σ)
      rewrite τ-weaken-exchange inc₁ inc₂ pos₂≤pos₁ τ
            | σ-weaken-exchange inc₁ inc₂ pos₂≤pos₁ σ = refl

    Γ-weaken-exchange : weaken-exchangeᵗ RegisterAssignment
    Γ-weaken-exchange inc₁ inc₂ pos₂≤pos₁ (registerₐ sp regs)
      rewrite σ-weaken-exchange inc₁ inc₂ pos₂≤pos₁ sp
            | regs-weaken-exchange inc₁ inc₂ pos₂≤pos₁ regs = refl

    regs-weaken-exchange : ∀ {n} → weaken-exchangeᵗ (Vec Type n)
    regs-weaken-exchange inc₁ inc₂ pos₂≤pos₁ [] = refl
    regs-weaken-exchange inc₁ inc₂ pos₂≤pos₁ (τ ∷ τs)
      rewrite τ-weaken-exchange inc₁ inc₂ pos₂≤pos₁ τ
            | regs-weaken-exchange inc₁ inc₂ pos₂≤pos₁ τs = refl

  mutual
    subst-weaken-insideᵗ : ∀ A {{S : Substitution A}} → Set
    subst-weaken-insideᵗ A =
      ∀ pos₁ pos₂ inc {v₁ v₂ : A} {i} →
        v₁ ⟦ i / pos₁ ⟧≡ v₂ →
        weaken (suc (pos₁ + pos₂)) inc v₁ ⟦ weaken pos₂ inc i / pos₁ ⟧≡ weaken (pos₁ + pos₂) inc v₂

    τ-subst-weaken-inside : subst-weaken-insideᵗ Type
    τ-subst-weaken-inside pos₁ pos₂ inc {α⁼ zero} (subst-α-> ())
    τ-subst-weaken-inside pos₁ pos₂ inc {α⁼ (suc ι)} .{α⁼ ι} (subst-α-> (s≤s ι>pos₁))
      with suc (pos₁ + pos₂) ≤? suc ι | pos₁ + pos₂ ≤? ι
    ... | yes 1+pos₁+pos₂≤1+ι | yes pos₁+pos₂≤ι
      rewrite +-comm inc (suc ι)
            | +-comm ι inc = subst-α-> (s≤s (NP.≤-steps inc ι>pos₁))
    τ-subst-weaken-inside pos₁ pos₂ inc {α⁼ (suc ι)} .{α⁼ ι} (subst-α-> (s≤s ι>pos₁))
        | yes (s≤s pos₁+pos₂≤ι) | no pos₁+pos₂≰ι
      with pos₁+pos₂≰ι pos₁+pos₂≤ι
    ... | ()
    τ-subst-weaken-inside pos₁ pos₂ inc {α⁼ (suc ι)} .{α⁼ ι} (subst-α-> (s≤s ι>pos₁))
        | no 1+pos₁+pos₂≰1+ι | yes pos₁+pos₂≤ι
      with 1+pos₁+pos₂≰1+ι (s≤s pos₁+pos₂≤ι)
    ... | ()
    τ-subst-weaken-inside pos₁ pos₂ inc {α⁼ (suc ι)} .{α⁼ ι} (subst-α-> (s≤s ι>pos₁))
        | no 1+pos₁+pos₂≰1+ι | no pos₁+pos₂≰ι = subst-α-> (s≤s ι>pos₁)
    τ-subst-weaken-inside pos₁ pos₂ inc {i = α τ} subst-α-≡
      with suc (pos₁ + pos₂) ≤? pos₁
    ... | yes 1+pos₁+pos₂≤pos₁
      with NP.1+n≰n (Nat-≤-trans (s≤s (NP.m≤m+n pos₁ pos₂)) 1+pos₁+pos₂≤pos₁)
    ... | ()
    τ-subst-weaken-inside pos₁ pos₂ inc {i = α τ} subst-α-≡
        | no 1+pos₁+pos₂≤?pos₁
        rewrite sym (τ-weaken-exchange {pos₁ = pos₂} inc pos₁ z≤n τ)
        = subst-α-≡
    τ-subst-weaken-inside pos₁ pos₂ inc {α⁼ ι} .{α⁼ ι} (subst-α-< ι<pos₁)
      with suc (pos₁ + pos₂) ≤? ι | pos₁ + pos₂ ≤? ι
    τ-subst-weaken-inside pos₁ pos₂ inc {α⁼ ι} .{α⁼ ι} (subst-α-< ι<pos₁)
        | yes 1+pos₁+pos₂≤ι | _
      with NP.1+n≰n (Nat-≤-trans ι<pos₁ (Nat-≤-trans (NP.≤-step (NP.m≤m+n pos₁ pos₂)) 1+pos₁+pos₂≤ι))
    ... | ()
    τ-subst-weaken-inside pos₁ pos₂ inc {α⁼ ι} .{α⁼ ι} (subst-α-< ι<pos₁)
        | _ | yes pos₁+pos₂≤ι
      with NP.1+n≰n (Nat-≤-trans ι<pos₁ (Nat-≤-trans (NP.m≤m+n pos₁ pos₂) pos₁+pos₂≤ι))
    ... | ()
    τ-subst-weaken-inside pos₁ pos₂ inc {α⁼ ι} .{α⁼ ι} (subst-α-< ι<pos₁)
        | no 1+pos₁+pos₂≰ι | no pos₁+pos₂≰ι = subst-α-< ι<pos₁
    τ-subst-weaken-inside pos₁ pos₂ inc subst-int = subst-int
    τ-subst-weaken-inside pos₁ pos₂ inc subst-ns = subst-ns
    τ-subst-weaken-inside pos₁ pos₂ inc {∀[ Δ ] Γ} (subst-∀ sub-Γ)
      with Γ-subst-weaken-inside (length Δ + pos₁) pos₂ inc sub-Γ
    ... | sub-Γ'
      with begin
        suc (length Δ + (pos₁ + pos₂))
      ≡⟨ +-comm 1 (length Δ) ∥ (λ v → v + (pos₁ + pos₂)) ⟩
        (length Δ + 1) + (pos₁ + pos₂)
      ≡⟨ +-assoc (length Δ) 1 (pos₁ + pos₂) ⟩
        length Δ + suc (pos₁ + pos₂)
      ∎ where open Eq-Reasoning
    ... | eq
      rewrite +-assoc (length Δ) pos₁ pos₂ | eq
      = subst-∀ sub-Γ'
    τ-subst-weaken-inside pos₁ pos₂ inc (subst-tuple sub-τs⁻)
      = subst-tuple (τs⁻-subst-weaken-inside pos₁ pos₂ inc sub-τs⁻)

    τ⁻-subst-weaken-inside : subst-weaken-insideᵗ InitType
    τ⁻-subst-weaken-inside pos₁ pos₂ inc (subst-τ⁻ sub-τ)
      = subst-τ⁻ (τ-subst-weaken-inside pos₁ pos₂ inc sub-τ)

    τs⁻-subst-weaken-inside : subst-weaken-insideᵗ (List InitType)
    τs⁻-subst-weaken-inside pos₁ pos₂ inc [] = []
    τs⁻-subst-weaken-inside pos₁ pos₂ inc (sub-τ⁻ ∷ sub-τs⁻)
      = τ⁻-subst-weaken-inside pos₁ pos₂ inc sub-τ⁻ ∷
        τs⁻-subst-weaken-inside pos₁ pos₂ inc sub-τs⁻

    σ-subst-weaken-inside : subst-weaken-insideᵗ StackType
    σ-subst-weaken-inside pos₁ pos₂ inc {ρ⁼ zero} (subst-ρ-> ())
    σ-subst-weaken-inside pos₁ pos₂ inc {ρ⁼ (suc ι)} .{ρ⁼ ι} (subst-ρ-> (s≤s ι>pos₁))
      with suc (pos₁ + pos₂) ≤? suc ι | pos₁ + pos₂ ≤? ι
    ... | yes 1+pos₁+pos₂≤1+ι | yes pos₁+pos₂≤ι
      rewrite +-comm inc (suc ι)
            | +-comm ι inc = subst-ρ-> (s≤s (NP.≤-steps inc ι>pos₁))
    σ-subst-weaken-inside pos₁ pos₂ inc {ρ⁼ (suc ι)} .{ρ⁼ ι} (subst-ρ-> (s≤s ι>pos₁))
        | yes (s≤s pos₁+pos₂≤ι) | no pos₁+pos₂≰ι
      with pos₁+pos₂≰ι pos₁+pos₂≤ι
    ... | ()
    σ-subst-weaken-inside pos₁ pos₂ inc {ρ⁼ (suc ι)} .{ρ⁼ ι} (subst-ρ-> (s≤s ι>pos₁))
        | no 1+pos₁+pos₂≰1+ι | yes pos₁+pos₂≤ι
      with 1+pos₁+pos₂≰1+ι (s≤s pos₁+pos₂≤ι)
    ... | ()
    σ-subst-weaken-inside pos₁ pos₂ inc {ρ⁼ (suc ι)} .{ρ⁼ ι} (subst-ρ-> (s≤s ι>pos₁))
        | no 1+pos₁+pos₂≰1+ι | no pos₁+pos₂≰ι = subst-ρ-> (s≤s ι>pos₁)
    σ-subst-weaken-inside pos₁ pos₂ inc {i = ρ σ} subst-ρ-≡
      with suc (pos₁ + pos₂) ≤? pos₁
    ... | yes 1+pos₁+pos₂≤pos₁
      with NP.1+n≰n (Nat-≤-trans (s≤s (NP.m≤m+n pos₁ pos₂)) 1+pos₁+pos₂≤pos₁)
    ... | ()
    σ-subst-weaken-inside pos₁ pos₂ inc {i = ρ σ} subst-ρ-≡
        | no 1+pos₁+pos₂≤?pos₁
        rewrite sym (σ-weaken-exchange {pos₁ = pos₂} inc pos₁ z≤n σ)
        = subst-ρ-≡
    σ-subst-weaken-inside pos₁ pos₂ inc {ρ⁼ ι} .{ρ⁼ ι} (subst-ρ-< ι<pos₁)
      with suc (pos₁ + pos₂) ≤? ι | pos₁ + pos₂ ≤? ι
    σ-subst-weaken-inside pos₁ pos₂ inc {ρ⁼ ι} .{ρ⁼ ι} (subst-ρ-< ι<pos₁)
        | yes 1+pos₁+pos₂≤ι | _
      with NP.1+n≰n (Nat-≤-trans ι<pos₁ (Nat-≤-trans (NP.≤-step (NP.m≤m+n pos₁ pos₂)) 1+pos₁+pos₂≤ι))
    ... | ()
    σ-subst-weaken-inside pos₁ pos₂ inc {ρ⁼ ι} .{ρ⁼ ι} (subst-ρ-< ι<pos₁)
        | _ | yes pos₁+pos₂≤ι
      with NP.1+n≰n (Nat-≤-trans ι<pos₁ (Nat-≤-trans (NP.m≤m+n pos₁ pos₂) pos₁+pos₂≤ι))
    ... | ()
    σ-subst-weaken-inside pos₁ pos₂ inc {ρ⁼ ι} .{ρ⁼ ι} (subst-ρ-< ι<pos₁)
      | no 1+pos₁+pos₂≰ι | no pos₁+pos₂≰ι = subst-ρ-< ι<pos₁
    σ-subst-weaken-inside pos₁ pos₂ inc [] = []
    σ-subst-weaken-inside pos₁ pos₂ inc (sub-τ ∷ sub-τs)
      = τ-subst-weaken-inside pos₁ pos₂ inc sub-τ ∷
        σ-subst-weaken-inside pos₁ pos₂ inc sub-τs

    Γ-subst-weaken-inside : subst-weaken-insideᵗ RegisterAssignment
    Γ-subst-weaken-inside pos₁ pos₂ inc (subst-registerₐ sub-sp sub-regs)
      = subst-registerₐ (σ-subst-weaken-inside pos₁ pos₂ inc sub-sp)
                        (regs-subst-weaken-inside pos₁ pos₂ inc sub-regs)

    regs-subst-weaken-inside : ∀ {n} → subst-weaken-insideᵗ (Vec Type n)
    regs-subst-weaken-inside pos₁ pos₂ inc [] = []
    regs-subst-weaken-inside pos₁ pos₂ inc (sub-τ ∷ sub-τs)
      = τ-subst-weaken-inside pos₁ pos₂ inc sub-τ ∷
        regs-subst-weaken-inside pos₁ pos₂ inc sub-τs

Vec-Substitution⁺ : ∀ A {S} {{S⁺ : Substitution⁺ A {{S}}}} m →
                      Substitution⁺ (Vec A m) {{Vec-Substitution A m}}
Vec-Substitution⁺ A {S} {{S⁺}} m = substitution⁺
    unique
    dec
    xs-weaken-0
    xs-weaken-weaken
    xs-weaken-subst
    xs-subst-weaken
    xs-subst-subst
    xs-weaken-exchange
    xs-subst-weaken-inside

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

        xs-weaken-weaken : ∀ {n} → weaken-weakenᵗ (Vec A n) {{Vec-Substitution A n}}
        xs-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ [] = refl
        xs-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (x ∷ xs)
          = cong₂ _∷_ (weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ x) (xs-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ xs)

        xs-weaken-subst : ∀ {n} → weaken-substᵗ (Vec A n) {{Vec-Substitution A n}}
        xs-weaken-subst inc pos₂≤pos₁ [] = []
        xs-weaken-subst inc pos₂≤pos₁ (sub-x ∷ sub-xs)
          = weaken-subst inc pos₂≤pos₁ sub-x ∷ xs-weaken-subst inc pos₂≤pos₁ sub-xs

        xs-subst-weaken : ∀ {n} → subst-weakenᵗ (Vec A n) {{Vec-Substitution A n}}
        xs-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ [] = []
        xs-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ (x ∷ xs)
          = subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ x ∷ xs-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ xs

        xs-subst-subst : ∀ {n} → subst-substᵗ (Vec A n) {{Vec-Substitution A n}}
        xs-subst-subst sub-i [] [] = [] , [] , []
        xs-subst-subst sub-i (sub-x₁ ∷ sub-xs₁) (sub-x₁' ∷ sub-xs₁')
          with subst-subst sub-i sub-x₁ sub-x₁'
        ... | x₂ , sub-x₂ , sub-x₂'
          with xs-subst-subst sub-i sub-xs₁ sub-xs₁'
        ... | xs₂ , sub-xs₂ , sub-xs₂'
          = _ , sub-x₂ ∷ sub-xs₂ , sub-x₂' ∷ sub-xs₂'

        xs-weaken-exchange : ∀ {n} → weaken-exchangeᵗ (Vec A n) {{Vec-Substitution A n}}
        xs-weaken-exchange inc₁ inc₂ pos₂≤pos₁ [] = refl
        xs-weaken-exchange inc₁ inc₂ pos₂≤pos₁ (x ∷ xs)
         = cong₂ _∷_ (weaken-exchange inc₁ inc₂ pos₂≤pos₁ x)
                     (xs-weaken-exchange inc₁ inc₂ pos₂≤pos₁ xs)

        xs-subst-weaken-inside : ∀ {n} → subst-weaken-insideᵗ (Vec A n) {{Vec-Substitution A n}}
        xs-subst-weaken-inside pos₁ pos₂ inc [] = []
        xs-subst-weaken-inside pos₁ pos₂ inc (sub-x ∷ sub-xs)
          = subst-weaken-inside pos₁ pos₂ inc sub-x ∷
            xs-subst-weaken-inside pos₁ pos₂ inc sub-xs

List-Substitution⁺ : ∀ A {S} {{S⁺ : Substitution⁺ A {{S}}}} →
                       Substitution⁺ (List A) {{List-Substitution A}}
List-Substitution⁺ A {S} {{S⁺}} = substitution⁺
    unique
    dec
    xs-weaken-0
    xs-weaken-weaken
    xs-weaken-subst
    xs-subst-weaken
    xs-subst-subst
    xs-weaken-exchange
    xs-subst-weaken-inside

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

        xs-weaken-weaken : weaken-weakenᵗ (List A) {{List-Substitution A}}
        xs-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ [] = refl
        xs-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (x ∷ xs)
          = cong₂ _∷_ (weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ x) (xs-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ xs)

        xs-weaken-subst : weaken-substᵗ (List A) {{List-Substitution A}}
        xs-weaken-subst inc pos₂≤pos₁ [] = []
        xs-weaken-subst inc pos₂≤pos₁ (sub-x ∷ sub-xs)
          = weaken-subst inc pos₂≤pos₁ sub-x ∷ xs-weaken-subst inc pos₂≤pos₁ sub-xs

        xs-subst-weaken : subst-weakenᵗ (List A) {{List-Substitution A}}
        xs-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ [] = []
        xs-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ (x ∷ xs)
          = subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ x ∷ xs-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ xs

        xs-subst-subst : subst-substᵗ (List A) {{List-Substitution A}}
        xs-subst-subst sub-i [] [] = [] , [] , []
        xs-subst-subst sub-i (sub-x₁ ∷ sub-xs₁) (sub-x₁' ∷ sub-xs₁')
          with subst-subst sub-i sub-x₁ sub-x₁'
        ... | x₂ , sub-x₂ , sub-x₂'
          with xs-subst-subst sub-i sub-xs₁ sub-xs₁'
        ... | xs₂ , sub-xs₂ , sub-xs₂'
          = _ , sub-x₂ ∷ sub-xs₂ , sub-x₂' ∷ sub-xs₂'

        xs-weaken-exchange : weaken-exchangeᵗ (List A) {{List-Substitution A}}
        xs-weaken-exchange inc₁ inc₂ pos₂≤pos₁ [] = refl
        xs-weaken-exchange inc₁ inc₂ pos₂≤pos₁ (x ∷ xs)
         = cong₂ _∷_ (weaken-exchange inc₁ inc₂ pos₂≤pos₁ x)
                     (xs-weaken-exchange inc₁ inc₂ pos₂≤pos₁ xs)

        xs-subst-weaken-inside : subst-weaken-insideᵗ (List A) {{List-Substitution A}}
        xs-subst-weaken-inside pos₁ pos₂ inc [] = []
        xs-subst-weaken-inside pos₁ pos₂ inc (sub-x ∷ sub-xs)
          = subst-weaken-inside pos₁ pos₂ inc sub-x ∷
            xs-subst-weaken-inside pos₁ pos₂ inc sub-xs

instance
  Type-Substitution⁺ : Substitution⁺ Type
  Type-Substitution⁺ =
    substitution⁺ subst-τ-unique _⟦_/_⟧τ? τ-weaken-0 τ-weaken-weaken τ-weaken-subst τ-subst-weaken τ-subst-subst τ-weaken-exchange τ-subst-weaken-inside

  TypeVec-Substitution⁺ : ∀ {m} → Substitution⁺ (Vec Type m)
  TypeVec-Substitution⁺ = substitution⁺ subst-regs-unique _⟦_/_⟧regs? regs-weaken-0 regs-weaken-weaken regs-weaken-subst regs-subst-weaken regs-subst-subst regs-weaken-exchange regs-subst-weaken-inside

  TypeList-Substitution⁺ : Substitution⁺ (List Type)
  TypeList-Substitution⁺ = List-Substitution⁺ Type

  InitType-Substitution⁺ : Substitution⁺ InitType
  InitType-Substitution⁺ =
    substitution⁺ subst-τ⁻-unique  _⟦_/_⟧τ⁻? τ⁻-weaken-0 τ⁻-weaken-weaken τ⁻-weaken-subst τ⁻-subst-weaken τ⁻-subst-subst τ⁻-weaken-exchange τ⁻-subst-weaken-inside

  InitTypeVec-Substitution⁺ : ∀ {m} → Substitution⁺ (Vec InitType m)
  InitTypeVec-Substitution⁺ = Vec-Substitution⁺ InitType _

  InitTypeList-Substitution⁺ : Substitution⁺ (List InitType)
  InitTypeList-Substitution⁺ = substitution⁺ subst-τs⁻-unique _⟦_/_⟧τs⁻? τs⁻-weaken-0 τs⁻-weaken-weaken τs⁻-weaken-subst τs⁻-subst-weaken τs⁻-subst-subst τs⁻-weaken-exchange τs⁻-subst-weaken-inside

  StackType-Substitution⁺ : Substitution⁺ StackType
  StackType-Substitution⁺ =
    substitution⁺ subst-σ-unique  _⟦_/_⟧σ? σ-weaken-0 σ-weaken-weaken σ-weaken-subst σ-subst-weaken σ-subst-subst σ-weaken-exchange σ-subst-weaken-inside

  RegisterAssignment-Substitution⁺ : Substitution⁺ RegisterAssignment
  RegisterAssignment-Substitution⁺ =
    substitution⁺ subst-Γ-unique _⟦_/_⟧Γ? Γ-weaken-0 Γ-weaken-weaken Γ-weaken-subst Γ-subst-weaken Γ-subst-subst Γ-weaken-exchange Γ-subst-weaken-inside

  Instantiation-Substitution⁺ : Substitution⁺ Instantiation
  Instantiation-Substitution⁺ = substitution⁺ unique dec i-weaken-0 i-weaken-weaken i-weaken-subst i-subst-weaken i-subst-subst i-weaken-exchange i-subst-weaken-inside
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

          i-weaken-weaken : weaken-weakenᵗ Instantiation
          i-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (α τ)
            rewrite weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ τ = refl
          i-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (ρ σ)
            rewrite weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ σ = refl

          i-weaken-subst : weaken-substᵗ Instantiation
          i-weaken-subst inc pos₂≤pos₁ (subst-α sub-τ) =
            subst-α (τ-weaken-subst inc pos₂≤pos₁ sub-τ)
          i-weaken-subst inc pos₂≤pos₁ (subst-ρ sub-σ) =
            subst-ρ (σ-weaken-subst inc pos₂≤pos₁ sub-σ)

          i-subst-weaken : subst-weakenᵗ Instantiation
          i-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ (α τ)
            = subst-α (subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ τ)
          i-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ (ρ σ)
            = subst-ρ (subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ σ)

          i-subst-subst : subst-substᵗ Instantiation
          i-subst-subst sub-i (subst-α sub-τ₁) (subst-α sub-τ₁')
            with subst-subst sub-i sub-τ₁ sub-τ₁'
          ... | τ₂ , sub-τ₂ , sub-τ₂'
            = _ , subst-α sub-τ₂ , subst-α sub-τ₂'
          i-subst-subst sub-i (subst-ρ sub-σ₁) (subst-ρ sub-σ₁')
            with subst-subst sub-i sub-σ₁ sub-σ₁'
          ... | σ₂ , sub-σ₂ , sub-σ₂'
            = _ , subst-ρ sub-σ₂ , subst-ρ sub-σ₂'

          i-weaken-exchange : weaken-exchangeᵗ Instantiation
          i-weaken-exchange inc₁ inc₂ pos₂≤pos₁ (α τ)
            = cong α (weaken-exchange inc₁ inc₂ pos₂≤pos₁ τ)
          i-weaken-exchange inc₁ inc₂ pos₂≤pos₁ (ρ σ)
            = cong ρ (weaken-exchange inc₁ inc₂ pos₂≤pos₁ σ)

          i-subst-weaken-inside : subst-weaken-insideᵗ Instantiation
          i-subst-weaken-inside pos₁ pos₂ inc (subst-α sub-τ)
            = subst-α (subst-weaken-inside pos₁ pos₂ inc sub-τ)
          i-subst-weaken-inside pos₁ pos₂ inc (subst-ρ sub-σ)
            = subst-ρ (subst-weaken-inside pos₁ pos₂ inc sub-σ)

  Instantiations-Substitution⁺ : Substitution⁺ Instantiations
  Instantiations-Substitution⁺ = substitution⁺ unique dec is-weaken-0 is-weaken-weaken is-weaken-subst is-subst-weaken is-subst-subst is-weaken-exchange is-subst-weaken-inside
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

          is-weaken-length : ∀ pos inc is →
                               length (weaken-is pos inc is) ≡ length is
          is-weaken-length pos inc [] = refl
          is-weaken-length pos inc (i ∷ is)
            rewrite is-weaken-length pos inc is = refl

          is-subst-length : ∀ {is₁ is₂ : Instantiations} {i pos} →
                              is₁ ⟦ i / pos ⟧≡ is₂ →
                              length is₁ ≡ length is₂
          is-subst-length [] = refl
          is-subst-length (sub-i ∷ sub-is) = cong suc (is-subst-length sub-is)

          is-weaken-weaken : weaken-weakenᵗ Instantiations
          is-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ [] = refl
          is-weaken-weaken {pos₁} inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (i ∷ is)
            with l+m≤l+n (length is) pos₂≤pos₁+inc₁
          ... | pos≤pos
            rewrite sym (+-assoc (length is) pos₁ inc₁)
            with weaken-weaken inc₁ inc₂ (l+m≤l+n (length is) pos₁≤pos₂) pos≤pos i
          ... | eq₁
            rewrite is-weaken-length pos₁ inc₁ is
              = cong₂ _∷_ eq₁ (is-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ is)

          is-weaken-subst : weaken-substᵗ Instantiations
          is-weaken-subst inc pos₂≤pos₁ [] = []
          is-weaken-subst {pos₁} {pos₂} inc pos₂≤pos₁ {v₁ = i₁ ∷ is₁} {v₂ = i₂ ∷ is₂} (sub-i ∷ sub-is)
            with weaken-subst inc (l+m≤l+n (length is₁) pos₂≤pos₁) sub-i
          ... | sub-i'
            with begin
              length is₁ + pos₂
            ≡⟨ is-subst-length sub-is ∥ (λ v → v + pos₂) ⟩
              length is₂ + pos₂
            ∎ | begin
              (length is₁ + pos₁) + inc
            ≡⟨ +-assoc (length is₁) pos₁ inc ⟩
              length is₁ + (pos₁ + inc)
            ⟨ is-weaken-length pos₂ inc is₁ ∥ (λ v → v + (pos₁ + inc)) ⟩≡
              length (weaken pos₂ inc is₁) + (pos₁ + inc)
            ∎ where open Eq-Reasoning
          ... | eq₁ | eq₂
            rewrite eq₁ | eq₂
            = sub-i' ∷ is-weaken-subst inc pos₂≤pos₁ sub-is

          is-subst-weaken : subst-weakenᵗ Instantiations
          is-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ [] = []
          is-subst-weaken {pos₁} {pos₂} inc pos₁≤pos₂ pos₂≤inc+pos₁ (i ∷ is)
            with begin
              length is + pos₁
            ≤⟨ l+m≤l+n (length is) pos₁≤pos₂ ⟩
              length is + pos₂
            ≡⟨ cong (λ v → v + pos₂) (sym (is-weaken-length pos₁ (suc inc) is)) ⟩
              length (weaken pos₁ (suc inc) is) + pos₂
            ∎ | begin
              length (weaken pos₁ (suc inc) is) + pos₂
            ≡⟨ cong (λ v → v + pos₂) (is-weaken-length pos₁ (suc inc) is) ⟩
              length is + pos₂
            ≤⟨ l+m≤l+n (length is) pos₂≤inc+pos₁ ⟩
              length is + (inc + pos₁)
            ≡⟨ sym (+-assoc (length is) inc pos₁) ⟩
              (length is + inc) + pos₁
            ≡⟨ cong (λ v → v + pos₁) (+-comm (length is) inc) ⟩
              (inc + length is) + pos₁
            ≡⟨ +-assoc inc (length is) pos₁ ⟩
              inc + (length is + pos₁)
            ∎ where open N.≤-Reasoning
          ... | ≤₁ | ≤₂
            = subst-weaken inc ≤₁ ≤₂ i ∷ is-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ is

          is-subst-subst : subst-substᵗ Instantiations
          is-subst-subst sub-i [] [] = [] , [] , []
          is-subst-subst {pos₁} {pos₂} sub-i {v₁ = i₁ ∷ is₁} {i₂ ∷ is₂} {i₁' ∷ is₁'} (sub-i₁ ∷ sub-is₁) (sub-i₁' ∷ sub-is₁')
            with begin
              length is₁ + suc (pos₁ + pos₂)
            ⟨ +-assoc (length is₁) (suc pos₁) pos₂ ⟩≡
              (length is₁ + suc pos₁) + pos₂
            ≡⟨ +-comm (length is₁) (suc pos₁) ∥ (λ v → v + pos₂) ⟩
              (suc pos₁ + length is₁) + pos₂
            ≡⟨ +-comm pos₁ (length is₁) ∥ (λ v → suc v + pos₂) ⟩
              (suc (length is₁ + pos₁)) + pos₂
            ≡⟨ refl ⟩
              suc ((length is₁ + pos₁) + pos₂)
            ∎ | begin
              (length is₁ + pos₁) + pos₂
            ≡⟨ +-assoc (length is₁) pos₁ pos₂ ⟩
              length is₁ + (pos₁ + pos₂)
            ≡⟨ is-subst-length sub-is₁' ∥ (λ v → v + (pos₁ + pos₂))  ⟩
              length is₂ + (pos₁ + pos₂)
            ∎ | begin
              length is₁ + pos₁
            ≡⟨ is-subst-length sub-is₁ ∥ (λ v → v + pos₁) ⟩
              length is₁' + pos₁
            ∎ where open Eq-Reasoning
          ... | eq₁ | eq₂ | eq₃
            rewrite eq₁
            with subst-subst sub-i sub-i₁ sub-i₁'
          ... | i₂' , sub-i₂ , sub-i₂'
            with is-subst-subst sub-i sub-is₁ sub-is₁'
          ... | is₂' , sub-is₂ , sub-is₂'
            rewrite eq₂ | eq₃
            = i₂' ∷ is₂' , sub-i₂ ∷ sub-is₂ , sub-i₂' ∷ sub-is₂'

          is-weaken-exchange : weaken-exchangeᵗ Instantiations
          is-weaken-exchange inc₁ inc₂ pos₂≤pos₁ [] = refl
          is-weaken-exchange {pos₁} {pos₂} inc₁ inc₂ pos₂≤pos₁ (i ∷ is)
            with weaken-exchange {pos₁ = length is + pos₁} {length is + pos₂} inc₁ inc₂ (l+m≤l+n (length is) pos₂≤pos₁) i
          ... | eq₁
            with begin
              length is + pos₂
            ⟨ is-weaken-length pos₁ inc₁ is ∥ (λ v → v + pos₂) ⟩≡
              length (weaken-is pos₁ inc₁ is) + pos₂
            ∎ | begin
              inc₂ + (length is + pos₁)
            ⟨ +-assoc inc₂ (length is) pos₁ ⟩≡
              (inc₂ + length is) + pos₁
            ≡⟨ +-comm inc₂ (length is) ∥ (λ v → v + pos₁) ⟩
              (length is + inc₂) + pos₁
            ≡⟨ +-assoc (length is) inc₂ pos₁ ⟩
              length is + (inc₂ + pos₁)
            ⟨ is-weaken-length pos₂ inc₂ is ∥ (λ v → v + (inc₂ + pos₁)) ⟩≡
              length (weaken pos₂ inc₂ is) + (inc₂ + pos₁)
            ∎ where open Eq-Reasoning
          ... | eq₂ | eq₃
            rewrite eq₂ | eq₃
            = cong₂ _∷_ eq₁
                        (is-weaken-exchange inc₁ inc₂ pos₂≤pos₁ is)

          is-subst-weaken-inside : subst-weaken-insideᵗ Instantiations
          is-subst-weaken-inside pos₁ pos₂ inc [] = []
          is-subst-weaken-inside pos₁ pos₂ inc {v₁ = i₁ ∷ is₁} {i₂ ∷ is₂} (sub-i ∷ sub-is)
            with subst-weaken-inside {{Instantiation-Substitution⁺}} (length is₁ + pos₁) pos₂ inc sub-i
          ... | sub-i'
            with is-subst-weaken-inside pos₁ pos₂ inc sub-is
          ... | sub-is'
            with begin
              suc ((length is₁ + pos₁) + pos₂)
            ≡⟨ +-comm 1 (length is₁) ∥ (λ v → (v + pos₁) + pos₂) ⟩
              ((length is₁ + 1) + pos₁) + pos₂
            ≡⟨ +-assoc (length is₁) 1 pos₁ ∥ (λ v → v + pos₂) ⟩
              (length is₁ + suc pos₁) + pos₂
            ≡⟨ +-assoc (length is₁) (suc pos₁) pos₂ ⟩
              length is₁ + suc (pos₁ + pos₂)
            ∎ | begin
              length is₁ + pos₁
            ⟨ is-weaken-length (suc (pos₁ + pos₂)) inc is₁ ∥ (λ v → v + pos₁) ⟩≡
              length (weaken-is (suc (pos₁ + pos₂)) inc is₁) + pos₁
            ∎ | begin
              (length is₁ + pos₁) + pos₂
            ≡⟨ +-assoc (length is₁) pos₁ pos₂ ⟩
              length is₁ + (pos₁ + pos₂)
            ≡⟨ is-subst-length sub-is ∥ (λ v → v + (pos₁ + pos₂)) ⟩
              length is₂ + (pos₁ + pos₂)
            ∎ where open Eq-Reasoning
          ... | eq₁ | eq₂ | eq₃
            rewrite eq₁ | eq₂ | eq₃
            = sub-i' ∷ sub-is'

  SmallValue-Substitution⁺ : Substitution⁺ SmallValue
  SmallValue-Substitution⁺ = substitution⁺ unique dec v-weaken-0 v-weaken-weaken v-weaken-subst v-subst-weaken v-subst-subst v-weaken-exchange v-subst-weaken-inside
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
            rewrite v-weaken-0 pos v
                  | weaken-0 (length Δ + pos) is = refl

          v-weaken-weaken : weaken-weakenᵗ SmallValue
          v-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (reg ♯r) = refl
          v-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (globval l) = refl
          v-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (int i) = refl
          v-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ ns = refl
          v-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (uninit τ)
            rewrite weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ τ = refl
          v-weaken-weaken {pos₁} inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (Λ Δ ∙ v ⟦ is ⟧)
            with l+m≤l+n (length Δ) pos₂≤pos₁+inc₁
          ... | pos≤pos
            rewrite sym (+-assoc (length Δ) pos₁ inc₁)
                  | v-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ v
                  | weaken-weaken inc₁ inc₂ (l+m≤l+n (length Δ) pos₁≤pos₂) pos≤pos is
            = refl

          v-weaken-subst : weaken-substᵗ SmallValue
          v-weaken-subst inc pos₂≤pos₁ subst-reg = subst-reg
          v-weaken-subst inc pos₂≤pos₁ subst-globval = subst-globval
          v-weaken-subst inc pos₂≤pos₁ subst-int = subst-int
          v-weaken-subst inc pos₂≤pos₁ subst-ns = subst-ns
          v-weaken-subst inc pos₂≤pos₁ (subst-uninit sub-τ) = subst-uninit (weaken-subst inc pos₂≤pos₁ sub-τ)
          v-weaken-subst {pos₁} inc pos₂≤pos₁ {v₁ = Λ Δ ∙ v ⟦ is ⟧} (subst-Λ sub-v sub-is)
            with weaken-subst inc (l+m≤l+n (length Δ) pos₂≤pos₁) sub-is
          ... | sub-is'
            rewrite +-assoc (length Δ) pos₁ inc
            = subst-Λ (v-weaken-subst inc pos₂≤pos₁ sub-v) sub-is'

          v-subst-weaken : subst-weakenᵗ SmallValue
          v-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ (reg ♯r) = subst-reg
          v-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ (globval l) = subst-globval
          v-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ (int i) = subst-int
          v-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ ns = subst-ns
          v-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ (uninit τ)
            = subst-uninit (subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ τ)
          v-subst-weaken {pos₁} {pos₂} inc pos₁≤pos₂ pos₂≤inc+pos₁ (Λ Δ ∙ v ⟦ is ⟧)
            with begin
              length Δ + pos₂
            ≤⟨ l+m≤l+n (length Δ) pos₂≤inc+pos₁ ⟩
              length Δ + (inc + pos₁)
            ≡⟨ sym (+-assoc (length Δ) inc pos₁) ⟩
              (length Δ + inc) + pos₁
            ≡⟨ cong (λ v → v + pos₁) (+-comm (length Δ) inc) ⟩
              (inc + length Δ) + pos₁
            ≡⟨ +-assoc inc (length Δ) pos₁ ⟩
              inc + (length Δ + pos₁)
            ∎ where open N.≤-Reasoning
          ... | pos-≤
            = subst-Λ (v-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ v)
                      (subst-weaken inc (l+m≤l+n (length Δ) pos₁≤pos₂) pos-≤ is)

          v-subst-subst : subst-substᵗ SmallValue
          v-subst-subst sub-i subst-reg subst-reg = _ , subst-reg , subst-reg
          v-subst-subst sub-i subst-globval subst-globval = _ , subst-globval , subst-globval
          v-subst-subst sub-i subst-int subst-int = _ , subst-int , subst-int
          v-subst-subst sub-i subst-ns subst-ns = _ , subst-ns , subst-ns
          v-subst-subst sub-i (subst-uninit sub-τ₁) (subst-uninit sub-τ₁')
            with subst-subst sub-i sub-τ₁ sub-τ₁'
          ... | τ₂ , sub-τ₂ , sub-τ₂'
            = _ , subst-uninit sub-τ₂ , subst-uninit sub-τ₂'
          v-subst-subst {pos₁} {pos₂} sub-i {Λ Δ ∙ v ⟦ is ⟧} (subst-Λ sub-v₁ sub-is₁) (subst-Λ sub-v₁' sub-is₁')
            with v-subst-subst sub-i  sub-v₁ sub-v₁'
          ... | v₂ , sub-v₂ , sub-v₂'
            with begin
              length Δ + suc (pos₁ + pos₂)
            ⟨ +-assoc (length Δ) 1 (pos₁ + pos₂) ⟩≡
              (length Δ + 1) + (pos₁ + pos₂)
            ≡⟨ +-comm (length Δ) 1 ∥ (λ v → v + (pos₁ + pos₂)) ⟩
              suc (length Δ) + (pos₁ + pos₂)
            ⟨ cong suc (+-assoc (length Δ) pos₁ pos₂) ⟩≡
              suc (length Δ + pos₁ + pos₂)
            ∎ where open Eq-Reasoning
          ... | eq
            rewrite eq
            with subst-subst {{Instantiations-Substitution⁺}} {length Δ + pos₁} {pos₂} sub-i sub-is₁ sub-is₁'
          ... | is₂ , sub-is₂ , sub-is₂'
            rewrite +-assoc (length Δ) pos₁ pos₂
            = _ , subst-Λ sub-v₂ sub-is₂ , subst-Λ sub-v₂' sub-is₂'

          v-weaken-exchange : weaken-exchangeᵗ SmallValue
          v-weaken-exchange inc₁ inc₂ pos₂≤pos₁ (reg ♯r) = refl
          v-weaken-exchange inc₁ inc₂ pos₂≤pos₁ (globval l) = refl
          v-weaken-exchange inc₁ inc₂ pos₂≤pos₁ (int i) = refl
          v-weaken-exchange inc₁ inc₂ pos₂≤pos₁ ns = refl
          v-weaken-exchange inc₁ inc₂ pos₂≤pos₁ (uninit τ)
            = cong uninit (weaken-exchange inc₁ inc₂ pos₂≤pos₁ τ)
          v-weaken-exchange {pos₁} inc₁ inc₂ pos₂≤pos₁ (Λ Δ ∙ v ⟦ is ⟧)
            rewrite v-weaken-exchange inc₁ inc₂ pos₂≤pos₁ v
            with weaken-exchange inc₁ inc₂ (l+m≤l+n (length Δ) pos₂≤pos₁) is
          ... | eq₁
            with begin
              inc₂ + (length Δ + pos₁)
            ⟨ +-assoc inc₂ (length Δ) pos₁ ⟩≡
              (inc₂ + length Δ) + pos₁
            ≡⟨ +-comm inc₂ (length Δ) ∥ (λ v → v + pos₁) ⟩
              (length Δ + inc₂) + pos₁
            ≡⟨ +-assoc (length Δ) inc₂ pos₁ ⟩
              length Δ + (inc₂ + pos₁)
            ∎ where open Eq-Reasoning
          ... | eq₂
            rewrite eq₂ | eq₁ = refl

          v-subst-weaken-inside : subst-weaken-insideᵗ SmallValue
          v-subst-weaken-inside pos₁ pos₂ inc subst-reg = subst-reg
          v-subst-weaken-inside pos₁ pos₂ inc subst-globval = subst-globval
          v-subst-weaken-inside pos₁ pos₂ inc subst-int = subst-int
          v-subst-weaken-inside pos₁ pos₂ inc subst-ns = subst-ns
          v-subst-weaken-inside pos₁ pos₂ inc (subst-uninit sub-τs)
            = subst-uninit (subst-weaken-inside pos₁ pos₂ inc sub-τs)
          v-subst-weaken-inside pos₁ pos₂ inc {v₁ = Λ Δ ∙ v ⟦ is ⟧} (subst-Λ sub-v sub-is)
            with subst-weaken-inside (length Δ + pos₁) pos₂ inc sub-is
          ... | sub-is'
            with begin
              suc (length Δ + (pos₁ + pos₂))
            ≡⟨ +-comm 1 (length Δ) ∥ (λ v → v + (pos₁ + pos₂)) ⟩
              (length Δ + 1) + (pos₁ + pos₂)
            ≡⟨ +-assoc (length Δ) 1 (pos₁ + pos₂) ⟩
              length Δ + suc (pos₁ + pos₂)
            ∎ where open Eq-Reasoning
          ... | eq
            rewrite +-assoc (length Δ) pos₁ pos₂ | eq
            = subst-Λ (v-subst-weaken-inside pos₁ pos₂ inc sub-v) sub-is'

  Instruction-Substitution⁺ : Substitution⁺ Instruction
  Instruction-Substitution⁺ = substitution⁺ unique dec ι-weaken-0 ι-weaken-weaken ι-weaken-subst ι-subst-weaken ι-subst-subst ι-weaken-exchange ι-subst-weaken-inside
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

          ι-weaken-weaken : weaken-weakenᵗ Instruction
          ι-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (add ♯rd ♯rs v)
            rewrite weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ v = refl
          ι-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (sub ♯rd ♯rs v)
            rewrite weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ v = refl
          ι-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (salloc i) = refl
          ι-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (sfree i) = refl
          ι-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (sld ♯rd i) = refl
          ι-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (sst i ♯rs) = refl
          ι-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (ld ♯rd ♯rs i) = refl
          ι-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (st ♯rd i ♯rs) = refl
          ι-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (malloc ♯rd τs)
            rewrite weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ τs = refl
          ι-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (mov ♯rd v)
            rewrite weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁  v = refl
          ι-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (beq ♯r v)
            rewrite weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ v = refl

          ι-weaken-subst : weaken-substᵗ Instruction
          ι-weaken-subst inc pos₂≤pos₁ (subst-add sub-v) = subst-add (weaken-subst inc pos₂≤pos₁ sub-v)
          ι-weaken-subst inc pos₂≤pos₁ (subst-sub sub-v) = subst-sub (weaken-subst inc pos₂≤pos₁ sub-v)
          ι-weaken-subst inc pos₂≤pos₁ subst-salloc = subst-salloc
          ι-weaken-subst inc pos₂≤pos₁ subst-sfree = subst-sfree
          ι-weaken-subst inc pos₂≤pos₁ subst-sld = subst-sld
          ι-weaken-subst inc pos₂≤pos₁ subst-sst = subst-sst
          ι-weaken-subst inc pos₂≤pos₁ subst-ld = subst-ld
          ι-weaken-subst inc pos₂≤pos₁ subst-st = subst-st
          ι-weaken-subst inc pos₂≤pos₁ (subst-malloc sub-τs) = subst-malloc (weaken-subst inc pos₂≤pos₁ sub-τs)
          ι-weaken-subst inc pos₂≤pos₁ (subst-mov sub-v) = subst-mov (weaken-subst inc pos₂≤pos₁ sub-v)
          ι-weaken-subst inc pos₂≤pos₁ (subst-beq sub-v) = subst-beq (weaken-subst inc pos₂≤pos₁ sub-v)

          ι-subst-weaken : subst-weakenᵗ Instruction
          ι-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ (add ♯rd ♯rs v) = subst-add (subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ v)
          ι-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ (sub ♯rd ♯rs v) = subst-sub (subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ v)
          ι-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ (salloc i) = subst-salloc
          ι-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ (sfree i) = subst-sfree
          ι-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ (sld ♯rd i) = subst-sld
          ι-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ (sst i ♯rs) = subst-sst
          ι-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ (ld ♯rd ♯rs i) = subst-ld
          ι-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ (st ♯rd i ♯rs) = subst-st
          ι-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ (malloc ♯rd τs) = subst-malloc (subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ τs)
          ι-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ (mov ♯rd v) = subst-mov (subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ v)
          ι-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ (beq ♯r v) = subst-beq (subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ v)

          ι-subst-subst : subst-substᵗ Instruction
          ι-subst-subst sub-i (subst-add sub-v₁) (subst-add sub-v₁')
            with subst-subst sub-i sub-v₁ sub-v₁'
          ... | v₂ , sub-v₂ , sub-v₂'
            = _ , subst-add sub-v₂ , subst-add sub-v₂'
          ι-subst-subst sub-i (subst-sub sub-v₁) (subst-sub sub-v₁')
            with subst-subst sub-i sub-v₁ sub-v₁'
          ... | v₂ , sub-v₂ , sub-v₂'
            = _ , subst-sub sub-v₂ , subst-sub sub-v₂'
          ι-subst-subst sub-i subst-salloc subst-salloc = _ , subst-salloc , subst-salloc
          ι-subst-subst sub-i subst-sfree subst-sfree = _ , subst-sfree , subst-sfree
          ι-subst-subst sub-i subst-sld subst-sld = _ , subst-sld , subst-sld
          ι-subst-subst sub-i subst-sst subst-sst = _ , subst-sst , subst-sst
          ι-subst-subst sub-i subst-ld subst-ld = _ , subst-ld , subst-ld
          ι-subst-subst sub-i subst-st subst-st = _ , subst-st , subst-st
          ι-subst-subst sub-i (subst-malloc sub-τs₁) (subst-malloc sub-τs₁')
            with subst-subst sub-i sub-τs₁ sub-τs₁'
          ... | τs₂ , sub-τs₂ , sub-τs₂'
            = _ , subst-malloc sub-τs₂ , subst-malloc sub-τs₂'
          ι-subst-subst sub-i (subst-mov sub-v₁) (subst-mov sub-v₁')
            with subst-subst sub-i sub-v₁ sub-v₁'
          ... | v₂ , sub-v₂ , sub-v₂'
            = _ , subst-mov sub-v₂ , subst-mov sub-v₂'
          ι-subst-subst sub-i (subst-beq sub-v₁) (subst-beq sub-v₁')
            with subst-subst sub-i sub-v₁ sub-v₁'
          ... | v₂ , sub-v₂ , sub-v₂'
            = _ , subst-beq sub-v₂ , subst-beq sub-v₂'

          ι-weaken-exchange : weaken-exchangeᵗ Instruction
          ι-weaken-exchange inc₁ inc₂ pos₂≤pos₁ (add ♯rd ♯rs v)
            rewrite weaken-exchange inc₁ inc₂ pos₂≤pos₁ v = refl
          ι-weaken-exchange inc₁ inc₂ pos₂≤pos₁ (sub ♯rd ♯rs v)
            rewrite weaken-exchange inc₁ inc₂ pos₂≤pos₁ v = refl
          ι-weaken-exchange inc₁ inc₂ pos₂≤pos₁ (salloc i) = refl
          ι-weaken-exchange inc₁ inc₂ pos₂≤pos₁ (sfree i) = refl
          ι-weaken-exchange inc₁ inc₂ pos₂≤pos₁ (sld ♯rd i) = refl
          ι-weaken-exchange inc₁ inc₂ pos₂≤pos₁ (sst i ♯rs) = refl
          ι-weaken-exchange inc₁ inc₂ pos₂≤pos₁ (ld ♯rd ♯rs i) = refl
          ι-weaken-exchange inc₁ inc₂ pos₂≤pos₁ (st ♯rd i ♯rs) = refl
          ι-weaken-exchange inc₁ inc₂ pos₂≤pos₁ (malloc ♯rd τs)
            rewrite weaken-exchange inc₁ inc₂ pos₂≤pos₁ τs = refl
          ι-weaken-exchange inc₁ inc₂ pos₂≤pos₁ (mov ♯rd v)
            rewrite weaken-exchange inc₁ inc₂ pos₂≤pos₁ v = refl
          ι-weaken-exchange inc₁ inc₂ pos₂≤pos₁ (beq ♯r v)
            rewrite weaken-exchange inc₁ inc₂ pos₂≤pos₁ v = refl

          ι-subst-weaken-inside : subst-weaken-insideᵗ Instruction
          ι-subst-weaken-inside pos₁ pos₂ inc (subst-add sub-v)
            = subst-add (subst-weaken-inside pos₁ pos₂ inc sub-v)
          ι-subst-weaken-inside pos₁ pos₂ inc (subst-sub sub-v)
            = subst-sub (subst-weaken-inside pos₁ pos₂ inc sub-v)
          ι-subst-weaken-inside pos₁ pos₂ inc subst-salloc = subst-salloc
          ι-subst-weaken-inside pos₁ pos₂ inc subst-sfree = subst-sfree
          ι-subst-weaken-inside pos₁ pos₂ inc subst-sld = subst-sld
          ι-subst-weaken-inside pos₁ pos₂ inc subst-sst = subst-sst
          ι-subst-weaken-inside pos₁ pos₂ inc subst-ld = subst-ld
          ι-subst-weaken-inside pos₁ pos₂ inc subst-st = subst-st
          ι-subst-weaken-inside pos₁ pos₂ inc (subst-malloc sub-τs)
            = subst-malloc (subst-weaken-inside pos₁ pos₂ inc sub-τs)
          ι-subst-weaken-inside pos₁ pos₂ inc (subst-mov sub-v)
            = subst-mov (subst-weaken-inside pos₁ pos₂ inc sub-v)
          ι-subst-weaken-inside pos₁ pos₂ inc (subst-beq sub-v)
            = subst-beq (subst-weaken-inside pos₁ pos₂ inc sub-v)

  InstructionSequence-Substitution⁺ : Substitution⁺ InstructionSequence
  InstructionSequence-Substitution⁺ = substitution⁺ unique dec I-weaken-0 I-weaken-weaken I-weaken-subst I-subst-weaken I-subst-subst I-weaken-exchange I-subst-weaken-inside
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

          I-weaken-weaken : weaken-weakenᵗ InstructionSequence
          I-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (ι ~> I)
            rewrite weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ ι
                  | I-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ I = refl
          I-weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ (jmp v)
            rewrite weaken-weaken inc₁ inc₂ pos₁≤pos₂ pos₂≤pos₁+inc₁ v = refl

          I-weaken-subst : weaken-substᵗ InstructionSequence
          I-weaken-subst inc pos₂≤pos₁ (subst-~> sub-v sub-I) = subst-~> (weaken-subst inc pos₂≤pos₁ sub-v) (I-weaken-subst inc pos₂≤pos₁ sub-I)
          I-weaken-subst inc pos₂≤pos₁ (subst-jmp sub-v) = subst-jmp (weaken-subst inc pos₂≤pos₁ sub-v)

          I-subst-weaken : subst-weakenᵗ InstructionSequence
          I-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ (ι ~> I)
            = subst-~> (subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ ι) (I-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ I)
          I-subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ (jmp v)
            = subst-jmp (subst-weaken inc pos₁≤pos₂ pos₂≤inc+pos₁ v)

          I-subst-subst : subst-substᵗ InstructionSequence
          I-subst-subst sub-i (subst-~> sub-ι₁ sub-I₁) (subst-~> sub-ι₁' sub-I₁')
            with subst-subst sub-i sub-ι₁ sub-ι₁'
          ... | ι₂ , sub-ι₂ , sub-ι₂'
            with I-subst-subst sub-i sub-I₁ sub-I₁'
          ... | I₂ , sub-I₂ , sub-I₂'
            = _ , subst-~> sub-ι₂ sub-I₂ , subst-~> sub-ι₂' sub-I₂'
          I-subst-subst sub-i (subst-jmp sub-v₁) (subst-jmp sub-v₁')
            with subst-subst sub-i sub-v₁ sub-v₁'
          ... | v₂ , sub-v₂ , sub-v₂'
            = _ , subst-jmp sub-v₂ , subst-jmp sub-v₂'

          I-weaken-exchange : weaken-exchangeᵗ InstructionSequence
          I-weaken-exchange inc₁ inc₂ pos₂≤pos₁ (ι ~> I)
            rewrite weaken-exchange inc₁ inc₂ pos₂≤pos₁ ι
                  | I-weaken-exchange inc₁ inc₂ pos₂≤pos₁ I = refl
          I-weaken-exchange inc₁ inc₂ pos₂≤pos₁ (jmp v)
            rewrite weaken-exchange inc₁ inc₂ pos₂≤pos₁ v = refl

          I-subst-weaken-inside : subst-weaken-insideᵗ InstructionSequence
          I-subst-weaken-inside pos₁ pos₂ inc (subst-~> sub-ι sub-I)
            = subst-~> (subst-weaken-inside pos₁ pos₂ inc sub-ι)
                       (I-subst-weaken-inside pos₁ pos₂ inc sub-I)
          I-subst-weaken-inside pos₁ pos₂ inc (subst-jmp sub-v)
            = subst-jmp (subst-weaken-inside pos₁ pos₂ inc sub-v)
