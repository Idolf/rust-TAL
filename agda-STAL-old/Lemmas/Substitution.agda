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
  infix 3 _⟦_⟧?
  field
    subst-unique : ∀ {v v₁ v₂ : A} {c} →
                     v ⟦ c ⟧≡ v₁ →
                     v ⟦ c ⟧≡ v₂ →
                     v₁ ≡ v₂
    can-weaken : ∀ (v : A) w ι → ∃ λ v' → v ⟦ weaken w / ι ⟧≡ v'
    _⟦_⟧? : ∀ (v : A) c → Dec (∃ λ v' → v ⟦ c ⟧≡ v')
    weaken-0 : ∀ (v : A) {ι} → v ⟦ weaken 0 / ι ⟧≡ v

  weaken-0-unique : ∀ {v₁ v₂ ι} → v₁ ⟦ weaken 0 / ι ⟧≡ v₂ →
                                  v₁ ≡ v₂
  weaken-0-unique {v₁} = subst-unique (weaken-0 v₁)
open Substitution⁺ {{...}} public

private
  subst-n-≢-inst : ∀ {i ι₁ ι₂} → ¬ (ι₁ ⟦ inst i / ι₁ ⟧n≡ ι₂)
  subst-n-≢-inst (subst-< ι₁<ι₁) = NP.1+n≰n ι₁<ι₁
  subst-n-≢-inst (subst-inst-> ι₁>ι₁) = NP.1+n≰n ι₁>ι₁

  mutual
    substᵗ-unique : ∀ A {{S : Substitution A}} → Set
    substᵗ-unique A = ∀ {v v₁ v₂ : A} {c : WeakCast} →
                        v ⟦ c ⟧≡ v₁ →
                        v ⟦ c ⟧≡ v₂ →
                        v₁ ≡ v₂

    subst-n-unique : substᵗ-unique ℕ
    subst-n-unique (subst-< n<ι) (subst-< n<ι') = refl
    subst-n-unique (subst-< n<ι) (subst-inst-> n>ι)
      with NP.1+n≰n (NP.<-trans n<ι n>ι)
    ... | ()
    subst-n-unique (subst-< n<ι) (subst-weaken-≥ n≥ι)
      with NP.1+n≰n (Nat-≤-trans n<ι n≥ι)
    ... | ()
    subst-n-unique (subst-inst-> n>ι) (subst-< n<ι)
      with NP.1+n≰n (NP.<-trans n<ι n>ι)
    ... | ()
    subst-n-unique (subst-inst-> n>ι) (subst-inst-> n>ι') = refl
    subst-n-unique (subst-weaken-≥ n≥ι) (subst-< n<ι)
      with NP.1+n≰n (Nat-≤-trans n<ι n≥ι)
    ... | ()
    subst-n-unique (subst-weaken-≥ n≥ι) (subst-weaken-≥ n≥ι') = refl

    subst-τ-unique : substᵗ-unique Type
    subst-τ-unique (subst-α-¬inst sub-n₁) (subst-α-¬inst sub-n₂)
      = cong α⁼ (subst-n-unique sub-n₁ sub-n₂)
    subst-τ-unique (subst-α-¬inst sub-n₁) (subst-α-inst sub-τ₂)
      with subst-n-≢-inst sub-n₁
    ... | ()
    subst-τ-unique (subst-α-inst sub-τ₁) (subst-α-¬inst sub-n₂)
      with subst-n-≢-inst sub-n₂
    ... | ()
    subst-τ-unique (subst-α-inst sub-τ₁) (subst-α-inst sub-τ₂) =
      subst-τ-unique sub-τ₁ sub-τ₂
    subst-τ-unique subst-int subst-int = refl
    subst-τ-unique subst-ns subst-ns = refl
    subst-τ-unique (subst-∀ {Δ = Δ} sub-Δ₁ sub-Γ₁) (subst-∀ sub-Δ₂ sub-Γ₂) =
      cong₂ ∀[_]_ (subst-Δ-unique sub-Δ₁ sub-Δ₂)
                  (subst-Γ-unique sub-Γ₁ sub-Γ₂)
    subst-τ-unique (subst-tuple sub-τs₁) (subst-tuple sub-τs₂) =
      cong tuple (subst-τs⁻-unique sub-τs₁ sub-τs₂)

    subst-τ⁻-unique : substᵗ-unique InitType
    subst-τ⁻-unique (subst-τ⁻ {φ = φ} sub-τ₁) (subst-τ⁻ sub-τ₂) =
      cong₂ _,_ (subst-τ-unique sub-τ₁ sub-τ₂) refl

    subst-τs⁻-unique : substᵗ-unique (List InitType)
    subst-τs⁻-unique [] [] = refl
    subst-τs⁻-unique (sub-τ⁻₁ ∷ sub-τs⁻₁) (sub-τ⁻₂ ∷ sub-τs⁻₂) =
        cong₂ _∷_ (subst-τ⁻-unique sub-τ⁻₁ sub-τ⁻₂)
                  (subst-τs⁻-unique sub-τs⁻₁ sub-τs⁻₂)

    subst-σ-unique : substᵗ-unique StackType
    subst-σ-unique (subst-ρ-¬inst sub-n₁) (subst-ρ-¬inst sub-n₂)
      = cong ρ⁼ (subst-n-unique sub-n₁ sub-n₂)
    subst-σ-unique (subst-ρ-¬inst sub-n₁) (subst-ρ-inst sub-σ₂)
      with subst-n-≢-inst sub-n₁
    ... | ()
    subst-σ-unique (subst-ρ-inst sub-σ₁) (subst-ρ-¬inst sub-n₂)
      with subst-n-≢-inst sub-n₂
    ... | ()
    subst-σ-unique (subst-ρ-inst sub-σ₁) (subst-ρ-inst sub-σ₂) =
      subst-σ-unique sub-σ₁ sub-σ₂
    subst-σ-unique subst-[] subst-[] = refl
    subst-σ-unique (sub-τ₁ ∷ sub-σ₁) (sub-τ₂ ∷ sub-σ₂) =
      cong₂ _∷_ (subst-τ-unique sub-τ₁ sub-τ₂) (subst-σ-unique sub-σ₁ sub-σ₂)

    subst-Γ-unique : substᵗ-unique RegisterAssignment
    subst-Γ-unique (subst-registerₐ sub-sp₁ sub-regs₁)
                   (subst-registerₐ sub-sp₂ sub-regs₂) =
      cong₂ registerₐ (subst-σ-unique sub-sp₁ sub-sp₂)
                      (subst-regs-unique sub-regs₁ sub-regs₂)

    subst-regs-unique : ∀ {m} → substᵗ-unique (Vec Type m)
    subst-regs-unique {v = []} {[]} {[]} [] [] = refl
    subst-regs-unique {v = τ ∷ τs} {τ₁ ∷ τs₁} {τ₂ ∷ τs₂}
      (sub-τ₁ ∷ sub-τs₁) (sub-τ₂ ∷ sub-τs₂) =
        cong₂ _∷_ (subst-τ-unique sub-τ₁ sub-τ₂)
                  (subst-regs-unique sub-τs₁ sub-τs₂)

    subst-Δ-unique : substᵗ-unique TypeAssignment
    subst-Δ-unique [] [] = refl
    subst-Δ-unique (sub-a₁ ∷ sub-Δ₁) (sub-a₂ ∷ sub-Δ₂) =
      cong₂ _∷_ (subst-a-unique sub-a₁ sub-a₂)
                (subst-Δ-unique sub-Δ₁ sub-Δ₂)

    subst-a-unique : substᵗ-unique TypeAssignmentValue
    subst-a-unique subst-α subst-α = refl
    subst-a-unique subst-ρ subst-ρ = refl

  mutual
    can-weaken-n : ∀ n n⁺ ι → ∃ λ n' → n ⟦ weaken n⁺ / ι ⟧n≡ n'
    can-weaken-n n n⁺ ι with ι ≤? n
    ... | yes n≥ι = n⁺ + n , subst-weaken-≥ n≥ι
    ... | no n≱ι = n , subst-< (NP.≰⇒> n≱ι)

    can-weaken-τ : ∀ τ n ι → ∃ λ τ' → τ ⟦ weaken n / ι ⟧τ≡ τ'
    can-weaken-τ (α⁼ ι₁) n ι₂ = Σ-map α⁼ subst-α-¬inst (can-weaken-n ι₁ n ι₂)
    can-weaken-τ int n ι = int , subst-int
    can-weaken-τ ns n ι = ns , subst-ns
    can-weaken-τ (∀[ Δ ] Γ) n ι
      = Σ-zip ∀[_]_ subst-∀
        (can-weaken-Δ Δ n ι) (can-weaken-Γ Γ n (length Δ + ι))
    can-weaken-τ (tuple τs) n ι
      = Σ-map tuple subst-tuple (can-weaken-τs⁻ τs n ι)

    can-weaken-τ⁻ : ∀ τ⁻ n ι → ∃ λ τ⁻' → τ⁻ ⟦ weaken n / ι ⟧τ⁻≡ τ⁻'
    can-weaken-τ⁻ (τ , φ) n ι
      = Σ-map (λ τ → τ , φ) subst-τ⁻ (can-weaken-τ τ n ι)

    can-weaken-τs⁻ : ∀ τs⁻ n ι → ∃ λ τs⁻' → τs⁻ ⟦ weaken n / ι ⟧τs⁻≡ τs⁻'
    can-weaken-τs⁻ [] n ι = [] , []
    can-weaken-τs⁻ (τ⁻ ∷ τs⁻) n ι
      = Σ-zip _∷_ _∷_ (can-weaken-τ⁻ τ⁻ n ι) (can-weaken-τs⁻ τs⁻ n ι)

    can-weaken-σ : ∀ σ n ι → ∃ λ σ' → σ ⟦ weaken n / ι ⟧σ≡ σ'
    can-weaken-σ (ρ⁼ ι₁) n ι₂ = Σ-map ρ⁼ subst-ρ-¬inst (can-weaken-n ι₁ n ι₂)
    can-weaken-σ [] n ι = [] , subst-[]
    can-weaken-σ (τ ∷ σ) n ι
      = Σ-zip _∷_ _∷_ (can-weaken-τ τ n ι) (can-weaken-σ σ n ι)

    can-weaken-Γ : ∀ Γ n ι → ∃ λ Γ' → Γ ⟦ weaken n / ι ⟧Γ≡ Γ'
    can-weaken-Γ (registerₐ sp regs) n ι
      = Σ-zip registerₐ subst-registerₐ
        (can-weaken-σ sp n ι) (can-weaken-regs regs n ι)

    can-weaken-regs : ∀ {m} (regs : Vec Type m) n ι →
                        ∃ λ regs' → regs ⟦ weaken n / ι ⟧regs≡ regs'
    can-weaken-regs [] n ι = [] , []
    can-weaken-regs (τ ∷ τs) n ι
      = Σ-zip _∷_ _∷_ (can-weaken-τ τ n ι) (can-weaken-regs τs n ι)

    can-weaken-Δ : ∀ Δ n ι → ∃ λ Δ' → Δ ⟦ weaken n / ι ⟧Δ≡ Δ'
    can-weaken-Δ [] n ι = [] , []
    can-weaken-Δ (a ∷ Δ) n ι
      = Σ-zip _∷_ _∷_ (can-weaken-a a n (length Δ + ι))
                      (can-weaken-Δ Δ n ι)

    can-weaken-a : ∀ a n ι → ∃ λ a' → a ⟦ weaken n / ι ⟧a≡ a'
    can-weaken-a α n ι = α , subst-α
    can-weaken-a ρ n ι = ρ , subst-ρ

  mutual
    _⟦_⟧n? : ∀ n c → Dec (∃ λ n' → n ⟦ c ⟧n≡ n')
    n ⟦ inst i / ι ⟧n? with Nat-cmp n ι
    n ⟦ inst i / ι ⟧n? | tri< n<ι _ _ = yes (n , subst-< n<ι)
    0 ⟦ inst i / .0 ⟧n? | tri≈ 0≮0 refl 0≯0 =
      no (λ { (.0 , subst-< ()) })
    suc n ⟦ inst i / ι ⟧n? | tri≈ sucn≮ι _ sucn≯ι =
      no (λ { (._ , subst-< sucn<ι) → sucn≮ι sucn<ι
            ; (._ , subst-inst-> sucn>ι) → sucn≯ι sucn>ι })
    suc n ⟦ inst i / ι ⟧n? | tri> ¬a ¬b (s≤s n≥ι) =
      yes (n , subst-inst-> (s≤s n≥ι))
    n ⟦ weaken n⁺ / ι ⟧n? with ι ≤? n
    ... | yes n≥ι = yes (n⁺ + n , subst-weaken-≥ n≥ι)
    ... | no n≱ι = yes (n , subst-< (NP.≰⇒> n≱ι))

    _⟦_⟧τ? : ∀ τ c → Dec (∃ λ τ' → τ ⟦ c ⟧τ≡ τ')
    α⁼ ι₁ ⟦ weaken n / ι₂ ⟧τ? = yes (can-weaken-τ (α⁼ ι₁) n ι₂)
    α⁼ ι₁ ⟦ inst i / ι₂ ⟧τ? with ι₁ ⟦ inst i / ι₂ ⟧n? | ι₁ ≟ ι₂
    α⁼ ι₁ ⟦ inst i / ι₂ ⟧τ? | yes (n' , sub-n) | _ =
      yes (α⁼ n' , subst-α-¬inst sub-n)
    α⁼ ι ⟦ inst (α τ) / .ι ⟧τ? | no ¬sub-n | yes refl
      = yes (Σ-map id subst-α-inst (can-weaken-τ τ ι 0))
    α⁼ ι ⟦ inst (ρ σ) / .ι ⟧τ? | no ¬sub-n | yes refl
      = no (λ { (._ , subst-α-¬inst sub-n) → ¬sub-n (_ , sub-n) })
    α⁼ ι₁ ⟦ inst i / ι₂ ⟧τ? | no ¬sub-n | no ι₁≢ι₂
      = no (help ι₁≢ι₂ ¬sub-n)
      where help : ∀ {ι₁ ι₂ i} → ι₁ ≢ ι₂ →
                     ¬ (∃ λ ι₁' → ι₁    ⟦ inst i / ι₂ ⟧n≡ ι₁') →
                     ¬ (∃ λ τ'  → α⁼ ι₁ ⟦ inst i / ι₂ ⟧τ≡ τ')
            help ι₁≢ι₂ ¬sub-n (._ , subst-α-¬inst sub-n) = ¬sub-n (_ , sub-n)
            help ι₁≢ι₂ ¬sub-n (_ , subst-α-inst sub-τ) = ι₁≢ι₂ refl
    int ⟦ c ⟧τ? = yes (int , subst-int)
    ns ⟦ c ⟧τ? = yes (ns , subst-ns)
    (∀[ Δ ] Γ) ⟦ cᵥ / ι ⟧τ? with Δ ⟦ cᵥ / ι ⟧Δ? | Γ ⟦ cᵥ / length Δ + ι ⟧Γ?
    (∀[ Δ ] Γ) ⟦ cᵥ / ι ⟧τ? | yes (Δ' , sub-Δ) | yes (Γ' , sub-Γ) =
      yes (∀[ Δ' ] Γ' , subst-∀ sub-Δ sub-Γ)
    (∀[ Δ ] Γ) ⟦ cᵥ / ι ⟧τ? | no ¬sub-Δ | _ =
      no (λ { (._ , subst-∀ sub-Δ sub-Γ) → ¬sub-Δ (_ , sub-Δ) })
    (∀[ Δ ] Γ) ⟦ cᵥ / ι ⟧τ? | _ | no ¬sub-Γ =
      no (λ { (._ , subst-∀ sub-Δ sub-Γ) → ¬sub-Γ (_ , sub-Γ) })
    tuple τs ⟦ c ⟧τ? with τs ⟦ c ⟧τs⁻?
    tuple τs ⟦ c ⟧τ? | yes (τs' , sub-τs) =
      yes (tuple τs' , subst-tuple sub-τs)
    tuple τs ⟦ c ⟧τ? | no ¬sub-τs =
      no (λ { (._ , subst-tuple sub-τs) → ¬sub-τs (_ , sub-τs) })

    _⟦_⟧τ⁻? : ∀ τ⁻ c → Dec (∃ λ τ⁻' → τ⁻ ⟦ c ⟧τ⁻≡ τ⁻')
    (τ , φ) ⟦ c ⟧τ⁻? with τ ⟦ c ⟧τ?
    (τ , φ) ⟦ c ⟧τ⁻? | yes (τ' , sub-τ) =
      yes ((τ' , φ) , subst-τ⁻ sub-τ)
    (τ , φ) ⟦ c ⟧τ⁻? | no ¬sub-τ =
      no (λ { (._ , subst-τ⁻ sub-τ) → ¬sub-τ (_ , sub-τ) })

    _⟦_⟧τs⁻? : ∀ τs⁻ c → Dec (∃ λ τs⁻' → τs⁻ ⟦ c ⟧τs⁻≡ τs⁻')
    [] ⟦ c ⟧τs⁻? = yes ([] , [])
    (τ⁻ ∷ τs⁻) ⟦ c ⟧τs⁻? with τ⁻ ⟦ c ⟧τ⁻? | τs⁻ ⟦ c ⟧τs⁻?
    ... | yes (τ⁻' , sub-τ⁻) | yes (τs⁻' , sub-τs⁻) =
      yes (τ⁻' ∷ τs⁻' , sub-τ⁻ ∷ sub-τs⁻)
    ... | no ¬sub-τ⁻ | _ =
      no (λ { (τ⁻' ∷ τs⁻' , sub-τ⁻ ∷ sub-τs⁻) → ¬sub-τ⁻ (τ⁻' , sub-τ⁻) })
    ... | _ | no ¬sub-τs⁻ =
      no (λ { (τ⁻' ∷ τs⁻' , sub-τ⁻ ∷ sub-τs⁻) → ¬sub-τs⁻ (τs⁻' , sub-τs⁻) })

    _⟦_⟧σ? : ∀ σ c → Dec (∃ λ σ' → σ ⟦ c ⟧σ≡ σ')
    ρ⁼ ι₁ ⟦ weaken n / ι₂ ⟧σ? = yes (can-weaken-σ (ρ⁼ ι₁) n ι₂)
    ρ⁼ ι₁ ⟦ inst i / ι₂ ⟧σ? with ι₁ ⟦ inst i / ι₂ ⟧n? | ι₁ ≟ ι₂
    ρ⁼ ι₁ ⟦ inst i / ι₂ ⟧σ? | yes (n' , sub-n) | _ =
      yes (ρ⁼ n' , subst-ρ-¬inst sub-n)
    ρ⁼ ι ⟦ inst (ρ σ) / .ι ⟧σ? | no ¬sub-n | yes refl
      = yes (Σ-map id subst-ρ-inst (can-weaken-σ σ ι 0))
    ρ⁼ ι ⟦ inst (α τ) / .ι ⟧σ? | no ¬sub-n | yes refl
      = no (λ { (._ , subst-ρ-¬inst sub-n) → ¬sub-n (_ , sub-n) })
    ρ⁼ ι₁ ⟦ inst i / ι₂ ⟧σ? | no ¬sub-n | no ι₁≢ι₂
      = no (help ι₁≢ι₂ ¬sub-n)
      where help : ∀ {ι₁ ι₂ i} → ι₁ ≢ ι₂ →
                     ¬ (∃ λ ι₁' → ι₁    ⟦ inst i / ι₂ ⟧n≡ ι₁') →
                     ¬ (∃ λ σ'  → ρ⁼ ι₁ ⟦ inst i / ι₂ ⟧σ≡ σ')
            help ι₁≢ι₂ ¬sub-n (._ , subst-ρ-¬inst sub-n) = ¬sub-n (_ , sub-n)
            help ι₁≢ι₂ ¬sub-n (_ , subst-ρ-inst sub-σ) = ι₁≢ι₂ refl
    [] ⟦ c ⟧σ? = yes ([] , subst-[])
    (τ ∷ σ) ⟦ c ⟧σ? with τ ⟦ c ⟧τ? | σ ⟦ c ⟧σ?
    ... | yes (τ' , sub-τ) | yes (σ' , sub-σ) =
      yes (τ' ∷ σ' , sub-τ ∷ sub-σ)
    ... | no ¬sub-τ | _ =
      no (λ { (._ , sub-τ ∷ sub-σ) → ¬sub-τ (_ , sub-τ) })
    ... | _ | no ¬sub-σ =
      no (λ { (._ , sub-τ ∷ sub-σ) → ¬sub-σ (_ , sub-σ) })

    _⟦_⟧Γ? : ∀ Γ c → Dec (∃ λ Γ' → Γ ⟦ c ⟧Γ≡ Γ')
    registerₐ sp regs ⟦ c ⟧Γ? with sp ⟦ c ⟧σ? | regs ⟦ c ⟧regs?
    ... | yes (sp' , sub-sp) | yes (regs' , sub-regs) =
      yes (registerₐ sp' regs' , subst-registerₐ sub-sp sub-regs)
    ... | no ¬sub-sp | _ =
      no (λ { (._ , subst-registerₐ sub-sp sub-regs) → ¬sub-sp (_ , sub-sp) })
    ... | _ | no ¬sub-regs = no
      (λ { (._ , subst-registerₐ sub-sp sub-regs) →
         ¬sub-regs (_ , sub-regs) })

    _⟦_⟧regs? : ∀ {m} (regs : Vec Type m) c →
                  Dec (∃ λ regs' → regs ⟦ c ⟧regs≡ regs')
    [] ⟦ c ⟧regs? = yes ([] , [])
    (τ ∷ τs) ⟦ c ⟧regs? with τ ⟦ c ⟧τ? | τs ⟦ c ⟧regs?
    ... | yes (τ' , sub-τ) | yes (τs' , sub-τs) =
      yes (τ' ∷ τs' , sub-τ ∷ sub-τs)
    ... | no ¬sub-τ | _ =
      no (λ { (τ' ∷ τs' , sub-τ ∷ sub-τs) → ¬sub-τ (τ' , sub-τ) })
    ... | _ | no ¬sub-τs =
      no (λ { (τ' ∷ τs' , sub-τ ∷ sub-τs) → ¬sub-τs (τs' , sub-τs) })

    _⟦_⟧Δ? : ∀ Δ c → Dec (∃ λ Δ' → Δ ⟦ c ⟧Δ≡ Δ')
    [] ⟦ c ⟧Δ? = yes ([] , [])
    (a ∷ Δ) ⟦ cᵥ / ι ⟧Δ? with a ⟦ cᵥ / length Δ + ι ⟧a? | Δ ⟦ cᵥ / ι ⟧Δ?
    ... | yes (a' , sub-a) | yes (Δ' , sub-Δ) =
      yes (a' ∷ Δ' , sub-a ∷ sub-Δ)
    ... | no ¬sub-a | _ =
      no (λ { (a' ∷ Δ' , sub-a ∷ sub-Δ) → ¬sub-a (a' , sub-a) })
    ... | _ | no ¬sub-Δ =
      no (λ { (a' ∷ Δ' , sub-a ∷ sub-Δ) → ¬sub-Δ (Δ' , sub-Δ) })

    _⟦_⟧a? : ∀ a c → Dec (∃ λ a' → a ⟦ c ⟧a≡ a')
    α ⟦ c ⟧a? = yes (α , subst-α)
    ρ ⟦ c ⟧a? = yes (ρ , subst-ρ)

  mutual
    n-weaken-0 : ∀ n {ι} → n ⟦ weaken 0 / ι ⟧n≡ n
    n-weaken-0 n {ι} with ι ≤? n
    ... | yes n≥ι = subst-weaken-≥ n≥ι
    ... | no n≱ι = subst-< (NP.≰⇒> n≱ι)

    τ-weaken-0 : ∀ τ {ι} → τ ⟦ weaken 0 / ι ⟧τ≡ τ
    τ-weaken-0 (α⁼ ι) = subst-α-¬inst (n-weaken-0 ι)
    τ-weaken-0 int = subst-int
    τ-weaken-0 ns = subst-ns
    τ-weaken-0 (∀[ Δ ] Γ) = subst-∀ (Δ-weaken-0 Δ) (Γ-weaken-0 Γ)
    τ-weaken-0 (tuple τs⁻) = subst-tuple (τs⁻-weaken-0 τs⁻)

    τ⁻-weaken-0 : ∀ τ⁻ {ι} → τ⁻ ⟦ weaken 0 / ι ⟧τ⁻≡ τ⁻
    τ⁻-weaken-0 (τ , φ) = subst-τ⁻ (τ-weaken-0 τ)

    τs⁻-weaken-0 : ∀ τs⁻ {ι} → τs⁻ ⟦ weaken 0 / ι ⟧τs⁻≡ τs⁻
    τs⁻-weaken-0 [] = []
    τs⁻-weaken-0 (τ⁻ ∷ τs⁻) = τ⁻-weaken-0 τ⁻ ∷ τs⁻-weaken-0 τs⁻

    σ-weaken-0 : ∀ σ {ι} → σ ⟦ weaken 0 / ι ⟧σ≡ σ
    σ-weaken-0 (ρ⁼ ι) = subst-ρ-¬inst (n-weaken-0 ι)
    σ-weaken-0 [] = subst-[]
    σ-weaken-0 (τ ∷ σ) = τ-weaken-0 τ ∷ σ-weaken-0 σ

    Γ-weaken-0 : ∀ Γ {ι} → Γ ⟦ weaken 0 / ι ⟧Γ≡ Γ
    Γ-weaken-0 (registerₐ sp regs) =
      subst-registerₐ (σ-weaken-0 sp) (regs-weaken-0 regs)

    regs-weaken-0 : ∀ {m} (τs : Vec Type m) {ι} → τs ⟦ weaken 0 / ι ⟧regs≡ τs
    regs-weaken-0 [] = []
    regs-weaken-0 (τ ∷ τs) = τ-weaken-0 τ ∷ regs-weaken-0 τs

    Δ-weaken-0 : ∀ Δ {ι} → Δ ⟦ weaken 0 / ι ⟧Δ≡ Δ
    Δ-weaken-0 [] = []
    Δ-weaken-0 (a ∷ Δ) = a-weaken-0 a ∷ Δ-weaken-0 Δ

    a-weaken-0 : ∀ a {ι} → a ⟦ weaken 0 / ι ⟧a≡ a
    a-weaken-0 α = subst-α
    a-weaken-0 ρ = subst-ρ

Vec-Substitution⁺ : ∀ A {S} {{S⁺ : Substitution⁺ A {{S}}}} m →
                      Substitution⁺ (Vec A m) {{Vec-Substitution A m}}
Vec-Substitution⁺ A {S} m = substitution⁺
    unique
    weak
    dec
    xs-weaken-0

  where _⟦_⟧xs≡_ : ∀ {m} → Vec A m → WeakCast → Vec A m → Set
        xs ⟦ c ⟧xs≡ xs' =
          AllZipᵥ (λ x x' → x ⟦ c ⟧≡ x') xs xs'

        unique : ∀ {m c} {xs xs₁ xs₂ : Vec A m} →
                   xs ⟦ c ⟧xs≡ xs₁ →
                   xs ⟦ c ⟧xs≡ xs₂ →
                   xs₁ ≡ xs₂
        unique {xs = []} {[]} {[]} [] [] = refl
        unique {xs = x ∷ xs} {x₁ ∷ xs₁} {x₂ ∷ xs₂}
               (sub-x₁ ∷ sub-xs₁) (sub-x₂ ∷ sub-xs₂) =
          cong₂ _∷_ (subst-unique sub-x₁ sub-x₂) (unique sub-xs₁ sub-xs₂)

        weak : ∀ {m} (xs : Vec A m) w ι → ∃ λ xs' → xs ⟦ weaken w / ι ⟧xs≡ xs'
        weak [] w ι = [] , []
        weak (x ∷ xs) w ι = Σ-zip _∷_ _∷_ (can-weaken x w ι) (weak xs w ι)

        dec : ∀ {m} (xs : Vec A m) c → Dec (∃ λ xs' → xs ⟦ c ⟧xs≡ xs')
        dec [] c = yes ([] , [])
        dec (x ∷ xs) c with x ⟦ c ⟧? | dec xs c
        dec (x ∷ xs) c | yes (x' , sub-x) | yes (xs' , sub-xs) =
          yes ((x' ∷ xs') , sub-x ∷ sub-xs)
        dec (x ∷ xs) c | no ¬sub-x | _ =
          no (λ { (x' ∷ xs' , sub-x ∷ sub-xs) → ¬sub-x (x' , sub-x)})
        dec (x ∷ xs) c | _ | no ¬sub-xs =
          no (λ { (x' ∷ xs' , sub-x ∷ sub-xs) → ¬sub-xs (xs' , sub-xs)})

        xs-weaken-0 : ∀ {m} (xs : Vec A m) {ι} → xs ⟦ weaken 0 / ι ⟧xs≡ xs
        xs-weaken-0 [] = []
        xs-weaken-0 (x ∷ xs) = weaken-0 x ∷ xs-weaken-0 xs

List-Substitution⁺ : ∀ A {S} {{S⁺ : Substitution⁺ A {{S}}}} →
                       Substitution⁺ (List A) {{List-Substitution A}}
List-Substitution⁺ A = substitution⁺
    unique
    weak
    dec
    xs-weaken-0

  where _⟦_⟧xs≡_ : List A → WeakCast → List A → Set
        xs ⟦ c ⟧xs≡ xs' = AllZip (λ x x' → x ⟦ c ⟧≡ x') xs xs'

        unique : ∀ {c} {xs xs₁ xs₂ : List A} →
                   xs ⟦ c ⟧xs≡ xs₁ →
                   xs ⟦ c ⟧xs≡ xs₂ →
                   xs₁ ≡ xs₂
        unique [] [] = refl
        unique (sub-x₁ ∷ sub-xs₁) (sub-x₂ ∷ sub-xs₂)
          = cong₂ _∷_ (subst-unique sub-x₁ sub-x₂)
                      (unique sub-xs₁ sub-xs₂)

        weak : ∀ (xs : List A) w ι → ∃ λ xs' → xs ⟦ weaken w / ι ⟧xs≡ xs'
        weak [] w ι = [] , []
        weak (x ∷ xs) w ι = Σ-zip _∷_ _∷_ (can-weaken x w ι) (weak xs w ι)

        dec : ∀ (xs : List A) c → Dec (∃ λ xs' → xs ⟦ c ⟧xs≡ xs')
        dec [] c = yes ([] , [])
        dec (x ∷ xs) c with x ⟦ c ⟧? | dec xs c
        dec (x ∷ xs) c | yes (x' , sub-x) | yes (xs' , sub-xs) =
          yes (x' ∷ xs' , sub-x ∷ sub-xs)
        dec (x ∷ xs) c | no ¬sub-x | _ =
          no (λ { (x' ∷ xs' , sub-x ∷ sub-xs) → ¬sub-x (x' , sub-x)})
        dec (x ∷ xs) c | _ | no ¬sub-xs =
          no (λ { (x' ∷ xs' , sub-x ∷ sub-xs) → ¬sub-xs (xs' , sub-xs)})

        xs-weaken-0 : ∀ (xs : List A) {ι} → xs ⟦ weaken 0 / ι ⟧xs≡ xs
        xs-weaken-0 [] = []
        xs-weaken-0 (x ∷ xs) = weaken-0 x ∷ xs-weaken-0 xs

instance
  Type-Substitution⁺ : Substitution⁺ Type
  Type-Substitution⁺ =
    substitution⁺ subst-τ-unique can-weaken-τ _⟦_⟧τ? τ-weaken-0

  TypeVec-Substitution⁺ : ∀ {m} → Substitution⁺ (Vec Type m)
  TypeVec-Substitution⁺ = Vec-Substitution⁺ Type _

  TypeList-Substitution⁺  : Substitution⁺ (List Type)
  TypeList-Substitution⁺ = List-Substitution⁺ Type

  InitType-Substitution⁺  : Substitution⁺ InitType
  InitType-Substitution⁺ =
    substitution⁺ subst-τ⁻-unique can-weaken-τ⁻ _⟦_⟧τ⁻? τ⁻-weaken-0

  InitTypeVec-Substitution⁺ : ∀ {m} → Substitution⁺ (Vec InitType m)
  InitTypeVec-Substitution⁺ = Vec-Substitution⁺ InitType _

  InitTypeList-Substitution⁺  : Substitution⁺ (List InitType)
  InitTypeList-Substitution⁺ = List-Substitution⁺ InitType

  StackType-Substitution⁺  : Substitution⁺ StackType
  StackType-Substitution⁺ =
    substitution⁺ subst-σ-unique can-weaken-σ _⟦_⟧σ? σ-weaken-0

  RegisterAssignment-Substitution⁺  : Substitution⁺ RegisterAssignment
  RegisterAssignment-Substitution⁺ =
    substitution⁺ subst-Γ-unique can-weaken-Γ _⟦_⟧Γ? Γ-weaken-0

  TypeAssignment-Substitution⁺  : Substitution⁺ TypeAssignment
  TypeAssignment-Substitution⁺ =
    substitution⁺ subst-Δ-unique can-weaken-Δ _⟦_⟧Δ? Δ-weaken-0

  TypeAssignmentValue-Substitution⁺  : Substitution⁺ TypeAssignmentValue
  TypeAssignmentValue-Substitution⁺ =
    substitution⁺ subst-a-unique can-weaken-a _⟦_⟧a? a-weaken-0

  Instantiation-Substitution⁺  : Substitution⁺ Instantiation
  Instantiation-Substitution⁺ = substitution⁺ unique weak dec i-weaken-0
    where unique : ∀ {c} {i i₁ i₂} →
                     i ⟦ c ⟧i≡ i₁ →
                     i ⟦ c ⟧i≡ i₂ →
                     i₁ ≡ i₂
          unique (subst-α sub-τ₁) (subst-α sub-τ₂) =
            cong α (subst-unique sub-τ₁ sub-τ₂)
          unique (subst-ρ sub-σ₁) (subst-ρ sub-σ₂) =
            cong ρ (subst-unique sub-σ₁ sub-σ₂)

          weak : ∀ i w ι → ∃ λ i' → i ⟦ weaken w / ι ⟧i≡ i'
          weak (α τ) w ι = Σ-map α subst-α (can-weaken τ w ι)
          weak (ρ σ) w ι = Σ-map ρ subst-ρ (can-weaken σ w ι)

          dec : ∀ i c → Dec (∃ λ i' → i ⟦ c ⟧i≡ i')
          dec (α τ) c with τ ⟦ c ⟧?
          ... | yes (τ' , sub-τ) = yes (α τ' , subst-α sub-τ)
          ... | no ¬sub-τ =
            no (λ { (α τ' , subst-α sub-τ) → ¬sub-τ (τ' , sub-τ) })
          dec (ρ σ) c with σ ⟦ c ⟧?
          ... | yes (σ' , sub-σ) = yes (ρ σ' , subst-ρ sub-σ)
          ... | no ¬sub-σ =
            no (λ { (ρ σ' , subst-ρ sub-σ) → ¬sub-σ (σ' , sub-σ) })

          i-weaken-0 : ∀ i {ι} → i ⟦ weaken 0 / ι ⟧i≡ i
          i-weaken-0 (α τ) = subst-α (weaken-0 τ)
          i-weaken-0 (ρ σ) = subst-ρ (weaken-0 σ)

  StrongCastValue-Substitution⁺  : Substitution⁺ StrongCastValue
  StrongCastValue-Substitution⁺ = substitution⁺ unique weak dec cᵥ-weaken-0
    where unique : ∀ {c} {cᵥ cᵥ₁ cᵥ₂} →
                     cᵥ ⟦ c ⟧cᵥ≡ cᵥ₁ →
                     cᵥ ⟦ c ⟧cᵥ≡ cᵥ₂ →
                     cᵥ₁ ≡ cᵥ₂
          unique (subst-inst sub-i₁) (subst-inst sub-i₂) =
            cong inst (subst-unique sub-i₁ sub-i₂)
          unique (subst-weaken sub-Δ⁺₁) (subst-weaken sub-Δ⁺₂) =
            cong weaken (subst-unique sub-Δ⁺₁ sub-Δ⁺₂)

          weak : ∀ cᵥ w ι → ∃ λ cᵥ' → cᵥ ⟦ weaken w / ι ⟧cᵥ≡ cᵥ'
          weak (inst i) w ι = Σ-map inst subst-inst (can-weaken i w ι)
          weak (weaken Δ⁺) w ι = Σ-map weaken subst-weaken (can-weaken Δ⁺ w ι)

          dec : ∀ cᵥ c → Dec (∃ λ cᵥ' → cᵥ ⟦ c ⟧cᵥ≡ cᵥ')
          dec (inst i) c with i ⟦ c ⟧?
          ... | yes (i' , sub-i) = yes (inst i' , subst-inst sub-i)
          ... | no ¬sub-i =
            no (λ { (inst i' , subst-inst sub-i) → ¬sub-i (i' , sub-i) })
          dec (weaken Δ⁺) c with Δ⁺ ⟦ c ⟧?
          ... | yes (Δ⁺' , sub-Δ⁺) = yes (weaken Δ⁺' , subst-weaken sub-Δ⁺)
          ... | no ¬sub-Δ⁺ =
            no (λ { (weaken Δ⁺' , subst-weaken sub-Δ⁺) →
              ¬sub-Δ⁺ (Δ⁺' , sub-Δ⁺) })

          cᵥ-weaken-0 : ∀ cᵥ {ι} → cᵥ ⟦ weaken 0 / ι ⟧cᵥ≡ cᵥ
          cᵥ-weaken-0 (inst i) = subst-inst (weaken-0 i)
          cᵥ-weaken-0 (weaken Δ⁺) = subst-weaken (weaken-0 Δ⁺)

  StrongCast-Substitution⁺  : Substitution⁺ StrongCast
  StrongCast-Substitution⁺ = substitution⁺ unique weak dec c-weaken-0
    where unique : ∀ {c⋆} {c c₁ c₂} →
                     c ⟦ c⋆ ⟧c≡ c₁ →
                     c ⟦ c⋆ ⟧c≡ c₂ →
                     c₁ ≡ c₂
          unique (subst-/ sub-cᵥ₁) (subst-/ sub-cᵥ₂) =
            cong₂ _/_ (subst-unique sub-cᵥ₁ sub-cᵥ₂) refl

          weak : ∀ c w ι → ∃ λ c' → c ⟦ weaken w / ι ⟧c≡ c'
          weak (cᵥ / ι) w ι⋆ with can-weaken cᵥ w (ι⋆ ∸ suc ι)
          ... | cᵥ' , sub-cᵥ = cᵥ' / ι , subst-/ sub-cᵥ

          dec : ∀ c c⋆ → Dec (∃ λ c' → c ⟦ c⋆ ⟧c≡ c')
          dec (cᵥ / ι) (cᵥ⋆ / ι⋆) with cᵥ ⟦ cᵥ⋆ / ι⋆ ∸ suc ι ⟧?
          ... | yes (cᵥ' , sub-cᵥ) = yes (cᵥ' / ι , subst-/ sub-cᵥ)
          ... | no ¬sub-cᵥ =
            no (λ { (cᵥ' / .ι , subst-/ sub-cᵥ) → ¬sub-cᵥ (cᵥ' , sub-cᵥ) })

          c-weaken-0 : ∀ c {ι} → c ⟦ weaken 0 / ι ⟧c≡ c
          c-weaken-0 (cᵥ / ι) = subst-/ (weaken-0 cᵥ)

  WordValue-Substitution⁺  : Substitution⁺ WordValue
  WordValue-Substitution⁺ = substitution⁺ unique weak dec w-weaken-0
    where unique : ∀ {c} {w w₁ w₂} →
                     w ⟦ c ⟧w≡ w₁ →
                     w ⟦ c ⟧w≡ w₂ →
                     w₁ ≡ w₂
          unique subst-globval subst-globval = refl
          unique subst-heapval subst-heapval = refl
          unique subst-int subst-int = refl
          unique subst-ns subst-ns = refl
          unique (subst-uninit sub-τ₁) (subst-uninit sub-τ₂) =
            cong uninit (subst-unique sub-τ₁ sub-τ₂)
          unique (subst-⟦⟧ sub-w₁ sub-c₁) (subst-⟦⟧ sub-w₂ sub-c₂)
            rewrite unique sub-w₁ sub-w₂
                  | subst-unique sub-c₁ sub-c₂ = refl


          weak : ∀ w w⋆ ι → ∃ λ w' → w ⟦ weaken w⋆ / ι ⟧w≡ w'
          weak (globval l ♯a) w⋆ ι = globval l ♯a , subst-globval
          weak (heapval lₕ) w⋆ ι = heapval lₕ , subst-heapval
          weak (int n) w⋆ ι = int n , subst-int
          weak ns w⋆ ι = ns , subst-ns
          weak (uninit τ) w⋆ ι = Σ-map uninit subst-uninit (can-weaken τ w⋆ ι)
          weak (w ⟦ cᵥ / ιₘ ⟧) w⋆ ι =
            Σ-zip (λ w' cᵥ' → w' ⟦ cᵥ' / ιₘ ⟧) subst-⟦⟧
                  (weak w w⋆ ι)
                  (can-weaken cᵥ w⋆ (wctx-length w ∸ suc ιₘ + ι))

          dec : ∀ w c → Dec (∃ λ w' → w ⟦ c ⟧w≡ w')
          dec (globval l ♯a) c = yes (globval l ♯a , subst-globval)
          dec (heapval lₕ) c = yes (heapval lₕ , subst-heapval)
          dec (int n) c = yes (int n , subst-int)
          dec ns c = yes (ns , subst-ns)
          dec (uninit τ) c with τ ⟦ c ⟧?
          ... | yes (τ' , sub-τ) = yes (uninit τ' , subst-uninit sub-τ)
          ... | no ¬sub-τ =
            no (λ { (uninit τ' , subst-uninit sub-τ) → ¬sub-τ (τ' , sub-τ) })
          dec (w ⟦ cᵥ₁ / ιₘ ⟧) (cᵥ / ι)
            with dec w (cᵥ / ι) | cᵥ₁ ⟦ cᵥ / (wctx-length w ∸ suc ιₘ) + ι ⟧?
          ... | yes (w' , sub-w) | yes (cᵥ₂ , sub-cᵥ) =
            yes (w' ⟦ cᵥ₂ / ιₘ ⟧ , subst-⟦⟧ sub-w sub-cᵥ)
          ... | no ¬sub-w | _ =
            no (λ { (w' ⟦ cᵥ₂ / .ιₘ ⟧ , subst-⟦⟧ sub-w sub-cᵥ ) →
              ¬sub-w (w' , sub-w)})
          ... | _ | no ¬sub-cᵥ =
            no (λ { (w' ⟦ cᵥ₂ / .ιₘ ⟧ , subst-⟦⟧ sub-w sub-cᵥ ) →
              ¬sub-cᵥ (cᵥ₂ , sub-cᵥ)})

          w-weaken-0 : ∀ w {ι} → w ⟦ weaken 0 / ι ⟧w≡ w
          w-weaken-0 (globval l ♯a) = subst-globval
          w-weaken-0 (heapval lₕ) = subst-heapval
          w-weaken-0 (int n) = subst-int
          w-weaken-0 ns = subst-ns
          w-weaken-0 (uninit τ) = subst-uninit (weaken-0 τ)
          w-weaken-0 (w ⟦ cᵥ / ιₘ ⟧) = subst-⟦⟧ (w-weaken-0 w) (weaken-0 cᵥ)

  SmallValue-Substitution⁺  : Substitution⁺ SmallValue
  SmallValue-Substitution⁺ = substitution⁺ unique weak dec v-weaken-0
    where unique : ∀ {c} {v v₁ v₂} →
                     v ⟦ c ⟧v≡ v₁ →
                     v ⟦ c ⟧v≡ v₂ →
                     v₁ ≡ v₂
          unique subst-reg subst-reg = refl
          unique (subst-word sub-w₁) (subst-word sub-w₂) =
            cong word (subst-unique sub-w₁ sub-w₂)
          unique (subst-⟦⟧ sub-v₁ sub-c₁) (subst-⟦⟧ sub-v₂ sub-c₂) =
            cong₂ _⟦_⟧ (unique sub-v₁ sub-v₂) (subst-unique sub-c₁ sub-c₂)

          weak : ∀ v w ι → ∃ λ v' → v ⟦ weaken w / ι ⟧v≡ v'
          weak (reg ♯r) w ι = reg ♯r , subst-reg
          weak (word w) w⋆ ι = Σ-map word subst-word (can-weaken w w⋆ ι)
          weak (v ⟦ c ⟧) w ι =
            Σ-zip _⟦_⟧ subst-⟦⟧
                  (weak v w ι)
                  (can-weaken c w (vctx-length v + ι))

          dec : ∀ v c → Dec (∃ λ v' → v ⟦ c ⟧v≡ v')
          dec (reg ♯r) c = yes (reg ♯r , subst-reg)
          dec (word w) c with w ⟦ c ⟧?
          ... | yes (w' , sub-w) = yes (word w' , subst-word sub-w)
          ... | no ¬sub-w =
            no (λ { (word w' , subst-word sub-w) → ¬sub-w (w' , sub-w)})
          dec (v ⟦ c ⟧) (cᵥ / ι)
            with dec v (cᵥ / ι) | c ⟦ cᵥ / vctx-length v + ι ⟧?
          ... | yes (v' , sub-v) | yes (c' , sub-c) =
            yes (v' ⟦ c' ⟧ , subst-⟦⟧ sub-v sub-c)
          ... | no ¬sub-v | _ =
            no (λ { (v' ⟦ c' ⟧ , subst-⟦⟧ sub-v sub-c) →
              ¬sub-v (v' , sub-v)})
          ... | _ | no ¬sub-c =
            no (λ { (v' ⟦ c' ⟧ , subst-⟦⟧ sub-v sub-c) →
              ¬sub-c (c' , sub-c)})

          v-weaken-0 : ∀ v {ι} → v ⟦ weaken 0 / ι ⟧v≡ v
          v-weaken-0 (reg ♯r) = λ {ι} → subst-reg
          v-weaken-0 (word w) = subst-word (weaken-0 w)
          v-weaken-0 (v ⟦ c ⟧) = subst-⟦⟧ (v-weaken-0 v) (weaken-0 c)

  Instruction-Substitution⁺  : Substitution⁺ Instruction
  Instruction-Substitution⁺ = substitution⁺ unique weak dec ι-weaken-0
    where unique : ∀ {c} {ι ι₁ ι₂} →
                     ι ⟦ c ⟧ι≡ ι₁ →
                     ι ⟦ c ⟧ι≡ ι₂ →
                     ι₁ ≡ ι₂
          unique (subst-add sub-v₁) (subst-add sub-v₂)
            rewrite subst-unique sub-v₁ sub-v₂ = refl
          unique (subst-sub sub-v₁) (subst-sub sub-v₂)
            rewrite subst-unique sub-v₁ sub-v₂ = refl
          unique (subst-push sub-v₁) (subst-push sub-v₂)
            rewrite subst-unique sub-v₁ sub-v₂ = refl
          unique subst-pop subst-pop = refl
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

          weak : ∀ ι w ι⋆ → ∃ λ ι' → ι ⟦ weaken w / ι⋆ ⟧ι≡ ι'
          weak (add ♯rd ♯rs v) w ι⋆ =
            Σ-map (add ♯rd ♯rs) subst-add (can-weaken v w ι⋆)
          weak (sub ♯rd ♯rs v) w ι⋆ =
            Σ-map (sub ♯rd ♯rs) subst-sub (can-weaken v w ι⋆)
          weak (push v) w ι⋆ = Σ-map push subst-push (can-weaken v w ι⋆)
          weak pop w ι⋆ = pop , subst-pop
          weak (sld ♯rd i) w ι⋆ = sld ♯rd i , subst-sld
          weak (sst i ♯rs) w ι⋆ = sst i ♯rs , subst-sst
          weak (ld ♯rd ♯rs i) w ι⋆ = ld ♯rd ♯rs i , subst-ld
          weak (st ♯rd i ♯rs) w ι⋆ = st ♯rd i ♯rs , subst-st
          weak (malloc ♯rd τs) w ι⋆ =
            Σ-map (malloc ♯rd) subst-malloc (can-weaken τs w ι⋆)
          weak (mov ♯rd v) w ι⋆ =
            Σ-map (mov ♯rd) subst-mov (can-weaken v w ι⋆)
          weak (beq ♯r v) w ι⋆ =
            Σ-map (beq ♯r) subst-beq (can-weaken v w ι⋆)

          dec : ∀ ι c → Dec (∃ λ ι' → ι ⟦ c ⟧ι≡ ι')
          dec (add ♯rd ♯rs v) c
            with v ⟦ c ⟧?
          ... | yes (v' , sub-v) = yes (add ♯rd ♯rs v' , subst-add sub-v)
          ... | no ¬sub-v =
            no (λ { (add .♯rd .♯rs v' , subst-add sub-v) →
              ¬sub-v (v' , sub-v) })
          dec (sub ♯rd ♯rs v) c
            with v ⟦ c ⟧?
          ... | yes (v' , sub-v) = yes (sub ♯rd ♯rs v' , subst-sub sub-v)
          ... | no ¬sub-v =
            no (λ { (sub .♯rd .♯rs v' , subst-sub sub-v) →
              ¬sub-v (v' , sub-v) })
          dec (push v) c
            with v ⟦ c ⟧?
          ... | yes (v' , sub-v) = yes (push v' , subst-push sub-v)
          ... | no ¬sub-v =
            no (λ { (push v' , subst-push sub-v) → ¬sub-v (v' , sub-v) })
          dec pop c = yes (pop , subst-pop)
          dec (sld ♯rd i) c = yes (sld ♯rd i , subst-sld)
          dec (sst i ♯rs) c = yes (sst i ♯rs , subst-sst)
          dec (ld ♯rd ♯rs i) c = yes (ld ♯rd ♯rs i , subst-ld)
          dec (st ♯rd i ♯rs) c = yes (st ♯rd i ♯rs , subst-st)
          dec (malloc ♯rd τs) c
            with τs ⟦ c ⟧?
          ... | yes (τs' , sub-τs) =
            yes (malloc ♯rd τs' , subst-malloc sub-τs)
          ... | no ¬sub-τs =
            no (λ { (malloc .♯rd τs' , subst-malloc sub-τs) →
              ¬sub-τs (τs' , sub-τs) })
          dec (mov ♯rd v) c
            with v ⟦ c ⟧?
          ... | yes (v' , sub-v) = yes (mov ♯rd v' , subst-mov sub-v)
          ... | no ¬sub-v =
            no (λ { (mov .♯rd v' , subst-mov sub-v) →
              ¬sub-v (v' , sub-v) })
          dec (beq ♯r v) c
            with v ⟦ c ⟧?
          ... | yes (v' , sub-v) = yes (beq ♯r v' , subst-beq sub-v)
          ... | no ¬sub-v =
            no (λ { (beq .♯r v' , subst-beq sub-v) →
              ¬sub-v (v' , sub-v) })

          ι-weaken-0 : ∀ ι {ι⋆} → ι ⟦ weaken 0 / ι⋆ ⟧ι≡ ι
          ι-weaken-0 (add ♯rd ♯rs v) = subst-add (weaken-0 v)
          ι-weaken-0 (sub ♯rd ♯rs v) = subst-sub (weaken-0 v)
          ι-weaken-0 (push v) = subst-push (weaken-0 v)
          ι-weaken-0 pop = subst-pop
          ι-weaken-0 (sld ♯rd i) = subst-sld
          ι-weaken-0 (sst i ♯rs) = subst-sst
          ι-weaken-0 (ld ♯rd ♯rs i) = subst-ld
          ι-weaken-0 (st ♯rd i ♯rs) = subst-st
          ι-weaken-0 (malloc ♯rd τs) = subst-malloc (weaken-0 τs)
          ι-weaken-0 (mov ♯rd v) = subst-mov (weaken-0 v)
          ι-weaken-0 (beq ♯r v) = subst-beq (weaken-0 v)

  InstructionSequence-Substitution⁺  : Substitution⁺ InstructionSequence
  InstructionSequence-Substitution⁺ = substitution⁺ unique weak dec I-weaken-0
    where unique : ∀ {c} {I I₁ I₂} →
                     I ⟦ c ⟧I≡ I₁ →
                     I ⟦ c ⟧I≡ I₂ →
                     I₁ ≡ I₂
          unique (subst-~> sub-ι₁ sub-I₁) (subst-~> sub-ι₂ sub-I₂)
            = cong₂ _~>_ (subst-unique sub-ι₁ sub-ι₂) (unique sub-I₁ sub-I₂)
          unique (subst-jmp sub-v₁) (subst-jmp sub-v₂)
            = cong jmp (subst-unique sub-v₁ sub-v₂)

          weak : ∀ I w ι → ∃ λ I' → I ⟦ weaken w / ι ⟧I≡ I'
          weak (ι ~> I) w ι⋆ =
            Σ-zip _~>_ subst-~> (can-weaken ι w ι⋆) (weak I w ι⋆)
          weak (jmp v) w ι = Σ-map jmp subst-jmp (can-weaken v w ι)

          dec : ∀ I c → Dec (∃ λ I' → I ⟦ c ⟧I≡ I')
          dec (ι ~> I) c with ι ⟦ c ⟧? | dec I c
          ... | yes (ι' , sub-ι) | yes (I' , sub-I) =
            yes (ι' ~> I' , subst-~> sub-ι sub-I)
          ... | no ¬sub-ι | _ =
            no (λ { (ι' ~> I' , subst-~> sub-ι sub-I) → ¬sub-ι (ι' , sub-ι)})
          ... | _ | no ¬sub-I =
            no (λ { (ι' ~> I' , subst-~> sub-ι sub-I) → ¬sub-I (I' , sub-I)})
          dec (jmp v) c with v ⟦ c ⟧?
          ... | yes (v' , sub-v) = yes (jmp v' , subst-jmp sub-v)
          ... | no ¬sub-v =
            no (λ { (jmp v' , subst-jmp sub-v) → ¬sub-v (v' , sub-v)})

          I-weaken-0 : ∀ I {ι} → I ⟦ weaken 0 / ι ⟧I≡ I
          I-weaken-0 (ι ~> I) = subst-~> (weaken-0 ι) (I-weaken-0 I)
          I-weaken-0 (jmp v) = subst-jmp (weaken-0 v)
