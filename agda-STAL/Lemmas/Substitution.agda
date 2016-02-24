module Lemmas.Substitution where

open import Util
open import Judgments
open HighSyntax

-- The purpose of this file is to include proofs that:
-- * Substitution is deterministic.
-- * Substitution is decidible.
-- * An Agda-encoding of some commutative diagrams about substitution and weakening.
record Substitution⁺ (A : Set) {{S : Substitution A}} : Set1 where
  constructor substitution⁺
  field
    subst-unique : ∀ {v v₁ v₂ : A} {θ ι} →
                     v ⟦ θ / ι ⟧≡ v₁ →
                     v ⟦ θ / ι ⟧≡ v₂ →
                     v₁ ≡ v₂
    subst-dec : ∀ θ ι (v : A) → Dec (∃ λ v' → v ⟦ θ / ι ⟧≡ v')
    weaken-subst :
      ∀ {pos₁ pos₂} inc →
        pos₂ ≤ pos₁ →
        ∀ {θ} {v₁ v₂ : A} →
        v₁ ⟦ θ / pos₁ ⟧≡ v₂ →
        weaken pos₂ inc v₁ ⟦ θ / pos₁ + inc ⟧≡ weaken pos₂ inc v₂
    subst-subst :
      ∀ {pos₁ pos₂ θ₁ θ₁' θ₂} →
        θ₁ ⟦ θ₂ / pos₂ ⟧≡ θ₁' →
        {v₁ v₂ v₁' : A} →
        v₁ ⟦ θ₂ / suc pos₁ + pos₂ ⟧≡ v₁' →
        v₁ ⟦ θ₁ / pos₁ ⟧≡ v₂ →
        ∃ λ v₂' →
        v₂  ⟦ θ₂ / pos₁ + pos₂ ⟧≡ v₂' ×
        v₁' ⟦ θ₁' / pos₁ ⟧≡ v₂'

  subst-unique-many : ∀ {v v₁ v₂ : A} {θs ι} →
                        v ⟦ θs / ι ⟧many≡ v₁ →
                        v ⟦ θs / ι ⟧many≡ v₂ →
                        v₁ ≡ v₂
  subst-unique-many [] [] = refl
  subst-unique-many (sub-v₁ ∷ subs-v₁) (sub-v₂ ∷ subs-v₂)
    with subst-unique sub-v₁ sub-v₂
  subst-unique-many (sub-v₁ ∷ subs-v₁) (sub-v₂ ∷ subs-v₂)
      | refl
    with subst-unique-many subs-v₁ subs-v₂
  subst-unique-many (sub-v₁ ∷ subs-v₁) (sub-v₂ ∷ subs-v₂)
      | refl | refl = refl

  _⟦_/_⟧many? : ∀ (v : A) θs ι → Dec (∃ λ v' → v ⟦ θs / ι ⟧many≡ v')
  v ⟦ [] / ι ⟧many? = yes (v , [])
  v ⟦ θ ∷ θs / ι ⟧many?
    with subst-dec θ ι v
  ... | no ¬sub-v = no (λ { (vₑ , sub-v ∷ subs-v) → ¬sub-v (_ , sub-v)})
  ... | yes (v' , sub-v)
    with v' ⟦ θs / ι ⟧many?
  ... | yes (vₑ , subs-v) = yes (vₑ , sub-v ∷ subs-v)
  ... | no ¬subs-v = no help
    where help : ¬ (∃ λ vₑ → v ⟦ θ ∷ θs / ι ⟧many≡ vₑ)
          help (vₑ , sub-v' ∷ subs-v)
            with subst-unique sub-v sub-v'
          help (vₑ , sub-v' ∷ subs-v)
              | refl = ¬subs-v (vₑ , subs-v)

  subst-subst-many : ∀ {vᵢ₁ vᵢ₂ vₒ₁ : A}
                       {θ θs₁ θs₂ pos₁ pos₂} →
                       θs₁ ⟦ θ / pos₁ ⟧≡ θs₂ →
                       vᵢ₁ ⟦ θ / pos₂ + length θs₁ + pos₁ ⟧≡ vᵢ₂ →
                       vᵢ₁ ⟦ θs₁ / pos₂ ⟧many≡ vₒ₁ →
                       ∃ λ vₒ₂ →
                         vₒ₁ ⟦ θ / pos₂ + pos₁ ⟧≡ vₒ₂ ×
                         vᵢ₂ ⟦ θs₂ / pos₂ ⟧many≡ vₒ₂
  subst-subst-many {pos₂ = pos₂} [] sub-vᵢ []
    rewrite +-comm pos₂ 0
    = _ , sub-vᵢ , []
  subst-subst-many {θs₁ = θ₁ ∷ θs₁} {θs₂ = θ₂ ∷ θs₂} {pos₁} {pos₂} (sub-θ ∷ sub-θs) sub-vᵢ (sub₁-v ∷ subs₁-v)
    with begin
      (pos₂ + suc (length θs₁)) + pos₁
    ≡⟨ +-comm pos₂ (suc (length θs₁)) ∥ (λ v → v + pos₁) ⟩
      (suc (length θs₁) + pos₂) + pos₁
    ≡⟨ +-comm (length θs₁) pos₂ ∥ (λ v → suc v + pos₁) ⟩
      (suc pos₂ + length θs₁) + pos₁
    ≡⟨ +-assoc (suc pos₂) (length θs₁) pos₁ ⟩
      suc pos₂ + (length θs₁ + pos₁)
    ∎ where open Eq-Reasoning
  ... | eq
    rewrite eq
    with subst-subst {pos₁ = pos₂} {pos₂ = length θs₁ + pos₁} sub-θ sub-vᵢ sub₁-v
  ... | vₘ₂ , sub-vₘ , sub₂-v
    rewrite sym (+-assoc pos₂ (length θs₁) pos₁)
    with subst-subst-many sub-θs sub-vₘ subs₁-v
  ... | vₒ₂ , sub-vₒ , subs₂-v
    = vₒ₂ , sub-vₒ , sub₂-v ∷ subs₂-v

open Substitution⁺ {{...}} public

private
  mutual
    subst-uniqueᵗ : ∀ A {{S : Substitution A}} → Set
    subst-uniqueᵗ A = ∀ {v v₁ v₂ : A} {θ ι} →
                        v ⟦ θ / ι ⟧≡ v₁ →
                        v ⟦ θ / ι ⟧≡ v₂ →
                        v₁ ≡ v₂

    τ-subst-unique : subst-uniqueᵗ Type
    τ-subst-unique (subst-α-> ι>ι) subst-α-≡
      with 1+n≰n ι>ι
    ... | ()
    τ-subst-unique (subst-α-> ι₁>ι₂) (subst-α-> ι₁>ι₂') = refl
    τ-subst-unique (subst-α-> ι₁>ι₂) (subst-α-< ι₁<ι₂)
      with 1+n≰n (Nat-<-trans ι₁<ι₂ ι₁>ι₂)
    ... | ()
    τ-subst-unique subst-α-≡ subst-α-≡ = refl
    τ-subst-unique subst-α-≡ (subst-α-> ι>ι)
      with 1+n≰n ι>ι
    ... | ()
    τ-subst-unique subst-α-≡ (subst-α-< ι<ι)
      with 1+n≰n ι<ι
    ... | ()
    τ-subst-unique (subst-α-< ι<ι) subst-α-≡
      with 1+n≰n ι<ι
    ... | ()
    τ-subst-unique (subst-α-< ι₁<ι₂) (subst-α-> ι₁>ι₂)
      with 1+n≰n (Nat-<-trans ι₁<ι₂ ι₁>ι₂)
    ... | ()
    τ-subst-unique (subst-α-< ι₁<ι₂) (subst-α-< ι₁<ι₂') = refl
    τ-subst-unique subst-int subst-int = refl
    τ-subst-unique subst-ns subst-ns = refl
    τ-subst-unique (subst-∀ sub-Γ₁) (subst-∀ sub-Γ₂)
      rewrite Γ-subst-unique sub-Γ₁ sub-Γ₂ = refl
    τ-subst-unique (subst-tuple sub-τs⁻₁) (subst-tuple sub-τs⁻₂)
      rewrite τs⁻-subst-unique sub-τs⁻₁ sub-τs⁻₂ = refl

    τ⁻-subst-unique : subst-uniqueᵗ InitType
    τ⁻-subst-unique (subst-τ⁻ {φ = φ} sub-τ₁) (subst-τ⁻ sub-τ₂) =
      cong₂ _,_ (τ-subst-unique sub-τ₁ sub-τ₂) refl

    τs⁻-subst-unique : subst-uniqueᵗ (List InitType)
    τs⁻-subst-unique [] [] = refl
    τs⁻-subst-unique (sub-τ⁻₁ ∷ sub-τs⁻₁) (sub-τ⁻₂ ∷ sub-τs⁻₂) =
        cong₂ _∷_ (τ⁻-subst-unique sub-τ⁻₁ sub-τ⁻₂)
                  (τs⁻-subst-unique sub-τs⁻₁ sub-τs⁻₂)

    σ-subst-unique : subst-uniqueᵗ StackType
    σ-subst-unique (subst-ρ-> ι>ι) subst-ρ-≡
      with 1+n≰n ι>ι
    ... | ()
    σ-subst-unique (subst-ρ-> ι₁>ι₂) (subst-ρ-> ι₁>ι₂') = refl
    σ-subst-unique (subst-ρ-> ι₁>ι₂) (subst-ρ-< ι₁<ι₂)
      with 1+n≰n (Nat-<-trans ι₁<ι₂ ι₁>ι₂)
    ... | ()
    σ-subst-unique subst-ρ-≡ subst-ρ-≡ = refl
    σ-subst-unique subst-ρ-≡ (subst-ρ-> ι>ι)
      with 1+n≰n ι>ι
    ... | ()
    σ-subst-unique subst-ρ-≡ (subst-ρ-< ι<ι)
      with 1+n≰n ι<ι
    ... | ()
    σ-subst-unique (subst-ρ-< ι<ι) subst-ρ-≡
      with 1+n≰n ι<ι
    ... | ()
    σ-subst-unique (subst-ρ-< ι₁<ι₂) (subst-ρ-> ι₁>ι₂)
      with 1+n≰n (Nat-<-trans ι₁<ι₂ ι₁>ι₂)
    ... | ()
    σ-subst-unique (subst-ρ-< ι₁<ι₂) (subst-ρ-< ι₁<ι₂') = refl
    σ-subst-unique [] [] = refl
    σ-subst-unique (sub-τ₁ ∷ sub-σ₁) (sub-τ₂ ∷ sub-σ₂)
      rewrite τ-subst-unique sub-τ₁ sub-τ₂
            | σ-subst-unique sub-σ₁ sub-σ₂ = refl

    Γ-subst-unique : subst-uniqueᵗ RegisterAssignment
    Γ-subst-unique (subst-registerₐ sub-sp₁ sub-regs₁)
                   (subst-registerₐ sub-sp₂ sub-regs₂) =
      cong₂ registerₐ (σ-subst-unique sub-sp₁ sub-sp₂)
                      (regs-subst-unique sub-regs₁ sub-regs₂)

    regs-subst-unique : ∀ {m} → subst-uniqueᵗ (Vec Type m)
    regs-subst-unique {v = []} {[]} {[]} [] [] = refl
    regs-subst-unique {v = τ ∷ τs} {τ₁ ∷ τs₁} {τ₂ ∷ τs₂}
      (sub-τ₁ ∷ sub-τs₁) (sub-τ₂ ∷ sub-τs₂) =
        cong₂ _∷_ (τ-subst-unique sub-τ₁ sub-τ₂)
                  (regs-subst-unique sub-τs₁ sub-τs₂)

  mutual
    subst-decᵗ : ∀ A {{S : Substitution A}} → Set
    subst-decᵗ A = ∀ θ ι (v : A) → Dec (∃ λ v' → v ⟦ θ / ι ⟧≡ v')

    τ-subst-dec : subst-decᵗ Type
    τ-subst-dec θ ι₂ (α⁼ ι₁)
      with Nat-cmp ι₁ ι₂
    ... | tri< ι₁<ι₂ _ _ = yes (α⁼ ι₁ , subst-α-< ι₁<ι₂)
    τ-subst-dec (α τ) .ι (α⁼ ι)
        | tri≈ _ refl _ = yes (weaken 0 ι τ , subst-α-≡)
    τ-subst-dec (ρ σ) .ι (α⁼ ι)
        | tri≈ _ refl _ =
      no (λ { (._ , subst-α-> ι>ι) → 1+n≰n ι>ι
            ; (._ , subst-α-< ι<ι) → 1+n≰n ι<ι })
    ... | tri> _ _ ι₁>ι₂ = yes (α⁼ (pred ι₁) , subst-α-> ι₁>ι₂)
    τ-subst-dec θ ι int = yes (int , subst-int)
    τ-subst-dec θ ι ns = yes (ns , subst-ns)
    τ-subst-dec θ ι (∀[ Δ ] Γ)
      with Γ-subst-dec θ (length Δ + ι) Γ
    ... | yes (Γ' , sub-Γ) = yes (∀[ Δ ] Γ' , subst-∀ sub-Γ)
    ... | no ¬sub-Γ = no (λ { (._ , subst-∀ sub-Γ) → ¬sub-Γ (_ , sub-Γ)})
    τ-subst-dec θ ι (tuple τs)
      with τs⁻-subst-dec θ ι τs
    ... | yes (τs' , sub-τs) =
          yes (tuple τs' , subst-tuple sub-τs)
    ... | no ¬sub-τs =
      no (λ { (._ , subst-tuple sub-τs) → ¬sub-τs (_ , sub-τs) })

    τ⁻-subst-dec : subst-decᵗ InitType
    τ⁻-subst-dec θ ι (τ , φ)
      with τ-subst-dec θ ι τ
    ... | yes (τ' , sub-τ) = yes ((τ' , φ) , subst-τ⁻ sub-τ)
    ... | no ¬sub-τ = no (λ { (._ , subst-τ⁻ sub-τ) → ¬sub-τ (_ , sub-τ) })

    τs⁻-subst-dec : subst-decᵗ (List InitType)
    τs⁻-subst-dec θ ι [] = yes ([] , [])
    τs⁻-subst-dec θ ι (τ⁻ ∷ τs⁻)
      with τ⁻-subst-dec θ ι τ⁻ | τs⁻-subst-dec θ ι τs⁻
    ... | yes (τ⁻' , sub-τ⁻) | yes (τs⁻' , sub-τs⁻) =
      yes (τ⁻' ∷ τs⁻' , sub-τ⁻ ∷ sub-τs⁻)
    ... | no ¬sub-τ⁻ | _ =
      no (λ { (τ⁻' ∷ τs⁻' , sub-τ⁻ ∷ sub-τs⁻) → ¬sub-τ⁻ (τ⁻' , sub-τ⁻) })
    ... | _ | no ¬sub-τs⁻ =
      no (λ { (τ⁻' ∷ τs⁻' , sub-τ⁻ ∷ sub-τs⁻) → ¬sub-τs⁻ (τs⁻' , sub-τs⁻) })

    σ-subst-dec : subst-decᵗ StackType
    σ-subst-dec θ ι₂ (ρ⁼ ι₁)
      with Nat-cmp ι₁ ι₂
    ... | tri< ι₁<ι₂ _ _ = yes (ρ⁼ ι₁ , subst-ρ-< ι₁<ι₂)
    σ-subst-dec (α τ) .ι (ρ⁼ ι)
        | tri≈ _ refl _ =
      no (λ { (._ , subst-ρ-> ι>ι) → 1+n≰n ι>ι
            ; (._ , subst-ρ-< ι<ι) → 1+n≰n ι<ι })
    σ-subst-dec (ρ σ) .ι (ρ⁼ ι)
        | tri≈ _ refl _ = yes (weaken 0 ι σ , subst-ρ-≡)
    ... | tri> _ _ ι₁>ι₂ = yes (ρ⁼ (pred ι₁) , subst-ρ-> ι₁>ι₂)
    σ-subst-dec θ ι [] = yes ([] , [])
    σ-subst-dec θ ι (τ ∷ σ)
      with τ-subst-dec θ ι τ | σ-subst-dec θ ι σ
    ... | yes (τ' , sub-τ) | yes (σ' , sub-σ) =
      yes (τ' ∷ σ' , sub-τ ∷ sub-σ)
    ... | no ¬sub-τ | _ =
      no (λ { (._ , sub-τ ∷ sub-σ) → ¬sub-τ (_ , sub-τ) })
    ... | _ | no ¬sub-σ =
      no (λ { (._ , sub-τ ∷ sub-σ) → ¬sub-σ (_ , sub-σ) })

    Γ-subst-dec : subst-decᵗ RegisterAssignment
    Γ-subst-dec θ ι (registerₐ sp regs)
      with σ-subst-dec θ ι sp | regs-subst-dec θ ι regs
    ... | yes (sp' , sub-sp) | yes (regs' , sub-regs) =
      yes (registerₐ sp' regs' , subst-registerₐ sub-sp sub-regs)
    ... | no ¬sub-sp | _ =
      no (λ { (._ , subst-registerₐ sub-sp sub-regs) → ¬sub-sp (_ , sub-sp) })
    ... | _ | no ¬sub-regs = no
      (λ { (._ , subst-registerₐ sub-sp sub-regs) →
         ¬sub-regs (_ , sub-regs) })

    regs-subst-dec : ∀ {n} → subst-decᵗ (Vec Type n)
    regs-subst-dec θ ι [] = yes ([] , [])
    regs-subst-dec θ ι (τ ∷ τs)
      with τ-subst-dec θ ι τ | regs-subst-dec θ ι τs
    ... | yes (τ' , sub-τ) | yes (τs' , sub-τs) =
      yes (τ' ∷ τs' , sub-τ ∷ sub-τs)
    ... | no ¬sub-τ | _ =
      no (λ { (τ' ∷ τs' , sub-τ ∷ sub-τs) → ¬sub-τ (τ' , sub-τ) })
    ... | _ | no ¬sub-τs =
      no (λ { (τ' ∷ τs' , sub-τ ∷ sub-τs) → ¬sub-τs (τs' , sub-τs) })

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
                        ∀ {θ} {v₁ v₂ : A} →
                        v₁ ⟦ θ / pos₁ ⟧≡ v₂ →
                        weaken pos₂ inc v₁ ⟦ θ / pos₁ + inc ⟧≡ weaken pos₂ inc v₂
    τ-weaken-subst : weaken-substᵗ Type
    τ-weaken-subst {pos₁} {pos₂} inc pos₂≤pos₁ {v₁ = α⁼ ι} (subst-α-> ι>pos₁)
      with pos₂ ≤? ι | pos₂ ≤? pred ι
    ... | no pos₂≰ι | _
      with pos₂≰ι (Nat-≤-trans pos₂≤pos₁ (≤⇒pred≤ _ _ ι>pos₁))
    ... | ()
    τ-weaken-subst inc pos₂≤pos₁ {v₁ = α⁼ ι} (subst-α-> ι>pos₁)
        | _ | no pos₂≰ι'
      with pos₂≰ι' (Nat-≤-trans pos₂≤pos₁ (pred-mono ι>pos₁))
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
      = subst-α-< (Nat-≤-trans ι<pos₁ (m≤m+n pos₁ inc))
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
      with pos₂≰ι (Nat-≤-trans pos₂≤pos₁ (≤⇒pred≤ _ _ ι>pos₁))
    ... | ()
    σ-weaken-subst inc pos₂≤pos₁ {v₁ = ρ⁼ ι} (subst-ρ-> ι>pos₁)
        | _ | no pos₂≰ι'
      with pos₂≰ι' (Nat-≤-trans pos₂≤pos₁ (pred-mono ι>pos₁))
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
      = subst-ρ-< (Nat-≤-trans ι<pos₁ (m≤m+n pos₁ inc))
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
                        ∀ {θ} (v : A) →
                        weaken pos₁ (suc inc) v ⟦ θ / pos₂ ⟧≡ weaken pos₁ inc v

    τ-subst-weaken : subst-weakenᵗ Type
    τ-subst-weaken {pos₁} inc pos₁≤pos₂ pos₂≤inc+pos₁ (α⁼ ι)
      with pos₁ ≤? ι
    ... | yes pos₁≤ι = subst-α-> (s≤s (Nat-≤-trans pos₂≤inc+pos₁ (l+m≤l+n inc pos₁≤ι)))
    ... | no pos₁≰ι = subst-α-< (Nat-≤-trans (≰⇒> pos₁≰ι) pos₁≤pos₂)
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
      ∎ where open ≤-Reasoning
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
    ... | no pos₁≰ι = subst-ρ-< (Nat-≤-trans (≰⇒> pos₁≰ι) pos₁≤pos₂)
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
    ∀ {ι pos θ τ} →
      ι > pos →
      α⁼ ι ⟦ θ / pos ⟧≡ τ →
      ∃ λ ι' →
        ι ≡ suc ι' ×
        τ ≡ α⁼ ι'
  sub-α-helper (s≤s ι≥pos) (subst-α-> (s≤s ι≥pos')) = _ , refl , refl
  sub-α-helper ι>pos subst-α-≡
    with 1+n≰n ι>pos
  ... | ()
  sub-α-helper ι>pos (subst-α-< ι<pos)
    with 1+n≰n (Nat-<-trans ι<pos ι>pos)
  ... | ()

  sub-ρ-helper :
    ∀ {ι pos θ σ} →
      ι > pos →
      ρ⁼ ι ⟦ θ / pos ⟧≡ σ →
      ∃ λ ι' →
        ι ≡ suc ι' ×
        σ ≡ ρ⁼ ι'
  sub-ρ-helper (s≤s ι≥pos) (subst-ρ-> (s≤s ι≥pos')) = _ , refl , refl
  sub-ρ-helper ι>pos subst-ρ-≡
    with 1+n≰n ι>pos
  ... | ()
  sub-ρ-helper ι>pos (subst-ρ-< ι<pos)
    with 1+n≰n (Nat-<-trans ι<pos ι>pos)
  ... | ()

  mutual
    subst-substᵗ : ∀ A {{_ : Substitution A}} → Set
    subst-substᵗ A = ∀ {pos₁ pos₂ θ₁ θ₁' θ₂} →
                       θ₁ ⟦ θ₂ / pos₂ ⟧≡ θ₁' →
                       {v₁ v₂ v₁' : A} →
                       v₁ ⟦ θ₂ / suc pos₁ + pos₂ ⟧≡ v₁' →
                       v₁ ⟦ θ₁ / pos₁ ⟧≡ v₂ →
                       ∃ λ v₂' →
                         v₂  ⟦ θ₂ / pos₁ + pos₂ ⟧≡ v₂' ×
                         v₁' ⟦ θ₁' / pos₁ ⟧≡ v₂'

    τ-subst-subst : subst-substᵗ Type
    τ-subst-subst {pos₁} {pos₂} sub-θ (subst-α-> (s≤s ι>pos)) (subst-α-> (s≤s ι>pos'))
      rewrite +-comm pos₁ (suc pos₂)
            | +-comm pos₂ pos₁
      = _ , subst-α-> ι>pos , subst-α-> (Nat-≤-trans (s≤s (m≤m+n pos₁ pos₂)) ι>pos)
    τ-subst-subst {pos₁} {pos₂} sub-θ (subst-α-> ι>pos) subst-α-≡
      with 1+n≰n (Nat-≤-trans (s≤s (≤-step (m≤m+n pos₁ pos₂))) ι>pos)
    ... | ()
    τ-subst-subst {pos₁} {pos₂} sub-θ (subst-α-> ι>pos) (subst-α-< ι<pos)
      with 1+n≰n (Nat-≤-trans ι<pos (Nat-≤-trans (≤-steps 2 (m≤m+n pos₁ pos₂)) ι>pos))
    ... | ()
    τ-subst-subst {pos₁} {pos₂} {θ₂ = α τ} sub-θ subst-α-≡ sub-τ₁'
      with sub-α-helper (s≤s (m≤m+n pos₁ pos₂)) sub-τ₁'
    ... | ι' , eq₁ , eq₂
      rewrite sym (cong pred eq₁)
            | eq₂
        = _ , subst-α-≡ , τ-subst-weaken (pos₁ + pos₂) z≤n (Nat-≤-trans (m≤m+n pos₁ pos₂) (m≤m+n (pos₁ + pos₂) zero)) τ
    τ-subst-subst {pos₁} {pos₂} sub-θ (subst-α-< (s≤s ι≤pos)) (subst-α-> (s≤s ι≥pos'))
        = _ , subst-α-< ι≤pos , subst-α-> (s≤s ι≥pos')
    τ-subst-subst {pos₁} {pos₂} (subst-α sub-τ) (subst-α-< ι<pos) subst-α-≡
      rewrite +-comm pos₁ pos₂
        = _ , τ-weaken-subst pos₁ z≤n sub-τ , subst-α-≡
    τ-subst-subst {pos₁} {pos₂} sub-θ (subst-α-< ι<pos) (subst-α-< ι<pos')
      = _ , subst-α-< (Nat-≤-trans ι<pos' (m≤m+n pos₁ pos₂)) , subst-α-< ι<pos'
    τ-subst-subst sub-θ subst-int subst-int = int , subst-int , subst-int
    τ-subst-subst sub-θ subst-ns subst-ns = ns , subst-ns , subst-ns
    τ-subst-subst {pos₁} {pos₂} sub-θ {∀[ Δ ] Γ₁} (subst-∀ sub-Γ₁) (subst-∀ sub-Γ₁')
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
      with Γ-subst-subst sub-θ sub-Γ₁ sub-Γ₁'
    ... | Γ₂' , sub-Γ₂ , sub-Γ₂'
      rewrite +-assoc (length Δ) pos₁ pos₂
      = ∀[ Δ ] Γ₂' , subst-∀ sub-Γ₂ , subst-∀ sub-Γ₂'
    τ-subst-subst sub-θ (subst-tuple sub-τs⁻₁) (subst-tuple sub-τs⁻₁')
      with τs⁻-subst-subst sub-θ sub-τs⁻₁ sub-τs⁻₁'
    ... | τs⁻₂ , sub-τs⁻₂ , sub-τs⁻₂'
      = _ , subst-tuple sub-τs⁻₂ , subst-tuple sub-τs⁻₂'

    τ⁻-subst-subst : subst-substᵗ InitType
    τ⁻-subst-subst sub-θ (subst-τ⁻ sub-τ₁) (subst-τ⁻ sub-τ₁')
      with τ-subst-subst sub-θ sub-τ₁ sub-τ₁'
    ... | τ⁻₂ , sub-τ⁻₂ , sub-τ⁻₂'
      = _ , subst-τ⁻ sub-τ⁻₂ , subst-τ⁻ sub-τ⁻₂'

    τs⁻-subst-subst : subst-substᵗ (List InitType)
    τs⁻-subst-subst sub-θ [] [] = [] , [] , []
    τs⁻-subst-subst sub-θ (sub-τ₁⁻ ∷ sub-τs₁⁻) (sub-τ₁⁻' ∷ sub-τs₁⁻')
      with τ⁻-subst-subst sub-θ sub-τ₁⁻ sub-τ₁⁻'
    ... | τ⁻₂ , sub-τ⁻₂ , sub-τ⁻₂'
      with τs⁻-subst-subst sub-θ sub-τs₁⁻ sub-τs₁⁻'
    ... | τs⁻₂ , sub-τs⁻₂ , sub-τs⁻₂'
      = _ , sub-τ⁻₂ ∷ sub-τs⁻₂ , sub-τ⁻₂' ∷ sub-τs⁻₂'

    σ-subst-subst : subst-substᵗ StackType
    σ-subst-subst {pos₁} {pos₂} sub-θ (subst-ρ-> (s≤s ι>pos)) (subst-ρ-> (s≤s ι>pos'))
      rewrite +-comm pos₁ (suc pos₂)
            | +-comm pos₂ pos₁
      = _ , subst-ρ-> ι>pos , subst-ρ-> (Nat-≤-trans (s≤s (m≤m+n pos₁ pos₂)) ι>pos)
    σ-subst-subst {pos₁} {pos₂} sub-θ (subst-ρ-> ι>pos) subst-ρ-≡
      with 1+n≰n (Nat-≤-trans (s≤s (≤-step (m≤m+n pos₁ pos₂))) ι>pos)
    ... | ()
    σ-subst-subst {pos₁} {pos₂} sub-θ (subst-ρ-> ι>pos) (subst-ρ-< ι<pos)
      with 1+n≰n (Nat-≤-trans ι<pos (Nat-≤-trans (≤-steps 2 (m≤m+n pos₁ pos₂)) ι>pos))
    ... | ()
    σ-subst-subst {pos₁} {pos₂} {θ₂ = ρ σ} sub-θ subst-ρ-≡ sub-σ₁'
      with sub-ρ-helper (s≤s (m≤m+n pos₁ pos₂)) sub-σ₁'
    ... | ι' , eq₁ , eq₂
      rewrite sym (cong pred eq₁)
            | eq₂
        = _ , subst-ρ-≡ , σ-subst-weaken (pos₁ + pos₂) z≤n (Nat-≤-trans (m≤m+n pos₁ pos₂) (m≤m+n (pos₁ + pos₂) zero)) σ
    σ-subst-subst {pos₁} {pos₂} sub-θ (subst-ρ-< (s≤s ι≤pos)) (subst-ρ-> (s≤s ι≥pos'))
        = _ , subst-ρ-< ι≤pos , subst-ρ-> (s≤s ι≥pos')
    σ-subst-subst {pos₁} {pos₂} (subst-ρ sub-σ) (subst-ρ-< ι<pos) subst-ρ-≡
      rewrite +-comm pos₁ pos₂
        = _ , σ-weaken-subst pos₁ z≤n sub-σ , subst-ρ-≡
    σ-subst-subst {pos₁} {pos₂} sub-θ (subst-ρ-< ι<pos) (subst-ρ-< ι<pos')
      = _ , subst-ρ-< (Nat-≤-trans ι<pos' (m≤m+n pos₁ pos₂)) , subst-ρ-< ι<pos'
    σ-subst-subst sub-θ [] [] = [] , [] , []
    σ-subst-subst sub-θ (sub-τ₁ ∷ sub-σ₁) (sub-τ₁' ∷ sub-σ₁')
      with τ-subst-subst sub-θ sub-τ₁ sub-τ₁'
    ... | τ₂ , sub-τ₂ , sub-τ₂'
      with σ-subst-subst sub-θ sub-σ₁ sub-σ₁'
    ... | σ₂ , sub-σ₂ , sub-σ₂'
      = _ , sub-τ₂ ∷ sub-σ₂ , sub-τ₂' ∷ sub-σ₂'

    Γ-subst-subst : subst-substᵗ RegisterAssignment
    Γ-subst-subst sub-θ (subst-registerₐ sub-σ₁ sub-τs₁) (subst-registerₐ sub-σ₁' sub-τs₁')
      with σ-subst-subst sub-θ sub-σ₁ sub-σ₁'
    ... | σ₂ , sub-σ₂ , sub-σ₂'
      with regs-subst-subst sub-θ sub-τs₁ sub-τs₁'
    ... | τs₂ , sub-τs₂ , sub-τs₂'
      = _ , subst-registerₐ sub-σ₂ sub-τs₂ , subst-registerₐ sub-σ₂' sub-τs₂'

    regs-subst-subst : ∀ {n} → subst-substᵗ (Vec Type n)
    regs-subst-subst sub-θ [] [] = [] , [] , []
    regs-subst-subst sub-θ (sub-τ₁ ∷ sub-τs₁) (sub-τ₁' ∷ sub-τs₁')
      with τ-subst-subst sub-θ sub-τ₁ sub-τ₁'
    ... | τ₂ , sub-τ₂ , sub-τ₂'
      with regs-subst-subst sub-θ sub-τs₁ sub-τs₁'
    ... | τs₂ , sub-τs₂ , sub-τs₂'
      = _ , sub-τ₂ ∷ sub-τs₂ , sub-τ₂' ∷ sub-τs₂'

List-Substitution⁺ : ∀ A {S : Substitution A} {{S⁺ : Substitution⁺ A}} →
                         Substitution⁺ (List A) {{List-Substitution A}}
List-Substitution⁺ A = substitution⁺
  (AllZip-≡ ∘₂ AllZip-zip subst-unique)
  (λ θ ι → dec-inj All-∃→ All-∃← ∘ All-dec (subst-dec θ ι))
  (λ inc pos₂≤pos₁ → AllZip-map' _ _ (weaken-subst inc pos₂≤pos₁))
  (λ sub-θ → AllZip-∃→ ∘₂ AllZip-swap ∘₂ AllZip-zip (subst-subst sub-θ))

instance
  Type-Substitution⁺ : Substitution⁺ Type
  Type-Substitution⁺ =
    substitution⁺ τ-subst-unique τ-subst-dec τ-weaken-subst τ-subst-subst

  TypeList-Substitution⁺ : Substitution⁺ (List Type)
  TypeList-Substitution⁺ = List-Substitution⁺ Type

  TypeVec-Substitution⁺ : ∀ {m} → Substitution⁺ (Vec Type m)
  TypeVec-Substitution⁺ = substitution⁺ regs-subst-unique regs-subst-dec regs-weaken-subst regs-subst-subst

  InitType-Substitution⁺ : Substitution⁺ InitType
  InitType-Substitution⁺ =
    substitution⁺ τ⁻-subst-unique τ⁻-subst-dec τ⁻-weaken-subst τ⁻-subst-subst

  InitTypeList-Substitution⁺ : Substitution⁺ (List InitType)
  InitTypeList-Substitution⁺ = substitution⁺ τs⁻-subst-unique τs⁻-subst-dec τs⁻-weaken-subst τs⁻-subst-subst

  StackType-Substitution⁺ : Substitution⁺ StackType
  StackType-Substitution⁺ =
    substitution⁺ σ-subst-unique σ-subst-dec σ-weaken-subst σ-subst-subst

  RegisterAssignment-Substitution⁺ : Substitution⁺ RegisterAssignment
  RegisterAssignment-Substitution⁺ =
    substitution⁺ Γ-subst-unique Γ-subst-dec Γ-weaken-subst Γ-subst-subst

  Instantiation-Substitution⁺ : Substitution⁺ Instantiation
  Instantiation-Substitution⁺ = substitution⁺ unique dec θ-weaken-subst θ-subst-subst
    where unique : subst-uniqueᵗ Instantiation
          unique (subst-α sub-τ₁) (subst-α sub-τ₂) =
            cong α (subst-unique sub-τ₁ sub-τ₂)
          unique (subst-ρ sub-σ₁) (subst-ρ sub-σ₂) =
            cong ρ (subst-unique sub-σ₁ sub-σ₂)

          dec : subst-decᵗ Instantiation
          dec θ ι (α τ) with subst-dec θ ι τ
          ... | yes (τ' , sub-τ) = yes (α τ' , subst-α sub-τ)
          ... | no ¬sub-τ =
            no (λ { (α τ' , subst-α sub-τ) → ¬sub-τ (τ' , sub-τ) })
          dec θ ι (ρ σ) with subst-dec θ ι σ
          ... | yes (σ' , sub-σ) = yes (ρ σ' , subst-ρ sub-σ)
          ... | no ¬sub-σ =
            no (λ { (ρ σ' , subst-ρ sub-σ) → ¬sub-σ (σ' , sub-σ) })

          θ-weaken-subst : weaken-substᵗ Instantiation
          θ-weaken-subst inc pos₂≤pos₁ (subst-α sub-τ) =
            subst-α (τ-weaken-subst inc pos₂≤pos₁ sub-τ)
          θ-weaken-subst inc pos₂≤pos₁ (subst-ρ sub-σ) =
            subst-ρ (σ-weaken-subst inc pos₂≤pos₁ sub-σ)

          θ-subst-subst : subst-substᵗ Instantiation
          θ-subst-subst sub-θ (subst-α sub-τ₁) (subst-α sub-τ₁')
            with subst-subst sub-θ sub-τ₁ sub-τ₁'
          ... | τ₂ , sub-τ₂ , sub-τ₂'
            = _ , subst-α sub-τ₂ , subst-α sub-τ₂'
          θ-subst-subst sub-θ (subst-ρ sub-σ₁) (subst-ρ sub-σ₁')
            with subst-subst sub-θ sub-σ₁ sub-σ₁'
          ... | σ₂ , sub-σ₂ , sub-σ₂'
            = _ , subst-ρ sub-σ₂ , subst-ρ sub-σ₂'

  Instantiations-Substitution⁺ : Substitution⁺ Instantiations
  Instantiations-Substitution⁺ = substitution⁺ unique dec θs-weaken-subst θs-subst-subst
    where unique : subst-uniqueᵗ Instantiations
          unique [] [] = refl
          unique (sub-θ₁ ∷ sub-θs₁) (sub-θ₂ ∷ sub-θs₂)
            rewrite subst-unique sub-θ₁ sub-θ₂
                  | unique sub-θs₁ sub-θs₂ = refl

          dec : subst-decᵗ Instantiations
          dec θ ι [] = yes ([] , [])
          dec θ ι (θ₁ ∷ θs₁)
            with subst-dec θ (length θs₁ + ι) θ₁ | dec θ ι θs₁
          ... | yes (θ₂ , sub-θ) | yes (θs₂ , sub-θs) = yes (θ₂ ∷ θs₂ , sub-θ ∷ sub-θs)
          ... | no ¬sub-θ | _ = no ( λ { (._ , sub-θ ∷ sub-θs) → ¬sub-θ (_ , sub-θ) })
          ... | _ | no ¬sub-θs = no ( λ { (._ , sub-θ ∷ sub-θs) → ¬sub-θs (_ , sub-θs) })

          θs-weaken-length : ∀ pos inc (θs : Instantiations) →
                               length (weaken pos inc θs) ≡ length θs
          θs-weaken-length pos inc [] = refl
          θs-weaken-length pos inc (θ ∷ θs)
            rewrite θs-weaken-length pos inc θs = refl

          θs-subst-length : ∀ {θs₁ θs₂ : Instantiations} {θ pos} →
                              θs₁ ⟦ θ / pos ⟧≡ θs₂ →
                              length θs₁ ≡ length θs₂
          θs-subst-length [] = refl
          θs-subst-length (sub-θ ∷ sub-θs) = cong suc (θs-subst-length sub-θs)

          θs-weaken-subst : weaken-substᵗ Instantiations
          θs-weaken-subst inc pos₂≤pos₁ [] = []
          θs-weaken-subst {pos₁} {pos₂} inc pos₂≤pos₁ {v₁ = θ₁ ∷ θs₁} {v₂ = θ₂ ∷ θs₂} (sub-θ ∷ sub-θs)
            with weaken-subst inc (l+m≤l+n (length θs₁) pos₂≤pos₁) sub-θ
          ... | sub-θ'
            with begin
              length θs₁ + pos₂
            ≡⟨ θs-subst-length sub-θs ∥ (λ v → v + pos₂) ⟩
              length θs₂ + pos₂
            ∎ | begin
              (length θs₁ + pos₁) + inc
            ≡⟨ +-assoc (length θs₁) pos₁ inc ⟩
              length θs₁ + (pos₁ + inc)
            ⟨ θs-weaken-length pos₂ inc θs₁ ∥ (λ v → v + (pos₁ + inc)) ⟩≡
              length (weaken pos₂ inc θs₁) + (pos₁ + inc)
            ∎ where open Eq-Reasoning
          ... | eq₁ | eq₂
            rewrite eq₁ | eq₂
            = sub-θ' ∷ θs-weaken-subst inc pos₂≤pos₁ sub-θs

          θs-subst-subst : subst-substᵗ Instantiations
          θs-subst-subst sub-θ [] [] = [] , [] , []
          θs-subst-subst {pos₁} {pos₂} sub-θ {v₁ = θ₁ ∷ θs₁} {θ₂ ∷ θs₂} {θ₁' ∷ θs₁'} (sub-θ₁ ∷ sub-θs₁) (sub-θ₁' ∷ sub-θs₁')
            with begin
              length θs₁ + suc (pos₁ + pos₂)
            ⟨ +-assoc (length θs₁) (suc pos₁) pos₂ ⟩≡
              (length θs₁ + suc pos₁) + pos₂
            ≡⟨ +-comm (length θs₁) (suc pos₁) ∥ (λ v → v + pos₂) ⟩
              (suc pos₁ + length θs₁) + pos₂
            ≡⟨ +-comm pos₁ (length θs₁) ∥ (λ v → suc v + pos₂) ⟩
              (suc (length θs₁ + pos₁)) + pos₂
            ≡⟨ refl ⟩
              suc ((length θs₁ + pos₁) + pos₂)
            ∎ | begin
              (length θs₁ + pos₁) + pos₂
            ≡⟨ +-assoc (length θs₁) pos₁ pos₂ ⟩
              length θs₁ + (pos₁ + pos₂)
            ≡⟨ θs-subst-length sub-θs₁' ∥ (λ v → v + (pos₁ + pos₂)) ⟩
              length θs₂ + (pos₁ + pos₂)
            ∎ | begin
              length θs₁ + pos₁
            ≡⟨ θs-subst-length sub-θs₁ ∥ (λ v → v + pos₁) ⟩
              length θs₁' + pos₁
            ∎ where open Eq-Reasoning
          ... | eq₁ | eq₂ | eq₃
            rewrite eq₁
            with subst-subst sub-θ sub-θ₁ sub-θ₁'
          ... | θ₂' , sub-θ₂ , sub-θ₂'
            with θs-subst-subst sub-θ sub-θs₁ sub-θs₁'
          ... | θs₂' , sub-θs₂ , sub-θs₂'
            rewrite eq₂ | eq₃
            = θ₂' ∷ θs₂' , sub-θ₂ ∷ sub-θs₂ , sub-θ₂' ∷ sub-θs₂'

  SmallValue-Substitution⁺ : Substitution⁺ SmallValue
  SmallValue-Substitution⁺ = substitution⁺ unique dec v-weaken-subst v-subst-subst
    where unique : subst-uniqueᵗ SmallValue
          unique subst-reg subst-reg = refl
          unique subst-globval subst-globval = refl
          unique subst-int subst-int = refl
          unique (subst-Λ sub-v₁ sub-θs₁) (subst-Λ sub-v₂ sub-θs₂)
            rewrite unique sub-v₁ sub-v₂
                  | subst-unique sub-θs₁ sub-θs₂ = refl

          dec : subst-decᵗ SmallValue
          dec θ ι (reg ♯r) = yes (reg ♯r , subst-reg)
          dec θ ι (globval lab) = yes (globval lab , subst-globval)
          dec θ ι (int i) = yes (int i , subst-int)
          dec θ ι (Λ Δ ∙ v ⟦ θs ⟧)
            with dec θ ι v | subst-dec θ (length Δ + ι) θs
          ... | yes (v' , sub-v) | yes (θs' , sub-θs) = yes (Λ Δ ∙ v' ⟦ θs' ⟧ , subst-Λ sub-v sub-θs)
          ... | no ¬sub-v | _ = no (λ { (._ , subst-Λ sub-v sub-θs) → ¬sub-v (_ , sub-v) })
          ... | _ | no ¬sub-θs = no (λ { (._ , subst-Λ sub-v sub-θs) → ¬sub-θs (_ , sub-θs) })

          v-weaken-subst : weaken-substᵗ SmallValue
          v-weaken-subst inc pos₂≤pos₁ subst-reg = subst-reg
          v-weaken-subst inc pos₂≤pos₁ subst-globval = subst-globval
          v-weaken-subst inc pos₂≤pos₁ subst-int = subst-int
          v-weaken-subst {pos₁} inc pos₂≤pos₁ {v₁ = Λ Δ ∙ v ⟦ θs ⟧} (subst-Λ sub-v sub-θs)
            with weaken-subst inc (l+m≤l+n (length Δ) pos₂≤pos₁) sub-θs
          ... | sub-θs'
            rewrite +-assoc (length Δ) pos₁ inc
            = subst-Λ (v-weaken-subst inc pos₂≤pos₁ sub-v) sub-θs'

          v-subst-subst : subst-substᵗ SmallValue
          v-subst-subst sub-θ subst-reg subst-reg = _ , subst-reg , subst-reg
          v-subst-subst sub-θ subst-globval subst-globval = _ , subst-globval , subst-globval
          v-subst-subst sub-θ subst-int subst-int = _ , subst-int , subst-int
          v-subst-subst {pos₁} {pos₂} sub-θ {Λ Δ ∙ v ⟦ θs ⟧} (subst-Λ sub-v₁ sub-θs₁) (subst-Λ sub-v₁' sub-θs₁')
            with v-subst-subst sub-θ sub-v₁ sub-v₁'
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
            with subst-subst {{Instantiations-Substitution⁺}} {length Δ + pos₁} {pos₂} sub-θ sub-θs₁ sub-θs₁'
          ... | θs₂ , sub-θs₂ , sub-θs₂'
            rewrite +-assoc (length Δ) pos₁ pos₂
            = _ , subst-Λ sub-v₂ sub-θs₂ , subst-Λ sub-v₂' sub-θs₂'

  Instruction-Substitution⁺ : Substitution⁺ Instruction
  Instruction-Substitution⁺ = substitution⁺ unique dec ι-weaken-subst ι-subst-subst
    where unique : subst-uniqueᵗ Instruction
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

          dec : subst-decᵗ Instruction
          dec θ ιₚ (add ♯rd ♯rs v)
            with subst-dec θ ιₚ v
          ... | yes (v' , sub-v) = yes (add ♯rd ♯rs v' , subst-add sub-v)
          ... | no ¬sub-v =
            no (λ { (add .♯rd .♯rs v' , subst-add sub-v) →
              ¬sub-v (v' , sub-v) })
          dec θ ιₚ (sub ♯rd ♯rs v)
            with subst-dec θ ιₚ v
          ... | yes (v' , sub-v) = yes (sub ♯rd ♯rs v' , subst-sub sub-v)
          ... | no ¬sub-v =
            no (λ { (sub .♯rd .♯rs v' , subst-sub sub-v) →
              ¬sub-v (v' , sub-v) })
          dec θ ιₚ (sfree n) = yes (sfree n , subst-sfree)
          dec θ ιₚ (salloc n) = yes (salloc n , subst-salloc)
          dec θ ιₚ (sld ♯rd i) = yes (sld ♯rd i , subst-sld)
          dec θ ιₚ (sst i ♯rs) = yes (sst i ♯rs , subst-sst)
          dec θ ιₚ (ld ♯rd ♯rs i) = yes (ld ♯rd ♯rs i , subst-ld)
          dec θ ιₚ (st ♯rd i ♯rs) = yes (st ♯rd i ♯rs , subst-st)
          dec θ ιₚ (malloc ♯rd τs)
            with subst-dec θ ιₚ τs
          ... | yes (τs' , sub-τs) =
            yes (malloc ♯rd τs' , subst-malloc sub-τs)
          ... | no ¬sub-τs =
            no (λ { (malloc .♯rd τs' , subst-malloc sub-τs) →
              ¬sub-τs (τs' , sub-τs) })
          dec θ ιₚ (mov ♯rd v)
            with subst-dec θ ιₚ v
          ... | yes (v' , sub-v) = yes (mov ♯rd v' , subst-mov sub-v)
          ... | no ¬sub-v =
            no (λ { (mov .♯rd v' , subst-mov sub-v) →
              ¬sub-v (v' , sub-v) })
          dec θ ιₚ (beq ♯r v)
            with subst-dec θ ιₚ v
          ... | yes (v' , sub-v) = yes (beq ♯r v' , subst-beq sub-v)
          ... | no ¬sub-v =
            no (λ { (beq .♯r v' , subst-beq sub-v) →
              ¬sub-v (v' , sub-v) })

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

          ι-subst-subst : subst-substᵗ Instruction
          ι-subst-subst sub-θ (subst-add sub-v₁) (subst-add sub-v₁')
            with subst-subst sub-θ sub-v₁ sub-v₁'
          ... | v₂ , sub-v₂ , sub-v₂'
            = _ , subst-add sub-v₂ , subst-add sub-v₂'
          ι-subst-subst sub-θ (subst-sub sub-v₁) (subst-sub sub-v₁')
            with subst-subst sub-θ sub-v₁ sub-v₁'
          ... | v₂ , sub-v₂ , sub-v₂'
            = _ , subst-sub sub-v₂ , subst-sub sub-v₂'
          ι-subst-subst sub-θ subst-salloc subst-salloc = _ , subst-salloc , subst-salloc
          ι-subst-subst sub-θ subst-sfree subst-sfree = _ , subst-sfree , subst-sfree
          ι-subst-subst sub-θ subst-sld subst-sld = _ , subst-sld , subst-sld
          ι-subst-subst sub-θ subst-sst subst-sst = _ , subst-sst , subst-sst
          ι-subst-subst sub-θ subst-ld subst-ld = _ , subst-ld , subst-ld
          ι-subst-subst sub-θ subst-st subst-st = _ , subst-st , subst-st
          ι-subst-subst sub-θ (subst-malloc sub-τs₁) (subst-malloc sub-τs₁')
            with subst-subst sub-θ sub-τs₁ sub-τs₁'
          ... | τs₂ , sub-τs₂ , sub-τs₂'
            = _ , subst-malloc sub-τs₂ , subst-malloc sub-τs₂'
          ι-subst-subst sub-θ (subst-mov sub-v₁) (subst-mov sub-v₁')
            with subst-subst sub-θ sub-v₁ sub-v₁'
          ... | v₂ , sub-v₂ , sub-v₂'
            = _ , subst-mov sub-v₂ , subst-mov sub-v₂'
          ι-subst-subst sub-θ (subst-beq sub-v₁) (subst-beq sub-v₁')
            with subst-subst sub-θ sub-v₁ sub-v₁'
          ... | v₂ , sub-v₂ , sub-v₂'
            = _ , subst-beq sub-v₂ , subst-beq sub-v₂'

  InstructionSequence-Substitution⁺ : Substitution⁺ InstructionSequence
  InstructionSequence-Substitution⁺ = substitution⁺ unique dec I-weaken-subst I-subst-subst
    where unique : subst-uniqueᵗ InstructionSequence
          unique (subst-~> sub-ι₁ sub-I₁) (subst-~> sub-ι₂ sub-I₂)
            = cong₂ _~>_ (subst-unique sub-ι₁ sub-ι₂) (unique sub-I₁ sub-I₂)
          unique (subst-jmp sub-v₁) (subst-jmp sub-v₂)
            = cong jmp (subst-unique sub-v₁ sub-v₂)
          unique subst-halt subst-halt = refl

          dec : subst-decᵗ InstructionSequence
          dec θ ιₚ (ι ~> I)
            with subst-dec θ ιₚ ι | dec θ ιₚ I
          ... | yes (ι' , sub-ι) | yes (I' , sub-I) =
            yes (ι' ~> I' , subst-~> sub-ι sub-I)
          ... | no ¬sub-ι | _ =
            no (λ { (ι' ~> I' , subst-~> sub-ι sub-I) → ¬sub-ι (ι' , sub-ι)})
          ... | _ | no ¬sub-I =
            no (λ { (ι' ~> I' , subst-~> sub-ι sub-I) → ¬sub-I (I' , sub-I)})
          dec θ ι (jmp v)
            with subst-dec θ ι v
          ... | yes (v' , sub-v) = yes (jmp v' , subst-jmp sub-v)
          ... | no ¬sub-v =
            no (λ { (jmp v' , subst-jmp sub-v) → ¬sub-v (v' , sub-v)})
          dec θ ι halt = yes (halt , subst-halt)

          I-weaken-subst : weaken-substᵗ InstructionSequence
          I-weaken-subst inc pos₂≤pos₁ (subst-~> sub-v sub-I) = subst-~> (weaken-subst inc pos₂≤pos₁ sub-v) (I-weaken-subst inc pos₂≤pos₁ sub-I)
          I-weaken-subst inc pos₂≤pos₁ (subst-jmp sub-v) = subst-jmp (weaken-subst inc pos₂≤pos₁ sub-v)
          I-weaken-subst inc pos₂≤pos₁ subst-halt = subst-halt

          I-subst-subst : subst-substᵗ InstructionSequence
          I-subst-subst sub-θ (subst-~> sub-ι₁ sub-I₁) (subst-~> sub-ι₁' sub-I₁')
            with subst-subst sub-θ sub-ι₁ sub-ι₁'
          ... | ι₂ , sub-ι₂ , sub-ι₂'
            with I-subst-subst sub-θ sub-I₁ sub-I₁'
          ... | I₂ , sub-I₂ , sub-I₂'
            = _ , subst-~> sub-ι₂ sub-I₂ , subst-~> sub-ι₂' sub-I₂'
          I-subst-subst sub-θ (subst-jmp sub-v₁) (subst-jmp sub-v₁')
            with subst-subst sub-θ sub-v₁ sub-v₁'
          ... | v₂ , sub-v₂ , sub-v₂'
            = _ , subst-jmp sub-v₂ , subst-jmp sub-v₂'
          I-subst-subst sub-θ subst-halt subst-halt
            = halt , subst-halt , subst-halt
