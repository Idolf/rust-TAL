open import Grammar
open import Util
import Data.Nat as N
import Data.Nat.Properties as NP
import Relation.Binary as B

mutual
  substᵗ : Set → Set1
  substᵗ A = A → Cast → A → Set

  infix 5 _⟦_⟧τ≡_
  data _⟦_⟧τ≡_ : substᵗ Type where
    subst-α-< :
           ∀ {ι₁ ι₂ cᵥ} →
             ι₁ < ι₂ →
      -------------------------
      α⁼ ι₁ ⟦ cᵥ / ι₂ ⟧τ≡ α⁼ ι₁

    subst-α-inst-≡ :
               ∀ {ι τ} →
      --------------------------
      α⁼ ι  ⟦ inst α τ / ι ⟧τ≡ τ

    subst-α-inst-> :
                  ∀ {ι₁ ι₂ a i} →
                  suc ι₁ > ι₂ →
      -------------------------------------
      α⁼ (suc ι₁) ⟦ inst a i / ι₂ ⟧τ≡ α⁼ ι₁

    subst-α-weaken-≥ :
                    ∀ {ι₁ ι₂ a} →
                      ι₁ ≥ ι₂ →
      -------------------------------------
      α⁼ ι₁ ⟦ weaken a / ι₂ ⟧τ≡ α⁼ (suc ι₁)

    subst-int :
          ∀ {c} →
      ---------------
      int ⟦ c ⟧τ≡ int

    subst-ns :
         ∀ {c} →
      -------------
      ns ⟦ c ⟧τ≡ ns

    subst-∀ :
             ∀ {Δ Γ Γ' cᵥ ι} →
      Γ ⟦ cᵥ / length Δ + ι ⟧Γ≡ Γ' →
      -------------------------------
      ∀[ Δ ] Γ ⟦ cᵥ / ι ⟧τ≡ ∀[ Δ ] Γ'

    subst-tuple :
             ∀ {c m τs τs'} →
            τs ⟦ c ⟧τs⁻≡ τs' →
      ------------------------------
      tuple {m} τs ⟦ c ⟧τ≡ tuple τs'

  infix 5 _⟦_⟧τ⁻≡_
  data _⟦_⟧τ⁻≡_ : substᵗ InitType where
    subst-τ⁻ :
            ∀ {φ τ τ' c} →
            τ ⟦ c ⟧τ≡ τ' →
      -------------------------
      (τ , φ) ⟦ c ⟧τ⁻≡ (τ' , φ)

  infix 5 _⟦_⟧τs⁻≡_
  data _⟦_⟧τs⁻≡_ : ∀ {m} → substᵗ (Vec InitType m) where
    subst-[] :
          ∀ {c} →
      ---------------
      [] ⟦ c ⟧τs⁻≡ []

    subst-∷ :
            ∀ {τ τ' m c} →
      {τs τs' : Vec InitType m} →
            τ ⟦ c ⟧τ⁻≡ τ' →
           τs ⟦ c ⟧τs⁻≡ τs' →
      -------------------------
      τ ∷ τs ⟦ c ⟧τs⁻≡ τ' ∷ τs'

  infix 5 _⟦_⟧σ≡_
  data _⟦_⟧σ≡_ : substᵗ StackType where
    subst-ρ-< :
           ∀ {ι₁ ι₂ cᵥ} →
             ι₁ < ι₂ →
      -----------------------
      ρ⁼ ι₁ ⟦ cᵥ / ι₂ ⟧σ≡ ρ⁼ ι₁

    subst-ρ-inst-≡ :
               ∀ {ι σ} →
      --------------------------
      ρ⁼ ι  ⟦ inst ρ σ / ι ⟧σ≡ σ

    subst-ρ-inst-> :
                  ∀ {ι₁ ι₂ a i} →
                  suc ι₁ > ι₂ →
      -------------------------------------
      ρ⁼ (suc ι₁) ⟦ inst a i / ι₂ ⟧σ≡ ρ⁼ ι₁

    subst-ρ-weaken-≥ :
               ∀ {ι₁ ι₂ a} →
                 ι₁ ≥ ι₂ →
      -------------------------------------
      ρ⁼ ι₁ ⟦ weaken a / ι₂ ⟧σ≡ ρ⁼ (suc ι₁)

    subst-[] :
         ∀ {c} →
     ---------------
     nil ⟦ c ⟧σ≡ nil

    subst-∷ :
        ∀ {τ τ' σ σ' c} →
         τ ⟦ c ⟧τ≡ τ' →
         σ ⟦ c ⟧σ≡ σ' →
      ---------------------
      τ ∷ σ ⟦ c ⟧σ≡ τ' ∷ σ'

  infix 5 _⟦_⟧Δ≡_
  data _⟦_⟧Δ≡_ : substᵗ TypeAssignment where
    subst-inst :
               ∀ {a a' Δ iᵥ} →
      -------------------------------
      a ∷ Δ ⟦ inst a' iᵥ / zero ⟧Δ≡ Δ

    subst-weaken :
               ∀ {Δ a} →
      ---------------------------
      Δ ⟦ weaken a / zero ⟧Δ≡ a ∷ Δ

    subst-suc :
           ∀ {a a' Δ Δ' ι cᵥ} →
           a ⟦ cᵥ / ι ⟧a≡ a' →
           Δ ⟦ cᵥ / ι ⟧Δ≡ Δ' →
      ------------------------------
      a ∷ Δ ⟦ cᵥ / suc ι ⟧Δ≡ a' ∷ Δ'

  infix 5 _⟦_⟧a≡_
  data _⟦_⟧a≡_ : substᵗ TypeAssignmentValue where
    subst-α :
        ∀ {c} →
      -----------
      α ⟦ c ⟧a≡ α

    subst-ρ :
        ∀ {c} →
      -----------
      ρ ⟦ c ⟧a≡ ρ

  infix 5 _⟦_⟧Γ≡_
  data _⟦_⟧Γ≡_ : substᵗ RegisterAssignment where
    subst-registerₐ :
              ∀ {regs regs' sp sp' c} →
                  sp ⟦ c ⟧σ≡ sp' →
               regs ⟦ c ⟧regs≡ regs' →
      ---------------------------------------------
      registerₐ sp regs ⟦ c ⟧Γ≡ registerₐ sp' regs'

  infix 5 _⟦_⟧regs≡_
  data _⟦_⟧regs≡_ : ∀ {m} → substᵗ (Vec Type m) where
    subst-[] :
           ∀ {c} →
      ----------------
      [] ⟦ c ⟧regs≡ []

    subst-∷ :
            ∀ {τ τ' m c} →
        {τs τs' : Vec Type m} →
            τ ⟦ c ⟧τ≡ τ' →
          τs ⟦ c ⟧regs≡ τs' →
      --------------------------
      τ ∷ τs ⟦ c ⟧regs≡ τ' ∷ τs'

private
  mutual
    substᵗ-unique : ∀ {A} → substᵗ A → Set
    substᵗ-unique _⟦_⟧≡_ = ∀ {v v₁ v₂ c} →
                             v ⟦ c ⟧≡ v₁ →
                             v ⟦ c ⟧≡ v₂ →
                             v₁ ≡ v₂

    subst-τ-unique : substᵗ-unique _⟦_⟧τ≡_
    subst-τ-unique (subst-α-< ι₁<ι₂) (subst-α-< ι₁<ι₂') = refl
    subst-τ-unique (subst-α-< ι<ι) subst-α-inst-≡
      with NP.1+n≰n ι<ι
    ... | ()
    subst-τ-unique (subst-α-< ι₁<ι₂) (subst-α-inst-> ι₁>ι₂)
      with NP.1+n≰n (NP.<-trans ι₁<ι₂ ι₁>ι₂)
    ... | ()
    subst-τ-unique (subst-α-< (s≤s ι₁≤sucι₂)) (subst-α-weaken-≥ ι₁≥sucι₂)
      with NP.1+n≰n (Nat-≤-trans  ι₁≥sucι₂ ι₁≤sucι₂)
    ... | ()
    subst-τ-unique subst-α-inst-≡ (subst-α-< ι<ι)
      with NP.1+n≰n ι<ι
    ... | ()
    subst-τ-unique subst-α-inst-≡ subst-α-inst-≡ = refl
    subst-τ-unique subst-α-inst-≡ (subst-α-inst-> ι>ι)
      with NP.1+n≰n ι>ι
    ... | ()
    subst-τ-unique (subst-α-inst-> ι₁>ι₂) (subst-α-< ι₁<ι₂)
      with NP.1+n≰n (NP.<-trans ι₁<ι₂ ι₁>ι₂)
    ... | ()
    subst-τ-unique (subst-α-inst-> ι>ι) subst-α-inst-≡
      with NP.1+n≰n ι>ι
    ... | ()
    subst-τ-unique (subst-α-inst-> ι₁>ι₂) (subst-α-inst-> ι₁>ι₂') = refl
    subst-τ-unique (subst-α-weaken-≥ ι₁≥sucι₂) (subst-α-< (s≤s ι₁≤sucι₂))
      with NP.1+n≰n (Nat-≤-trans  ι₁≥sucι₂ ι₁≤sucι₂)
    ... | ()
    subst-τ-unique (subst-α-weaken-≥ ι₁≥ι₂) (subst-α-weaken-≥ ι₁≥ι₂') = refl
    subst-τ-unique subst-int subst-int = refl
    subst-τ-unique subst-ns subst-ns = refl
    subst-τ-unique (subst-∀ {Δ = Δ} sub-Γ₁) (subst-∀ sub-Γ₂) =
      cong (∀[_]_ Δ) (subst-Γ-unique sub-Γ₁ sub-Γ₂)
    subst-τ-unique (subst-tuple sub-τs₁) (subst-tuple sub-τs₂) =
      cong tuple (subst-τs⁻-unique sub-τs₁ sub-τs₂)

    subst-τ⁻-unique : substᵗ-unique _⟦_⟧τ⁻≡_
    subst-τ⁻-unique (subst-τ⁻ {φ = φ} sub-τ₁) (subst-τ⁻ sub-τ₂) =
      cong₂ _,_ (subst-τ-unique sub-τ₁ sub-τ₂) refl

    subst-τs⁻-unique : ∀ {m} → substᵗ-unique (_⟦_⟧τs⁻≡_ {m})
    subst-τs⁻-unique subst-[] subst-[] = refl
    subst-τs⁻-unique (subst-∷ sub-τ₁ sub-τs₁) (subst-∷ sub-τ₂ sub-τs₂) =
      cong₂ _∷_ (subst-τ⁻-unique sub-τ₁ sub-τ₂)
                (subst-τs⁻-unique sub-τs₁ sub-τs₂)

    subst-σ-unique : substᵗ-unique _⟦_⟧σ≡_
    subst-σ-unique (subst-ρ-< ι₁<ι₂) (subst-ρ-< ι₁<ι₂') = refl
    subst-σ-unique (subst-ρ-< ι<ι) subst-ρ-inst-≡
      with NP.1+n≰n ι<ι
    ... | ()
    subst-σ-unique (subst-ρ-< ι₁<ι₂) (subst-ρ-inst-> ι₁>ι₂)
      with NP.1+n≰n (NP.<-trans ι₁<ι₂ ι₁>ι₂)
    ... | ()
    subst-σ-unique (subst-ρ-< (s≤s ι₁≤sucι₂)) (subst-ρ-weaken-≥ ι₁≥sucι₂)
      with NP.1+n≰n (Nat-≤-trans  ι₁≥sucι₂ ι₁≤sucι₂)
    ... | ()
    subst-σ-unique subst-ρ-inst-≡ (subst-ρ-< ι<ι)
      with NP.1+n≰n ι<ι
    ... | ()
    subst-σ-unique subst-ρ-inst-≡ subst-ρ-inst-≡ = refl
    subst-σ-unique subst-ρ-inst-≡ (subst-ρ-inst-> ι>ι)
      with NP.1+n≰n ι>ι
    ... | ()
    subst-σ-unique (subst-ρ-inst-> ι₁>ι₂) (subst-ρ-< ι₁<ι₂)
      with NP.1+n≰n (NP.<-trans ι₁<ι₂ ι₁>ι₂)
    ... | ()
    subst-σ-unique (subst-ρ-inst-> ι>ι) subst-ρ-inst-≡
      with NP.1+n≰n ι>ι
    ... | ()
    subst-σ-unique (subst-ρ-inst-> ι₁>ι₂) (subst-ρ-inst-> ι₁>ι₂') = refl
    subst-σ-unique (subst-ρ-weaken-≥ ι₁≥sucι₂) (subst-ρ-< (s≤s ι₁≤sucι₂))
      with NP.1+n≰n (Nat-≤-trans  ι₁≥sucι₂ ι₁≤sucι₂)
    ... | ()
    subst-σ-unique (subst-ρ-weaken-≥ ι₁≥ι₂) (subst-ρ-weaken-≥ ι₁≥ι₂') = refl
    subst-σ-unique subst-[] subst-[] = refl
    subst-σ-unique (subst-∷ sub-τ₁ sub-σ₁) (subst-∷ sub-τ₂ sub-σ₂) =
      cong₂ _∷_ (subst-τ-unique sub-τ₁ sub-τ₂) (subst-σ-unique sub-σ₁ sub-σ₂)

    subst-Δ-unique : substᵗ-unique _⟦_⟧Δ≡_
    subst-Δ-unique subst-inst subst-inst = refl
    subst-Δ-unique subst-weaken subst-weaken = refl
    subst-Δ-unique (subst-suc sub-a₁ sub-Δ₁) (subst-suc sub-a₂ sub-Δ₂) =
      cong₂ _∷_ (subst-a-unique sub-a₁ sub-a₂) (subst-Δ-unique sub-Δ₁ sub-Δ₂)

    subst-a-unique : substᵗ-unique _⟦_⟧a≡_
    subst-a-unique subst-α subst-α = refl
    subst-a-unique subst-ρ subst-ρ = refl

    subst-Γ-unique : substᵗ-unique _⟦_⟧Γ≡_
    subst-Γ-unique (subst-registerₐ sub-sp₁ sub-regs₁)
                   (subst-registerₐ sub-sp₂ sub-regs₂) =
      cong₂ registerₐ (subst-σ-unique sub-sp₁ sub-sp₂)
                      (subst-regs-unique sub-regs₁ sub-regs₂)

    subst-regs-unique : ∀ {m} → substᵗ-unique (_⟦_⟧regs≡_ {m})
    subst-regs-unique subst-[] subst-[] = refl
    subst-regs-unique (subst-∷ sub-τ₁ sub-τs₁) (subst-∷ sub-τ₂ sub-τs₂) =
      cong₂ _∷_ (subst-τ-unique sub-τ₁ sub-τ₂)
                (subst-regs-unique sub-τs₁ sub-τs₂)

  mutual
    _⟦_⟧τ? : ∀ τ c → Dec (∃ λ τ' → τ ⟦ c ⟧τ≡ τ')
    α⁼ ι₁ ⟦ cᵥ / ι₂ ⟧τ? with Nat-cmp ι₁ ι₂
    α⁼ ι₁ ⟦ cᵥ / ι₂ ⟧τ? | tri< ι₁<ι₂ _ _ = yes (α⁼ ι₁ , subst-α-< ι₁<ι₂)
    α⁼ ι  ⟦ inst α τ / .ι ⟧τ? | tri≈ _ refl _ = yes (τ , subst-α-inst-≡)
    α⁼ ι  ⟦ inst ρ σ / .ι ⟧τ? | tri≈ _ refl _ = no help
      where help : ∀ {ι σ} → ¬ (∃ λ τ' → α⁼ ι ⟦ inst ρ σ / ι ⟧τ≡ τ')
            help (._ , subst-α-< ι<ι) = NP.1+n≰n ι<ι
            help (._ , subst-α-inst-> ι>ι) = NP.1+n≰n ι>ι
    α⁼ ι  ⟦ weaken a / .ι ⟧τ? | tri≈ _ refl _ =
      yes (α⁼ (suc ι) , subst-α-weaken-≥ (Nat-≤-refl ι))
    α⁼ zero ⟦ inst a i / ι₂ ⟧τ? | tri> _ _ ()
    α⁼ (suc ι₁) ⟦ inst a x / ι₂ ⟧τ? | tri> _ _ sucι₁>ι₂ =
      yes (α⁼ ι₁ , subst-α-inst-> sucι₁>ι₂)
    α⁼ ι₁ ⟦ weaken x / ι₂ ⟧τ? | tri> _ _ ι₁>ι₂ =
      yes (α⁼ (suc ι₁) , subst-α-weaken-≥ (NP.≤⇒pred≤ _ _ ι₁>ι₂))
    int ⟦ c ⟧τ? = yes (int , subst-int)
    ns ⟦ c ⟧τ? = yes (ns , subst-ns)
    (∀[ Δ ] Γ) ⟦ cᵥ / ι ⟧τ? with Γ ⟦ cᵥ / length Δ + ι ⟧Γ?
    (∀[ Δ ] Γ) ⟦ cᵥ / ι ⟧τ? | yes (Γ' , sub-Γ) =
      yes (∀[ Δ ] Γ' , subst-∀ sub-Γ)
    (∀[ Δ ] Γ) ⟦ cᵥ / ι ⟧τ? | no ¬sub-Γ =
      no (λ { (._ , subst-∀ sub-Γ) → ¬sub-Γ (_ , sub-Γ) })
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

    _⟦_⟧τs⁻? : ∀ {m} (τs⁻ : Vec InitType m) c →
                     Dec (∃ λ τs⁻' → τs⁻ ⟦ c ⟧τs⁻≡ τs⁻')
    [] ⟦ c ⟧τs⁻? = yes ([] , subst-[])
    (τ⁻ ∷ τs⁻) ⟦ c ⟧τs⁻? with τ⁻ ⟦ c ⟧τ⁻? | τs⁻ ⟦ c ⟧τs⁻?
    ... | yes (τ⁻' , sub-τ⁻) | yes (τs⁻' , sub-τs⁻) =
      yes (τ⁻' ∷ τs⁻' , subst-∷ sub-τ⁻ sub-τs⁻)
    ... | no ¬sub-τ⁻ | _ =
      no (λ { (._ , subst-∷ sub-τ⁻ sub-τs⁻) → ¬sub-τ⁻ (_ , sub-τ⁻) })
    ... | _ | no ¬sub-τs⁻ =
      no (λ { (._ , subst-∷ sub-τ⁻ sub-τs⁻) → ¬sub-τs⁻ (_ , sub-τs⁻) })

    _⟦_⟧σ? : ∀ σ c → Dec (∃ λ σ' → σ ⟦ c ⟧σ≡ σ')
    ρ⁼ ι₁ ⟦ cᵥ / ι₂ ⟧σ? with Nat-cmp ι₁ ι₂
    ρ⁼ ι₁ ⟦ cᵥ / ι₂ ⟧σ? | tri< ι₁<ι₂ _ _ = yes (ρ⁼ ι₁ , subst-ρ-< ι₁<ι₂)
    ρ⁼ ι  ⟦ inst ρ σ / .ι ⟧σ? | tri≈ _ refl _ = yes (σ , subst-ρ-inst-≡)
    ρ⁼ ι  ⟦ inst α τ / .ι ⟧σ? | tri≈ _ refl _ = no help
      where help : ∀ {ι τ} → ¬ (∃ λ σ' → ρ⁼ ι ⟦ inst α τ / ι ⟧σ≡ σ')
            help (._ , subst-ρ-< ι<ι) = NP.1+n≰n ι<ι
            help (._ , subst-ρ-inst-> ι>ι) = NP.1+n≰n ι>ι
    ρ⁼ ι  ⟦ weaken a / .ι ⟧σ? | tri≈ _ refl _ =
      yes (ρ⁼ (suc ι) , subst-ρ-weaken-≥ (Nat-≤-refl ι))
    ρ⁼ zero ⟦ inst a i / ι₂ ⟧σ? | tri> _ _ ()
    ρ⁼ (suc ι₁) ⟦ inst a x / ι₂ ⟧σ? | tri> _ _ sucι₁>ι₂ =
      yes (ρ⁼ ι₁ , subst-ρ-inst-> sucι₁>ι₂)
    ρ⁼ ι₁ ⟦ weaken x / ι₂ ⟧σ? | tri> _ _ ι₁>ι₂ =
      yes (ρ⁼ (suc ι₁) , subst-ρ-weaken-≥ (NP.≤⇒pred≤ _ _ ι₁>ι₂))
    nil ⟦ c ⟧σ? = yes (nil , subst-[])
    (τ ∷ σ) ⟦ c ⟧σ? with τ ⟦ c ⟧τ? | σ ⟦ c ⟧σ?
    ... | yes (τ' , sub-τ) | yes (σ' , sub-σ) =
      yes (τ' ∷ σ' , subst-∷ sub-τ sub-σ)
    ... | no ¬sub-τ | _ =
      no (λ { (._ , subst-∷ sub-τ sub-σ) → ¬sub-τ (_ , sub-τ) })
    ... | _ | no ¬sub-σ =
      no (λ { (._ , subst-∷ sub-τ sub-σ) → ¬sub-σ (_ , sub-σ) })

    _⟦_⟧Δ? : ∀ Δ c → Dec (∃ λ Δ' → Δ ⟦ c ⟧Δ≡ Δ')
    [] ⟦ inst a i / ι ⟧Δ? = no (λ { (_ , ()) })
    [] ⟦ weaken a / zero ⟧Δ? = yes (a ∷ [] , subst-weaken)
    [] ⟦ weaken a / suc ι ⟧Δ? = no (λ { (_ , ()) })
    (a ∷ Δ) ⟦ inst a' iᵥ  / zero ⟧Δ? = yes (Δ , subst-inst)
    (a ∷ Δ) ⟦ weaken a' / zero ⟧Δ? = yes (a' ∷ a ∷ Δ , subst-weaken)
    (a ∷ Δ) ⟦ cᵥ / suc ι ⟧Δ? with a ⟦ cᵥ / ι ⟧a? | Δ ⟦ cᵥ / ι ⟧Δ?
    ... | yes (a' , sub-a) | yes (Δ' , sub-Δ) =
      yes (a' ∷ Δ' , subst-suc sub-a sub-Δ)
    ... | no ¬sub-a | _ =
      no (λ { (._ , subst-suc sub-a sub-Δ) → ¬sub-a (_ , sub-a) })
    ... | _ | no ¬sub-Δ =
      no (λ { (._ , subst-suc sub-a sub-Δ) → ¬sub-Δ (_ , sub-Δ) })

    _⟦_⟧a? : ∀ a c → Dec (∃ λ a' → a ⟦ c ⟧a≡ a')
    α ⟦ c ⟧a? = yes (α , subst-α)
    ρ ⟦ c ⟧a? = yes (ρ , subst-ρ)

    _⟦_⟧Γ? : ∀ Γ c → Dec (∃ λ Γ' → Γ ⟦ c ⟧Γ≡ Γ')
    registerₐ sp regs ⟦ c ⟧Γ? with sp ⟦ c ⟧σ? | regs ⟦ c ⟧regs?
    ... | yes (sp' , sub-sp) | yes (regs' , sub-regs) =
      yes (registerₐ sp' regs' , subst-registerₐ sub-sp sub-regs)
    ... | no ¬sub-sp | _ =
      no (λ { (._ , subst-registerₐ sub-sp sub-regs) → ¬sub-sp (_ , sub-sp) })
    ... | _ | no ¬sub-regs = no
      (λ {(._ , subst-registerₐ sub-sp sub-regs) → ¬sub-regs (_ , sub-regs) })

    _⟦_⟧regs? : ∀ {m} (regs : Vec Type m) c →
                  Dec (∃ λ regs' → regs ⟦ c ⟧regs≡ regs')
    [] ⟦ c ⟧regs? = yes ([] , subst-[])
    (τ ∷ τs) ⟦ c ⟧regs? with τ ⟦ c ⟧τ? | τs ⟦ c ⟧regs?
    ... | yes (τ' , sub-τ) | yes (τs' , sub-τs) =
      yes (τ' ∷ τs' , subst-∷ sub-τ sub-τs)
    ... | no ¬sub-τ | _ =
      no (λ { (._ , subst-∷ sub-τ sub-τs) → ¬sub-τ (_ , sub-τ) })
    ... | _ | no ¬sub-τs =
      no (λ { (._ , subst-∷ sub-τ sub-τs) → ¬sub-τs (_ , sub-τs) })

  mutual
    can-weaken-τ : ∀ ι τ a → ∃ λ τ' → τ ⟦ weaken a / ι ⟧τ≡ τ'
    can-weaken-τ ι₁ (α⁼ ι₂) a with ι₁ ≤? ι₂
    ... | yes ι₁≤ι₂ = α⁼ (suc ι₂) , subst-α-weaken-≥ ι₁≤ι₂
    ... | no ι₁≰ι₂ = α⁼ ι₂ , subst-α-< (NP.≰⇒> ι₁≰ι₂)
    can-weaken-τ ι int a = int , subst-int
    can-weaken-τ ι ns a = ns , subst-ns
    can-weaken-τ ι (∀[ Δ ] Γ) a with can-weaken-Γ (length Δ + ι) Γ a
    ... | Γ' , sub-Γ = ∀[ Δ ] Γ' , subst-∀ sub-Γ
    can-weaken-τ ι (tuple τs) a with can-weaken-τs⁻ ι τs a
    ... | τs' , sub-τs = tuple τs' , subst-tuple sub-τs

    can-weaken-τ⁻ : ∀ ι τ⁻ a → ∃ λ τ⁻' → τ⁻ ⟦ weaken a / ι ⟧τ⁻≡ τ⁻'
    can-weaken-τ⁻ ι (τ , φ) a with can-weaken-τ ι τ a
    ... | τ' , sub-τ = (τ' , φ) , subst-τ⁻ sub-τ

    can-weaken-τs⁻ : ∀ ι {m} (τs⁻ : Vec InitType m) a →
                       ∃ λ τs⁻' → τs⁻ ⟦ weaken a / ι ⟧τs⁻≡ τs⁻'
    can-weaken-τs⁻ ι [] a = [] , subst-[]
    can-weaken-τs⁻ ι (τ⁻ ∷ τs⁻) a
      with can-weaken-τ⁻ ι τ⁻ a | can-weaken-τs⁻ ι τs⁻ a
    ... | τ⁻' , sub-τ⁻ | τs⁻' , sub-τs⁻ = τ⁻' ∷ τs⁻' , subst-∷ sub-τ⁻ sub-τs⁻

    can-weaken-σ : ∀ ι σ a → ∃ λ σ' → σ ⟦ weaken a / ι ⟧σ≡ σ'
    can-weaken-σ ι₁ (ρ⁼ ι₂) a with ι₁ ≤? ι₂
    ... | yes ι₁≤ι₂ = ρ⁼ (suc ι₂) , subst-ρ-weaken-≥ ι₁≤ι₂
    ... | no ι₁≰ι₂ = ρ⁼ ι₂ , subst-ρ-< (NP.≰⇒> ι₁≰ι₂)
    can-weaken-σ ι nil a = nil , subst-[]
    can-weaken-σ ι (τ ∷ σ) a with can-weaken-τ ι τ a | can-weaken-σ ι σ a
    ... | τ' , sub-τ | σ' , sub-σ = τ' ∷ σ' , subst-∷ sub-τ sub-σ

    can-weaken₁-Δ : ∀ Δ a → ∃ λ Δ' → Δ ⟦ weaken a / zero ⟧Δ≡ Δ'
    can-weaken₁-Δ Δ a = a ∷ Δ , subst-weaken

    can-weaken-a : ∀ ι a aᵥ → ∃ λ a' → a ⟦ weaken aᵥ / ι ⟧a≡ a'
    can-weaken-a ι α aᵥ = α , subst-α
    can-weaken-a ι ρ aᵥ = ρ , subst-ρ

    can-weaken-Γ : ∀ ι Γ a → ∃ λ Γ' → Γ ⟦ weaken a / ι ⟧Γ≡ Γ'
    can-weaken-Γ ι (registerₐ sp regs) a
      with can-weaken-σ ι sp a | can-weaken-regs ι regs a
    ... | sp' , sub-sp | regs' , sub-regs =
          registerₐ sp' regs' , subst-registerₐ sub-sp sub-regs

    can-weaken-regs : ∀ ι {m} (regs : Vec Type m) a →
                        ∃ λ regs' → regs ⟦ weaken a / ι ⟧regs≡ regs'
    can-weaken-regs ι [] a = [] , subst-[]
    can-weaken-regs ι (τ ∷ τs) a
      with can-weaken-τ ι τ a | can-weaken-regs ι τs a
    ... | τ' , sub-τ | τs' , sub-τs = τ' ∷ τs' , subst-∷ sub-τ sub-τs

record Substitution (A : Set) : Set1 where
  constructor substitution
  field
    _⟦_⟧≡_ : A → Cast → A → Set
    subst-unique : ∀ {v v₁ v₂ c} → v ⟦ c ⟧≡ v₁ →
                                   v ⟦ c ⟧≡ v₂ →
                                   v₁ ≡ v₂
    _⟦_⟧? : ∀ v c → Dec (∃ λ v' → v ⟦ c ⟧≡ v')
    can-weaken₁ : ∀ v a → ∃ λ v' → v ⟦ weaken a / zero ⟧≡ v'

-- These two should do the same, but they do not
-- open Substitution {{...}} public
infix 5 _⟦_⟧≡_ _⟦_⟧?
_⟦_⟧≡_ : ∀ {A} {{_ : Substitution A}} →
           A → Cast → A → Set
_⟦_⟧≡_ {{s}} = Substitution._⟦_⟧≡_ s
subst-unique : ∀ {A} {{_ : Substitution A}} →
                 ∀ {v v₁ v₂ : A} {c} → v ⟦ c ⟧≡ v₁ →
                                       v ⟦ c ⟧≡ v₂ →
                                       v₁ ≡ v₂
subst-unique {{s}} = Substitution.subst-unique s
_⟦_⟧? : ∀ {A} {{_ : Substitution A}} →
          ∀ (v : A) c → Dec (∃ λ v' → v ⟦ c ⟧≡ v')
_⟦_⟧? {{s}} = Substitution._⟦_⟧? s
can-weaken₁ : ∀ {A} {{_ : Substitution A}} →
                ∀ v a → ∃ λ v' → v ⟦ weaken a / zero ⟧≡ v'
can-weaken₁ {{s}} = Substitution.can-weaken₁ s

data weakenMany {A : Set} {{s : Substitution A}} :
     A → List TypeAssignmentValue → A → Set where
  weakenMany-[] : ∀ {v} → weakenMany v [] v
  weakenMany-∷  : ∀ {v₁ v₂ v₃ : A} {a as} →
                    weakenMany v₁ as v₂ →
                    v₂ ⟦ weaken a / zero ⟧≡ v₃ →
                    weakenMany v₁ (a ∷ as) v₃

can-weakenMany : ∀ {A} {{s : Substitution A}} v₁ Δ →
                   ∃ λ v₂ → weakenMany v₁ Δ v₂
can-weakenMany v₁ [] = v₁ , weakenMany-[]
can-weakenMany v₁ (a ∷ Δ) with can-weakenMany v₁ Δ
... | v₂ , sub-Δ with can-weaken₁ v₂ a
... | v₃ , sub-a = v₃ , weakenMany-∷ sub-Δ sub-a

instance
  Type-substitution : Substitution Type
  Type-substitution =
    substitution _⟦_⟧τ≡_ subst-τ-unique _⟦_⟧τ? (can-weaken-τ zero)

  InitType-substitution : Substitution InitType
  InitType-substitution =
    substitution _⟦_⟧τ⁻≡_ subst-τ⁻-unique _⟦_⟧τ⁻? (can-weaken-τ⁻ zero)

  StackType-substitution : Substitution StackType
  StackType-substitution =
    substitution _⟦_⟧σ≡_ subst-σ-unique _⟦_⟧σ? (can-weaken-σ zero)

  TypeAssignment-substitution : Substitution TypeAssignment
  TypeAssignment-substitution =
    substitution _⟦_⟧Δ≡_ subst-Δ-unique _⟦_⟧Δ? can-weaken₁-Δ

  TypeAssignmentValue-substitution : Substitution TypeAssignmentValue
  TypeAssignmentValue-substitution =
    substitution _⟦_⟧a≡_ subst-a-unique _⟦_⟧a? (can-weaken-a zero)

  RegisterAssignment-substitution : Substitution RegisterAssignment
  RegisterAssignment-substitution =
    substitution _⟦_⟧Γ≡_ subst-Γ-unique _⟦_⟧Γ? (can-weaken-Γ zero)

  Vec-substitution : ∀ {A} {m} {{s : Substitution A}} → Substitution (Vec A m)
  Vec-substitution = substitution
      _⟦_⟧xs≡_
      unique
      dec
      weaken₁

    where _⟦_⟧xs≡_ : ∀ {A} {{s : Substitution A}} {m} →
                       Vec A m → Cast → Vec A m → Set
          xs ⟦ c ⟧xs≡ xs' =
            Allᵥ (λ { (x , x') → x ⟦ c ⟧≡ x' }) (Vec-zip xs xs')

          unique : ∀ {A c m} {xs xs₁ xs₂ : Vec A m}
                     {{s : Substitution A}} →
                     xs ⟦ c ⟧xs≡ xs₁ →
                     xs ⟦ c ⟧xs≡ xs₂ →
                     xs₁ ≡ xs₂
          unique {xs = []} {[]} {[]} [] [] = refl
          unique {xs = x ∷ xs} {x₁ ∷ xs₁} {x₂ ∷ xs₂} {{s}}
                 (sub-x₁ ∷ sub-xs₁) (sub-x₂ ∷ sub-xs₂) =
            cong₂ _∷_ (subst-unique sub-x₁ sub-x₂) (unique sub-xs₁ sub-xs₂)

          dec : ∀ {A m} {{s : Substitution A}} (xs : Vec A m) c →
                  Dec (∃ λ xs' → xs ⟦ c ⟧xs≡ xs')
          dec [] c = yes ([] , [])
          dec (x ∷ xs) c with x ⟦ c ⟧? | dec xs c
          dec (x ∷ xs) c | yes (x' , sub-x) | yes (xs' , sub-xs) =
            yes ((x' ∷ xs') , sub-x ∷ sub-xs)
          dec (x ∷ xs) c | no ¬sub-x | _ = no (help ¬sub-x)
            where help : ∀ {A} {{s : Substitution A}}
                           {c m x} {xs : Vec A m} →
                           ¬ (∃ λ x' → x ⟦ c ⟧≡ x') →
                           ¬ (∃ λ xs' → (x ∷ xs) ⟦ c ⟧xs≡ xs')
                  help ¬sub-x (x' ∷ xs' , sub-x ∷ sub-xs) = ¬sub-x (_ , sub-x)
          dec (x ∷ xs) c | _ | no ¬sub-xs = no (help ¬sub-xs)
            where help : ∀ {A} {{s : Substitution A}}
                           {c m x} {xs : Vec A m} →
                           ¬ (∃ λ xs' → xs ⟦ c ⟧xs≡ xs') →
                           ¬ (∃ λ xs' → (x ∷ xs) ⟦ c ⟧xs≡ xs')
                  help ¬sub-xs (x' ∷ xs' , sub-x ∷ sub-xs) =
                    ¬sub-xs (_ , sub-xs)

          weaken₁ : ∀ {A m} {{s : Substitution A}} (xs : Vec A m) a →
                      ∃ λ xs' → xs ⟦ weaken a / zero ⟧xs≡ xs'
          weaken₁ [] a = [] , []
          weaken₁ (x ∷ xs) a with can-weaken₁ x a | weaken₁ xs a
          ... | x' , sub-x | xs' , sub-xs = x' ∷ xs' , sub-x ∷ sub-xs

  List-substitution : ∀ {A} {{s : Substitution A}} → Substitution (List A)
  List-substitution = substitution
      _⟦_⟧xs≡_
      unique
      dec
      weaken₁

    where _⟦_⟧xs≡_ : ∀ {A} {{s : Substitution A}} →
                         List A → Cast → List A → Set
          xs ⟦ c ⟧xs≡ xs' = length xs ≡ length xs' ×
                            All (λ { (x , x') → x ⟦ c ⟧≡ x' }) (zip xs xs')

          unique : ∀ {A c} {xs xs₁ xs₂ : List A}
                     {{s : Substitution A}} →
                     xs ⟦ c ⟧xs≡ xs₁ →
                     xs ⟦ c ⟧xs≡ xs₂ →
                     xs₁ ≡ xs₂
          unique {xs = []} {[]} {[]} (refl , []) (refl , []) = refl
          unique {xs = []} {_} {_ ∷ _} _ (() , _)
          unique {xs = []} {_ ∷ _} {_} (() , _) _
          unique {xs = x ∷ xs} {[]} {_} (() , _) _
          unique {xs = x ∷ xs} {_} {[]} _ (() , _)
          unique {xs = x ∷ xs} {x₁ ∷ xs₁} {x₂ ∷ xs₂}
                 (eq₁ , sub-x₁ ∷ sub-xs₁) (eq₂ , sub-x₂ ∷ sub-xs₂)
            = cong₂ _∷_ (subst-unique sub-x₁ sub-x₂)
                        (unique (NP.cancel-+-left 1 eq₁ , sub-xs₁)
                                (NP.cancel-+-left 1 eq₂ , sub-xs₂))

          dec : ∀ {A} {{s : Substitution A}} (xs : List A) c →
                  Dec (∃ λ xs' → xs ⟦ c ⟧xs≡ xs')
          dec [] c = yes ([] , (refl , []))
          dec (x ∷ xs) c with x ⟦ c ⟧? | dec xs c
          dec (x ∷ xs) c | yes (x' , sub-x) | yes (xs' , (eq , sub-xs)) =
            yes (x' ∷ xs' , (cong suc eq) , sub-x ∷ sub-xs)
          dec (x ∷ xs) c | no ¬sub-x | _ = no (help ¬sub-x)
            where help : ∀ {A} {{s : Substitution A}}
                           {c x} {xs : List A} →
                           ¬ (∃ λ x' → x ⟦ c ⟧≡ x') →
                           ¬ (∃ λ xs' → (x ∷ xs) ⟦ c ⟧xs≡ xs')
                  help ¬sub-x ([] , () , _)
                  help ¬sub-x (x' ∷ xs' , (eq , sub-x ∷ sub-xs)) =
                    ¬sub-x (x' , sub-x)
          dec (x ∷ xs) c | _ | no ¬sub-xs = no (help ¬sub-xs)
            where help : ∀ {A} {{s : Substitution A}}
                           {c x} {xs : List A} →
                           ¬ (∃ λ xs' → xs ⟦ c ⟧xs≡ xs') →
                           ¬ (∃ λ xs' → (x ∷ xs) ⟦ c ⟧xs≡ xs')
                  help ¬sub-xs ([] , () , _)
                  help ¬sub-xs (x' ∷ xs' , eq , sub-x ∷ sub-xs) =
                    ¬sub-xs (xs' , (NP.cancel-+-left 1 eq) , sub-xs)

          weaken₁ : ∀ {A} {{s : Substitution A}} (xs : List A) a →
                      ∃ λ xs' → xs ⟦ weaken a / zero ⟧xs≡ xs'
          weaken₁ [] a = [] , refl , []
          weaken₁ (x ∷ xs) a with can-weaken₁ x a | weaken₁ xs a
          ... | x' , sub-x | xs' , eq , sub-xs =
            x' ∷ xs' , (cong suc eq) , (sub-x ∷ sub-xs)
