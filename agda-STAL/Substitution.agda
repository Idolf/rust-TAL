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
            ∀ {ι τ τ'} →
       τ ⟦ weaken ι / zero ⟧τ≡ τ' →
      ---------------------------
      α⁼ ι  ⟦ inst α τ / ι ⟧τ≡ τ'

    subst-α-inst-> :
                  ∀ {ι₁ ι₂ a i} →
                  suc ι₁ > ι₂ →
      -------------------------------------
      α⁼ (suc ι₁) ⟦ inst a i / ι₂ ⟧τ≡ α⁼ ι₁

    subst-α-weaken-≥ :
                    ∀ {ι₁ ι₂ n} →
                      ι₁ ≥ ι₂ →
      -------------------------------------
      α⁼ ι₁ ⟦ weaken n / ι₂ ⟧τ≡ α⁼ (n + ι₁)

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
               ∀ {ι σ σ'} →
      σ ⟦ weaken ι / zero ⟧σ≡ σ' →
      ----------------------------
      ρ⁼ ι  ⟦ inst ρ σ / ι ⟧σ≡ σ'

    subst-ρ-inst-> :
                  ∀ {ι₁ ι₂ a i} →
                  suc ι₁ > ι₂ →
      -------------------------------------
      ρ⁼ (suc ι₁) ⟦ inst a i / ι₂ ⟧σ≡ ρ⁼ ι₁

    subst-ρ-weaken-≥ :
               ∀ {ι₁ ι₂ n} →
                 ι₁ ≥ ι₂ →
      -------------------------------------
      ρ⁼ ι₁ ⟦ weaken n / ι₂ ⟧σ≡ ρ⁼ (n + ι₁)

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
    subst-τ-unique (subst-α-< ι<ι) (subst-α-inst-≡ sub-τ)
      with NP.1+n≰n ι<ι
    ... | ()
    subst-τ-unique (subst-α-< ι₁<ι₂) (subst-α-inst-> ι₁>ι₂)
      with NP.1+n≰n (NP.<-trans ι₁<ι₂ ι₁>ι₂)
    ... | ()
    subst-τ-unique (subst-α-< (s≤s ι₁≤sucι₂)) (subst-α-weaken-≥ ι₁≥sucι₂)
      with NP.1+n≰n (Nat-≤-trans  ι₁≥sucι₂ ι₁≤sucι₂)
    ... | ()
    subst-τ-unique (subst-α-inst-≡ sub-τ) (subst-α-< ι<ι)
      with NP.1+n≰n ι<ι
    ... | ()
    subst-τ-unique (subst-α-inst-≡ sub-τ) (subst-α-inst-≡ sub-τ') = subst-τ-unique sub-τ sub-τ'
    subst-τ-unique (subst-α-inst-≡ sub-τ) (subst-α-inst-> ι>ι)
      with NP.1+n≰n ι>ι
    ... | ()
    subst-τ-unique (subst-α-inst-> ι₁>ι₂) (subst-α-< ι₁<ι₂)
      with NP.1+n≰n (NP.<-trans ι₁<ι₂ ι₁>ι₂)
    ... | ()
    subst-τ-unique (subst-α-inst-> ι>ι) (subst-α-inst-≡ sub-τ)
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
    subst-σ-unique (subst-ρ-< ι<ι) (subst-ρ-inst-≡ sub-σ)
      with NP.1+n≰n ι<ι
    ... | ()
    subst-σ-unique (subst-ρ-< ι₁<ι₂) (subst-ρ-inst-> ι₁>ι₂)
      with NP.1+n≰n (NP.<-trans ι₁<ι₂ ι₁>ι₂)
    ... | ()
    subst-σ-unique (subst-ρ-< (s≤s ι₁≤sucι₂)) (subst-ρ-weaken-≥ ι₁≥sucι₂)
      with NP.1+n≰n (Nat-≤-trans  ι₁≥sucι₂ ι₁≤sucι₂)
    ... | ()
    subst-σ-unique (subst-ρ-inst-≡ sub-σ) (subst-ρ-< ι<ι)
      with NP.1+n≰n ι<ι
    ... | ()
    subst-σ-unique (subst-ρ-inst-≡ sub-σ) (subst-ρ-inst-≡ sub-σ') = subst-σ-unique sub-σ sub-σ'
    subst-σ-unique (subst-ρ-inst-≡ sub-σ) (subst-ρ-inst-> ι>ι)
      with NP.1+n≰n ι>ι
    ... | ()
    subst-σ-unique (subst-ρ-inst-> ι₁>ι₂) (subst-ρ-< ι₁<ι₂)
      with NP.1+n≰n (NP.<-trans ι₁<ι₂ ι₁>ι₂)
    ... | ()
    subst-σ-unique (subst-ρ-inst-> ι>ι) (subst-ρ-inst-≡ sub-σ)
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
    can-weaken-τ : ∀ τ n ι → ∃ λ τ' → τ ⟦ weaken n / ι ⟧τ≡ τ'
    can-weaken-τ (α⁼ ι₁) n ι₂ with ι₂ ≤? ι₁
    ... | yes ι₁≥ι₂ = α⁼ (n + ι₁) , subst-α-weaken-≥ ι₁≥ι₂
    ... | no ι₁≱ι₂ = α⁼ ι₁ , subst-α-< (NP.≰⇒> ι₁≱ι₂)
    can-weaken-τ int n ι = int , subst-int
    can-weaken-τ ns n ι = ns , subst-ns
    can-weaken-τ (∀[ Δ ] Γ) n ι with can-weaken-Γ Γ n (length Δ + ι)
    ... | Γ' , sub-Γ = ∀[ Δ ] Γ' , subst-∀ sub-Γ
    can-weaken-τ (tuple τs) n ι with can-weaken-τs⁻ τs n ι
    ... | τs' , sub-τs = tuple τs' , subst-tuple sub-τs

    can-weaken-τ⁻ : ∀ τ⁻ n ι → ∃ λ τ⁻' → τ⁻ ⟦ weaken n / ι ⟧τ⁻≡ τ⁻'
    can-weaken-τ⁻ (τ , φ) n ι with can-weaken-τ τ n ι
    ... | τ' , sub-τ = (τ' , φ) , subst-τ⁻ sub-τ

    can-weaken-τs⁻ : ∀ {m} (τs⁻ : Vec InitType m) n ι →
                       ∃ λ τs⁻' → τs⁻ ⟦ weaken n / ι ⟧τs⁻≡ τs⁻'
    can-weaken-τs⁻ [] n ι = [] , subst-[]
    can-weaken-τs⁻ (τ⁻ ∷ τs⁻) n ι
      with can-weaken-τ⁻ τ⁻ n ι | can-weaken-τs⁻ τs⁻ n ι
    ... | τ⁻' , sub-τ⁻ | τs⁻' , sub-τs⁻ = τ⁻' ∷ τs⁻' , subst-∷ sub-τ⁻ sub-τs⁻

    can-weaken-σ : ∀ σ n ι → ∃ λ σ' → σ ⟦ weaken n / ι ⟧σ≡ σ'
    can-weaken-σ (ρ⁼ ι₁) n ι₂ with ι₂ ≤? ι₁
    ... | yes ι₁≥ι₂ = ρ⁼ (n + ι₁) , subst-ρ-weaken-≥ ι₁≥ι₂
    ... | no ι₁≱ι₂ = ρ⁼ ι₁ , subst-ρ-< (NP.≰⇒> ι₁≱ι₂)
    can-weaken-σ nil n ι = nil , subst-[]
    can-weaken-σ (τ ∷ σ) n ι with can-weaken-τ τ n ι | can-weaken-σ σ n ι
    ... | τ' , sub-τ | σ' , sub-σ = τ' ∷ σ' , subst-∷ sub-τ sub-σ

    can-weaken-Γ : ∀ Γ n ι → ∃ λ Γ' → Γ ⟦ weaken n / ι ⟧Γ≡ Γ'
    can-weaken-Γ (registerₐ sp regs) n ι
      with can-weaken-σ sp n ι | can-weaken-regs regs n ι
    ... | sp' , sub-sp | regs' , sub-regs =
          registerₐ sp' regs' , subst-registerₐ sub-sp sub-regs

    can-weaken-regs : ∀ {m} (regs : Vec Type m) n ι →
                        ∃ λ regs' → regs ⟦ weaken n / ι ⟧regs≡ regs'
    can-weaken-regs [] n ι = [] , subst-[]
    can-weaken-regs (τ ∷ τs) n ι
      with can-weaken-τ τ n ι | can-weaken-regs τs n ι
    ... | τ' , sub-τ | τs' , sub-τs = τ' ∷ τs' , subst-∷ sub-τ sub-τs

  mutual
    _⟦_⟧τ? : ∀ τ c → Dec (∃ λ τ' → τ ⟦ c ⟧τ≡ τ')
    α⁼ ι₁ ⟦ cᵥ / ι₂ ⟧τ? with Nat-cmp ι₁ ι₂
    α⁼ ι₁ ⟦ cᵥ / ι₂ ⟧τ? | tri< ι₁<ι₂ _ _ = yes (α⁼ ι₁ , subst-α-< ι₁<ι₂)
    α⁼ ι  ⟦ inst α τ / .ι ⟧τ? | tri≈ _ refl _ with can-weaken-τ τ ι 0
    ... | τ' , sub-τ = yes (τ' , subst-α-inst-≡ sub-τ)
    α⁼ ι  ⟦ inst ρ σ / .ι ⟧τ? | tri≈ _ refl _ = no help
      where help : ∀ {ι σ} → ¬ (∃ λ τ' → α⁼ ι ⟦ inst ρ σ / ι ⟧τ≡ τ')
            help (._ , subst-α-< ι<ι) = NP.1+n≰n ι<ι
            help (._ , subst-α-inst-> ι>ι) = NP.1+n≰n ι>ι
    α⁼ ι  ⟦ weaken n / .ι ⟧τ? | tri≈ _ refl _ =
      yes (α⁼ (n + ι) , subst-α-weaken-≥ (Nat-≤-refl ι))
    α⁼ zero ⟦ inst a i / ι₂ ⟧τ? | tri> _ _ ()
    α⁼ (suc ι₁) ⟦ inst a x / ι₂ ⟧τ? | tri> _ _ sucι₁>ι₂ =
      yes (α⁼ ι₁ , subst-α-inst-> sucι₁>ι₂)
    α⁼ ι₁ ⟦ weaken n / ι₂ ⟧τ? | tri> _ _ ι₁>ι₂ =
      yes (α⁼ (n + ι₁) , subst-α-weaken-≥ (NP.≤⇒pred≤ _ _ ι₁>ι₂))
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
    ρ⁼ ι  ⟦ inst ρ σ / .ι ⟧σ? | tri≈ _ refl _ with can-weaken-σ σ ι 0
    ... | σ' , sub-σ = yes (σ' , subst-ρ-inst-≡ sub-σ)
    ρ⁼ ι  ⟦ inst α τ / .ι ⟧σ? | tri≈ _ refl _ = no help
      where help : ∀ {ι τ} → ¬ (∃ λ σ' → ρ⁼ ι ⟦ inst α τ / ι ⟧σ≡ σ')
            help (._ , subst-ρ-< ι<ι) = NP.1+n≰n ι<ι
            help (._ , subst-ρ-inst-> ι>ι) = NP.1+n≰n ι>ι
    ρ⁼ ι  ⟦ weaken n / .ι ⟧σ? | tri≈ _ refl _ =
      yes (ρ⁼ (n + ι) , subst-ρ-weaken-≥ (Nat-≤-refl ι))
    ρ⁼ zero ⟦ inst a i / ι₂ ⟧σ? | tri> _ _ ()
    ρ⁼ (suc ι₁) ⟦ inst a x / ι₂ ⟧σ? | tri> _ _ sucι₁>ι₂ =
      yes (ρ⁼ ι₁ , subst-ρ-inst-> sucι₁>ι₂)
    ρ⁼ ι₁ ⟦ weaken n / ι₂ ⟧σ? | tri> _ _ ι₁>ι₂ =
      yes (ρ⁼ (n + ι₁) , subst-ρ-weaken-≥ (NP.≤⇒pred≤ _ _ ι₁>ι₂))
    nil ⟦ c ⟧σ? = yes (nil , subst-[])
    (τ ∷ σ) ⟦ c ⟧σ? with τ ⟦ c ⟧τ? | σ ⟦ c ⟧σ?
    ... | yes (τ' , sub-τ) | yes (σ' , sub-σ) =
      yes (τ' ∷ σ' , subst-∷ sub-τ sub-σ)
    ... | no ¬sub-τ | _ =
      no (λ { (._ , subst-∷ sub-τ sub-σ) → ¬sub-τ (_ , sub-τ) })
    ... | _ | no ¬sub-σ =
      no (λ { (._ , subst-∷ sub-τ sub-σ) → ¬sub-σ (_ , sub-σ) })

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

record Substitution (A : Set) : Set1 where
  constructor substitution
  field
    _⟦_⟧≡_ : A → Cast → A → Set
    subst-unique : ∀ {v v₁ v₂ c} → v ⟦ c ⟧≡ v₁ →
                                   v ⟦ c ⟧≡ v₂ →
                                   v₁ ≡ v₂
    _⟦_⟧? : ∀ v c → Dec (∃ λ v' → v ⟦ c ⟧≡ v')
    can-weaken : ∀ v n ι → ∃ λ v' → v ⟦ weaken n / ι ⟧≡ v'

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
can-weaken : ∀ {A} {{_ : Substitution A}} →
               ∀ v n ι → ∃ λ v' → v ⟦ weaken n / ι ⟧≡ v'
can-weaken {{s}} = Substitution.can-weaken s

instance
  Type-substitution : Substitution Type
  Type-substitution =
    substitution _⟦_⟧τ≡_ subst-τ-unique _⟦_⟧τ? can-weaken-τ

  InitType-substitution : Substitution InitType
  InitType-substitution =
    substitution _⟦_⟧τ⁻≡_ subst-τ⁻-unique _⟦_⟧τ⁻? can-weaken-τ⁻

  StackType-substitution : Substitution StackType
  StackType-substitution =
    substitution _⟦_⟧σ≡_ subst-σ-unique _⟦_⟧σ? can-weaken-σ

  RegisterAssignment-substitution : Substitution RegisterAssignment
  RegisterAssignment-substitution =
    substitution _⟦_⟧Γ≡_ subst-Γ-unique _⟦_⟧Γ? can-weaken-Γ

  Vec-substitution : ∀ {A} {m} {{s : Substitution A}} → Substitution (Vec A m)
  Vec-substitution = substitution
      _⟦_⟧xs≡_
      unique
      dec
      weak

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

          weak : ∀ {A m} {{s : Substitution A}} (xs : Vec A m) n ι →
                   ∃ λ xs' → xs ⟦ weaken n / ι ⟧xs≡ xs'
          weak [] n ι = [] , []
          weak (x ∷ xs) n ι with can-weaken x n ι | weak xs n ι
          ... | x' , sub-x | xs' , sub-xs = x' ∷ xs' , sub-x ∷ sub-xs

  List-substitution : ∀ {A} {{s : Substitution A}} → Substitution (List A)
  List-substitution = substitution
      _⟦_⟧xs≡_
      unique
      dec
      weak

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

          weak : ∀ {A} {{s : Substitution A}} (xs : List A) n ι →
                   ∃ λ xs' → xs ⟦ weaken n / ι ⟧xs≡ xs'
          weak [] n ι = [] , refl , []
          weak (x ∷ xs) n ι with can-weaken x n ι | weak xs n ι
          ... | x' , sub-x | xs' , eq , sub-xs =
            x' ∷ xs' , (cong suc eq) , (sub-x ∷ sub-xs)
