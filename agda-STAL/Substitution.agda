open import Grammar
open import Util
import Data.Nat as N
import Data.Nat.Properties as NP
import Relation.Binary as B

mutual
  private
    substᵗ : Set → Set1
    substᵗ A = A → WeakCast → A → Set

  infix 5 _⟦_⟧n≡_
  data _⟦_⟧n≡_ : substᵗ ℕ where
    subst-< :
         ∀ {n ι cᵥ} →
           n < ι →
      ----------------
      n ⟦ cᵥ / ι ⟧n≡ n

    subst-inst-> :
             ∀ {n ι i} →
             suc n > ι →
      ------------------------
      suc n ⟦ inst i / ι ⟧n≡ n

    subst-weaken-≥ :
            ∀ {n ι n⁺} →
               n ≥ ι →
      ----------------------------
      n ⟦ weaken n⁺ / ι ⟧n≡ n⁺ + n

  infix 5 _⟦_⟧τ≡_
  data _⟦_⟧τ≡_ : substᵗ Type where
    subst-α-¬inst :
          ∀ {ι₁ ι₁' ι₂ cᵥ} →
         ι₁ ⟦ cᵥ / ι₂ ⟧n≡ ι₁' →
      --------------------------
      α⁼ ι₁ ⟦ cᵥ / ι₂ ⟧τ≡ α⁼ ι₁'

    subst-α-inst :
            ∀ {ι τ τ'} →
       τ ⟦ weaken ι / zero ⟧τ≡ τ' →
      ---------------------------
      α⁼ ι  ⟦ inst (α τ) / ι ⟧τ≡ τ'

    subst-int :
          ∀ {c} →
      ---------------
      int ⟦ c ⟧τ≡ int

    subst-ns :
         ∀ {c} →
      -------------
      ns ⟦ c ⟧τ≡ ns

    subst-∀ :
            ∀ {Δ Δ' Γ Γ' cᵥ ι} →
            Δ ⟦ cᵥ / ι ⟧Δ≡ Δ' →
       Γ ⟦ cᵥ / length Δ + ι ⟧Γ≡ Γ' →
      --------------------------------
      ∀[ Δ ] Γ ⟦ cᵥ / ι ⟧τ≡ ∀[ Δ' ] Γ'

    subst-tuple :
           ∀ {c τs τs'} →
          τs ⟦ c ⟧τs⁻≡ τs' →
      --------------------------
      tuple τs ⟦ c ⟧τ≡ tuple τs'

  infix 5 _⟦_⟧τ⁻≡_
  data _⟦_⟧τ⁻≡_ : substᵗ InitType where
    subst-τ⁻ :
            ∀ {φ τ τ' c} →
            τ ⟦ c ⟧τ≡ τ' →
      -------------------------
      (τ , φ) ⟦ c ⟧τ⁻≡ (τ' , φ)

  infix 5 _⟦_⟧τs⁻≡_
  _⟦_⟧τs⁻≡_ : substᵗ (List InitType)
  τs⁻ ⟦ c ⟧τs⁻≡ τs⁻' =
    AllZip (λ τ⁻ τ⁻' → τ⁻ ⟦ c ⟧τ⁻≡ τ⁻') τs⁻ τs⁻'

  infix 5 _⟦_⟧σ≡_
  data _⟦_⟧σ≡_ : substᵗ StackType where
    subst-ρ-¬inst :
          ∀ {ι₁ ι₁' ι₂ cᵥ} →
        ι₁ ⟦ cᵥ / ι₂ ⟧n≡ ι₁' →
      --------------------------
      ρ⁼ ι₁ ⟦ cᵥ / ι₂ ⟧σ≡ ρ⁼ ι₁'

    subst-ρ-inst :
               ∀ {ι σ σ'} →
      σ ⟦ weaken ι / zero ⟧σ≡ σ' →
      ----------------------------
      ρ⁼ ι  ⟦ inst (ρ σ) / ι ⟧σ≡ σ'

    subst-nil :
         ∀ {c} →
     ---------------
     nil ⟦ c ⟧σ≡ nil

    _∷_ :
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
  _⟦_⟧regs≡_ : ∀ {m} → substᵗ (Vec Type m)
  τs ⟦ c ⟧regs≡ τs' = AllZipᵥ (λ τ τ' → τ ⟦ c ⟧τ≡ τ') τs τs'

  infix 5 _⟦_⟧Δ≡_
  infixr 5 _∷_
  data _⟦_⟧Δ≡_ : substᵗ TypeAssignment where
    [] :
          ∀ {c} →
      -------------
      [] ⟦ c ⟧Δ≡ []

    _∷_ :
            ∀ {a a' Δ Δ' cᵥ ι} →
      a ⟦ cᵥ / length Δ + ι ⟧a≡ a' →
            Δ ⟦ cᵥ / ι ⟧Δ≡ Δ' →
      ------------------------------
        a ∷ Δ ⟦ cᵥ / ι ⟧Δ≡ a' ∷ Δ'

  infix 5 _⟦_⟧a≡_
  data _⟦_⟧a≡_ : substᵗ TypeAssignmentValue where
    subst-α : ∀ {c} → α ⟦ c ⟧a≡ α
    subst-ρ : ∀ {c} → ρ ⟦ c ⟧a≡ ρ

  infix 5 _⟦_⟧i≡_
  data _⟦_⟧i≡_ : substᵗ Instantiation where
    subst-α :
        ∀ {τ τ' c} →
       τ ⟦ c ⟧τ≡ τ' →
      ----------------
      α τ ⟦ c ⟧i≡ α τ'

    subst-ρ :
        ∀ {σ σ' c} →
       σ ⟦ c ⟧σ≡ σ' →
      ----------------
      ρ σ ⟦ c ⟧i≡ ρ σ'


subst-n-≢-inst : ∀ {i ι₁ ι₂} → ¬ ι₁ ⟦ inst i / ι₁ ⟧n≡ ι₂
subst-n-≢-inst (subst-< ι₁<ι₁) = NP.1+n≰n ι₁<ι₁
subst-n-≢-inst (subst-inst-> ι₁>ι₁) = NP.1+n≰n ι₁>ι₁

private
  mutual
    substᵗ-unique : ∀ {A} → substᵗ A → Set
    substᵗ-unique _⟦_⟧≡_ = ∀ {v v₁ v₂ c} →
                             v ⟦ c ⟧≡ v₁ →
                             v ⟦ c ⟧≡ v₂ →
                             v₁ ≡ v₂

    subst-n-unique : substᵗ-unique _⟦_⟧n≡_
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

    subst-τ-unique : substᵗ-unique _⟦_⟧τ≡_
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

    subst-τ⁻-unique : substᵗ-unique _⟦_⟧τ⁻≡_
    subst-τ⁻-unique (subst-τ⁻ {φ = φ} sub-τ₁) (subst-τ⁻ sub-τ₂) =
      cong₂ _,_ (subst-τ-unique sub-τ₁ sub-τ₂) refl

    subst-τs⁻-unique : substᵗ-unique _⟦_⟧τs⁻≡_
    subst-τs⁻-unique [] [] = refl
    subst-τs⁻-unique (sub-τ⁻₁ ∷ sub-τs⁻₁) (sub-τ⁻₂ ∷ sub-τs⁻₂) =
        cong₂ _∷_ (subst-τ⁻-unique sub-τ⁻₁ sub-τ⁻₂)
                  (subst-τs⁻-unique sub-τs⁻₁ sub-τs⁻₂)

    subst-σ-unique : substᵗ-unique _⟦_⟧σ≡_
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
    subst-σ-unique subst-nil subst-nil = refl
    subst-σ-unique (sub-τ₁ ∷ sub-σ₁) (sub-τ₂ ∷ sub-σ₂) =
      cong₂ _∷_ (subst-τ-unique sub-τ₁ sub-τ₂) (subst-σ-unique sub-σ₁ sub-σ₂)

    subst-Γ-unique : substᵗ-unique _⟦_⟧Γ≡_
    subst-Γ-unique (subst-registerₐ sub-sp₁ sub-regs₁)
                   (subst-registerₐ sub-sp₂ sub-regs₂) =
      cong₂ registerₐ (subst-σ-unique sub-sp₁ sub-sp₂)
                      (subst-regs-unique sub-regs₁ sub-regs₂)

    subst-regs-unique : ∀ {m} → substᵗ-unique (_⟦_⟧regs≡_ {m})
    subst-regs-unique {v = []} {[]} {[]} [] [] = refl
    subst-regs-unique {v = τ ∷ τs} {τ₁ ∷ τs₁} {τ₂ ∷ τs₂}
      (sub-τ₁ ∷ sub-τs₁) (sub-τ₂ ∷ sub-τs₂) =
        cong₂ _∷_ (subst-τ-unique sub-τ₁ sub-τ₂)
                  (subst-regs-unique sub-τs₁ sub-τs₂)

    subst-Δ-unique : substᵗ-unique _⟦_⟧Δ≡_
    subst-Δ-unique [] [] = refl
    subst-Δ-unique (sub-a₁ ∷ sub-Δ₁) (sub-a₂ ∷ sub-Δ₂) =
      cong₂ _∷_ (subst-a-unique sub-a₁ sub-a₂)
                (subst-Δ-unique sub-Δ₁ sub-Δ₂)

    subst-a-unique : substᵗ-unique _⟦_⟧a≡_
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
    can-weaken-σ nil n ι = nil , subst-nil
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
    nil ⟦ c ⟧σ? = yes (nil , subst-nil)
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
      (λ {(._ , subst-registerₐ sub-sp sub-regs) → ¬sub-regs (_ , sub-regs) })

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
    σ-weaken-0 nil = subst-nil
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

record Substitution (A W : Set) : Set1 where
  constructor substitution
  field
    W₀ : W
    _⟦_⟧≡_ : A → Cast W → A → Set
    subst-unique : ∀ {v v₁ v₂ c} → v ⟦ c ⟧≡ v₁ →
                                   v ⟦ c ⟧≡ v₂ →
                                   v₁ ≡ v₂
    can-weaken : ∀ v w ι → ∃ λ v' → v ⟦ weaken w / ι ⟧≡ v'
    _⟦_⟧? : ∀ v c → Dec (∃ λ v' → v ⟦ c ⟧≡ v')
    weaken-0 : ∀ v {ι} → v ⟦ weaken W₀ / ι ⟧≡ v
  infix 5 _⟦_⟧≡_ _⟦_⟧?

  weaken-0-unique : ∀ {v₁ v₂ ι} → v₁ ⟦ weaken W₀ / ι ⟧≡ v₂ →
                                  v₁ ≡ v₂
  weaken-0-unique {v₁} = subst-unique (weaken-0 v₁)

open Substitution {{...}} public

Vec-Substitution : ∀ {A W} {m} {{s : Substitution A W}} →
                     Substitution (Vec A m) W
Vec-Substitution = substitution
    W₀
    _⟦_⟧xs≡_
    unique
    weak
    dec
    xs-weaken-0

  where _⟦_⟧xs≡_ : ∀ {A W} {{s : Substitution A W}} {m} →
                     Vec A m → Cast W → Vec A m → Set
        xs ⟦ c ⟧xs≡ xs' =
          AllZipᵥ (λ x x' → x ⟦ c ⟧≡ x') xs xs'

        unique : ∀ {A W m c} {xs xs₁ xs₂ : Vec A m}
                   {{s : Substitution A W}} →
                   xs ⟦ c ⟧xs≡ xs₁ →
                   xs ⟦ c ⟧xs≡ xs₂ →
                   xs₁ ≡ xs₂
        unique {xs = []} {[]} {[]} [] [] = refl
        unique {xs = x ∷ xs} {x₁ ∷ xs₁} {x₂ ∷ xs₂} {{s}}
               (sub-x₁ ∷ sub-xs₁) (sub-x₂ ∷ sub-xs₂) =
          cong₂ _∷_ (subst-unique sub-x₁ sub-x₂) (unique sub-xs₁ sub-xs₂)

        weak : ∀ {A W m} {{s : Substitution A W}}
                 (xs : Vec A m) w ι → ∃ λ xs' → xs ⟦ weaken w / ι ⟧xs≡ xs'
        weak [] w ι = [] , []
        weak (x ∷ xs) w ι with can-weaken x w ι | weak xs w ι
        ... | x' , sub-x | xs' , sub-xs = x' ∷ xs' , sub-x ∷ sub-xs

        dec : ∀ {A W m} {{s : Substitution A W}} (xs : Vec A m) c →
                Dec (∃ λ xs' → xs ⟦ c ⟧xs≡ xs')
        dec [] c = yes ([] , [])
        dec (x ∷ xs) c with x ⟦ c ⟧? | dec xs c
        dec (x ∷ xs) c | yes (x' , sub-x) | yes (xs' , sub-xs) =
          yes ((x' ∷ xs') , sub-x ∷ sub-xs)
        dec (x ∷ xs) c | no ¬sub-x | _ =
          no (λ { (x' ∷ xs' , sub-x ∷ sub-xs) → ¬sub-x (x' , sub-x)})
        dec (x ∷ xs) c | _ | no ¬sub-xs =
          no (λ { (x' ∷ xs' , sub-x ∷ sub-xs) → ¬sub-xs (xs' , sub-xs)})

        xs-weaken-0 : ∀ {A W m} {{_ : Substitution A W}}
                        (xs : Vec A m) {ι} → xs ⟦ weaken W₀ / ι ⟧xs≡ xs
        xs-weaken-0 [] = []
        xs-weaken-0 (x ∷ xs) = weaken-0 x ∷ xs-weaken-0 xs

List-Substitution : ∀ {A W} {{s : Substitution A W}} → Substitution (List A) W
List-Substitution = substitution
    W₀
    _⟦_⟧xs≡_
    unique
    weak
    dec
    xs-weaken-0

  where _⟦_⟧xs≡_ : ∀ {A W} {{s : Substitution A W}} →
                       List A → Cast W → List A → Set
        xs ⟦ c ⟧xs≡ xs' = AllZip (λ x x' → x ⟦ c ⟧≡ x') xs xs'

        unique : ∀ {A W c} {xs xs₁ xs₂ : List A}
                   {{s : Substitution A W}} →
                   xs ⟦ c ⟧xs≡ xs₁ →
                   xs ⟦ c ⟧xs≡ xs₂ →
                   xs₁ ≡ xs₂
        unique [] [] = refl
        unique (sub-x₁ ∷ sub-xs₁) (sub-x₂ ∷ sub-xs₂)
          = cong₂ _∷_ (subst-unique sub-x₁ sub-x₂)
                      (unique sub-xs₁ sub-xs₂)

        weak : ∀ {A W} {{s : Substitution A W}}
                 (xs : List A) w ι → ∃ λ xs' → xs ⟦ weaken w / ι ⟧xs≡ xs'
        weak [] w ι = [] , []
        weak (x ∷ xs) w ι with can-weaken x w ι | weak xs w ι
        ... | x' , sub-x | xs' , sub-xs =
          x' ∷ xs' , sub-x ∷ sub-xs

        dec : ∀ {A W} {{s : Substitution A W}} (xs : List A) c →
                Dec (∃ λ xs' → xs ⟦ c ⟧xs≡ xs')
        dec [] c = yes ([] , [])
        dec (x ∷ xs) c with x ⟦ c ⟧? | dec xs c
        dec (x ∷ xs) c | yes (x' , sub-x) | yes (xs' , sub-xs) =
          yes (x' ∷ xs' , sub-x ∷ sub-xs)
        dec (x ∷ xs) c | no ¬sub-x | _ =
          no (λ { (x' ∷ xs' , sub-x ∷ sub-xs) → ¬sub-x (x' , sub-x)})
        dec (x ∷ xs) c | _ | no ¬sub-xs =
          no (λ { (x' ∷ xs' , sub-x ∷ sub-xs) → ¬sub-xs (xs' , sub-xs)})

        xs-weaken-0 : ∀ {A W} {{_ : Substitution A W}}
                        (xs : List A) {ι} → xs ⟦ weaken W₀ / ι ⟧xs≡ xs
        xs-weaken-0 [] = []
        xs-weaken-0 (x ∷ xs) = weaken-0 x ∷ xs-weaken-0 xs

instance
  Type-Substitution : Substitution Type ℕ
  Type-Substitution =
    substitution 0 _⟦_⟧τ≡_ subst-τ-unique can-weaken-τ _⟦_⟧τ? τ-weaken-0

  TypeVec-Substitution : ∀ {m} → Substitution (Vec Type m) ℕ
  TypeVec-Substitution = Vec-Substitution

  TypeList-Substitution : Substitution (List Type) ℕ
  TypeList-Substitution = List-Substitution

  InitType-Substitution : Substitution InitType ℕ
  InitType-Substitution =
    substitution 0 _⟦_⟧τ⁻≡_ subst-τ⁻-unique can-weaken-τ⁻ _⟦_⟧τ⁻? τ⁻-weaken-0

  InitTypeVec-Substitution : ∀ {m} → Substitution (Vec InitType m) ℕ
  InitTypeVec-Substitution = Vec-Substitution

  InitTypeList-Substitution : Substitution (List InitType) ℕ
  InitTypeList-Substitution = List-Substitution

  StackType-Substitution : Substitution StackType ℕ
  StackType-Substitution =
    substitution 0 _⟦_⟧σ≡_ subst-σ-unique can-weaken-σ _⟦_⟧σ? σ-weaken-0

  RegisterAssignment-Substitution : Substitution RegisterAssignment ℕ
  RegisterAssignment-Substitution =
    substitution 0 _⟦_⟧Γ≡_ subst-Γ-unique can-weaken-Γ _⟦_⟧Γ? Γ-weaken-0

  TypeAssignment-Substitution : Substitution TypeAssignment ℕ
  TypeAssignment-Substitution =
    substitution 0 _⟦_⟧Δ≡_ subst-Δ-unique can-weaken-Δ _⟦_⟧Δ? Δ-weaken-0

  TypeAssignmentValue-Substitution : Substitution TypeAssignmentValue ℕ
  TypeAssignmentValue-Substitution =
    substitution 0 _⟦_⟧a≡_ subst-a-unique can-weaken-a _⟦_⟧a? a-weaken-0

Strong→WeakCastValue : StrongCastValue → WeakCastValue
Strong→WeakCastValue (inst i) = inst i
Strong→WeakCastValue (weaken Δ) = weaken (length Δ)

Strong→WeakCast : StrongCast → WeakCast
Strong→WeakCast (cᵥ / ι) = Strong→WeakCastValue cᵥ / ι

instance
  Weak→StrongSubstitution : ∀ {A} {{s : Substitution A ℕ}} →
                              {{_ : Substitution.W₀ s ≡ 0}} →
                              Substitution A TypeAssignment
  Weak→StrongSubstitution {{substitution .0 _⟦_⟧≡_ subst-unique
                                         can-weaken _⟦_⟧? weaken-0}}
                          {{refl}} = substitution
    []
    (λ v₁ c v₂ → v₁ ⟦ Strong→WeakCast c ⟧≡ v₂)
    subst-unique
    (λ v w ι → can-weaken v (length w) ι)
    (λ v c → v ⟦ Strong→WeakCast c ⟧?)
    weaken-0
