open import Grammar
open import Util
import Data.Nat.Properties as NP

mutual
  substᵗ : Set → Set1
  substᵗ A = A → InstantiationValue → AssignmentIndex → A → Set

  infix 5 _⟦_/_⟧τ≡_
  data _⟦_/_⟧τ≡_ : substᵗ Type where
    subst-α-≡ :
               ∀ {ι τ} →
      --------------------------
      α⁼ ι  ⟦ inst-α τ / ι ⟧τ≡ τ

    subst-α-< :
            ∀ {ι₁ ι₂ i} →
             ι₁ < ι₂ →
      -----------------------
      α⁼ ι₁ ⟦ i / ι₂ ⟧τ≡ α⁼ ι₁

    subst-α-> :
               ∀ {ι₁ ι₂ i} →
               ι₂ < suc ι₁ →
      ------------------------------
      α⁼ (suc ι₁) ⟦ i / ι₂ ⟧τ≡ α⁼ ι₁

    subst-int :
           ∀ {ι i} →
      -------------------
      int ⟦ i / ι ⟧τ≡ int

    subst-ns :
          ∀ {ι i} →
      -----------------
      ns ⟦ i / ι ⟧τ≡ ns

    subst-∀ :
           ∀ {Δ Γ Γ' i ι} →
      Γ ⟦ i / length Δ + ι ⟧Γ≡ Γ' →
      ------------------------------
      ∀[ Δ ] Γ ⟦ i / ι ⟧τ≡ ∀[ Δ ] Γ'

    subst-tuple :
            ∀ {i ι m τs τs'} →
           τs ⟦ i / ι ⟧τs⁻≡ τs' →
      ----------------------------------
      tuple {m} τs ⟦ i / ι ⟧τ≡ tuple τs'

  infix 5 _⟦_/_⟧τ⁻≡_
  data _⟦_/_⟧τ⁻≡_ : substᵗ InitType where
    subst-τ⁻ :
          ∀ {φ τ τ' i ι} →
         τ ⟦ i / ι ⟧τ≡ τ' →
      -------------------------
      (τ , φ) ⟦ i / ι ⟧τ⁻≡ (τ' , φ)

  infix 5 _⟦_/_⟧τs⁻≡_
  data _⟦_/_⟧τs⁻≡_ : ∀ {m} → substᵗ (Vec InitType m) where
    subst-[] :
           ∀ {i ι} →
      -------------------
      [] ⟦ i / ι ⟧τs⁻≡ []

    subst-∷ :
            ∀ {τ τ' m i ι} →
       {τs τs' : Vec InitType m} →
          τ ⟦ i / ι ⟧τ⁻≡ τ' →
         τs ⟦ i / ι ⟧τs⁻≡ τs' →
      -----------------------------
      τ ∷ τs ⟦ i / ι ⟧τs⁻≡ τ' ∷ τs'

  infix 5 _⟦_/_⟧σ≡_
  data _⟦_/_⟧σ≡_ : substᵗ StackType where
    subst-ρ-≡ :
              ∀ {ι σ} →
      -------------------------
      ρ⁼ ι ⟦ inst-ρ σ / ι ⟧σ≡ σ


    subst-ρ-< :
            ∀ {ι₁ ι₂ i} →
             ι₁ < ι₂ →
      -----------------------
      ρ⁼ ι₁ ⟦ i / ι₂ ⟧σ≡ ρ⁼ ι₁

    subst-ρ-> :
               ∀ {ι₁ ι₂ i} →
               ι₂ < suc ι₁ →
      ------------------------------
      ρ⁼ (suc ι₁) ⟦ i / ι₂ ⟧σ≡ ρ⁼ ι₁

    subst-[] :
           ∀ {i ι} →
      -------------------
      nil ⟦ i / ι ⟧σ≡ nil

    subst-∷ :
         ∀ {τ τ' σ σ' i ι} →
         τ ⟦ i / ι ⟧τ≡ τ' →
         σ ⟦ i / ι ⟧σ≡ σ' →
      -------------------------
      τ ∷ σ ⟦ i / ι ⟧σ≡ τ' ∷ σ'

  infix 5 _⟦_/_⟧Γ≡_
  data _⟦_/_⟧Γ≡_ : substᵗ RegisterAssignment where
    subst-registerₐ :
                ∀ {regs regs' sp sp' i ι} →
                   sp ⟦ i / ι ⟧σ≡ sp' →
                regs ⟦ i / ι ⟧regs≡ regs' →
      -------------------------------------------------
      registerₐ sp regs ⟦ i / ι ⟧Γ≡ registerₐ sp' regs'

  infix 5 _⟦_/_⟧regs≡_
  data _⟦_/_⟧regs≡_ : ∀ {m} → substᵗ (Vec Type m) where
    subst-[] :
           ∀ {i ι} →
      -------------------
      [] ⟦ i / ι ⟧regs≡ []

    subst-∷ :
            ∀ {τ τ' m i ι} →
         {τs τs' : Vec Type m} →
           τ ⟦ i / ι ⟧τ≡ τ' →
         τs ⟦ i / ι ⟧regs≡ τs' →
      ------------------------------
      τ ∷ τs ⟦ i / ι ⟧regs≡ τ' ∷ τs'

private
  mutual
    substᵗ-unique : ∀ {A} → substᵗ A → Set
    substᵗ-unique _⟦_/_⟧≡_ = ∀ {v v₁ v₂ i ι} →
                               v ⟦ i / ι ⟧≡ v₁ →
                               v ⟦ i / ι ⟧≡ v₂ →
                               v₁ ≡ v₂

    subst-τ-unique : substᵗ-unique _⟦_/_⟧τ≡_
    subst-τ-unique subst-α-≡ subst-α-≡ = refl
    subst-τ-unique subst-α-≡ (subst-α-< ι<ι) with NP.1+n≰n ι<ι
    subst-τ-unique subst-α-≡ (subst-α-< ι<ι) | ()
    subst-τ-unique subst-α-≡ (subst-α-> ι>ι) with NP.1+n≰n ι>ι
    subst-τ-unique subst-α-≡ (subst-α-> ι>ι) | ()
    subst-τ-unique (subst-α-< ι<ι) subst-α-≡ with NP.1+n≰n ι<ι
    subst-τ-unique (subst-α-< ι<ι) subst-α-≡ | ()
    subst-τ-unique (subst-α-< ι₁<ι₂) (subst-α-< ι₁<ι₂') = refl
    subst-τ-unique (subst-α-< ι₁<ι₂) (subst-α-> ι₁>ι₂)
      with NP.1+n≰n (NP.<-trans ι₁<ι₂ ι₁>ι₂)
    ... | ()
    subst-τ-unique (subst-α-> ι>ι) subst-α-≡
      with NP.1+n≰n ι>ι
    ... | ()
    subst-τ-unique (subst-α-> ι₁>ι₂) (subst-α-< ι₁<ι₂)
      with NP.1+n≰n (NP.<-trans ι₁<ι₂ ι₁>ι₂)
    ... | ()
    subst-τ-unique (subst-α-> ι₁>ι₂) (subst-α-> ι₁>ι₂') = refl
    subst-τ-unique subst-int subst-int = refl
    subst-τ-unique subst-ns subst-ns = refl
    subst-τ-unique (subst-∀ {Δ = Δ} sub-Γ₁) (subst-∀ sub-Γ₂) =
      cong (∀[_]_ Δ) (subst-Γ-unique sub-Γ₁ sub-Γ₂)
    subst-τ-unique (subst-tuple sub-τs₁) (subst-tuple sub-τs₂) =
      cong tuple (subst-τs⁻-unique sub-τs₁ sub-τs₂)

    subst-τ⁻-unique : substᵗ-unique _⟦_/_⟧τ⁻≡_
    subst-τ⁻-unique (subst-τ⁻ {φ = φ} sub-τ₁) (subst-τ⁻ sub-τ₂) =
      cong₂ _,_ (subst-τ-unique sub-τ₁ sub-τ₂) refl

    subst-τs⁻-unique : ∀ {m} → substᵗ-unique (_⟦_/_⟧τs⁻≡_ {m})
    subst-τs⁻-unique subst-[] subst-[] = refl
    subst-τs⁻-unique (subst-∷ sub-τ₁ sub-τs₁) (subst-∷ sub-τ₂ sub-τs₂) =
      cong₂ _∷_ (subst-τ⁻-unique sub-τ₁ sub-τ₂)
                (subst-τs⁻-unique sub-τs₁ sub-τs₂)

    subst-σ-unique : substᵗ-unique _⟦_/_⟧σ≡_
    subst-σ-unique subst-ρ-≡ subst-ρ-≡ = refl
    subst-σ-unique subst-ρ-≡ (subst-ρ-< ι<ι)
      with NP.1+n≰n ι<ι
    ... | ()
    subst-σ-unique subst-ρ-≡ (subst-ρ-> ι>ι)
      with NP.1+n≰n ι>ι
    ... | ()
    subst-σ-unique (subst-ρ-< ι<ι) subst-ρ-≡
      with NP.1+n≰n ι<ι
    ... | ()
    subst-σ-unique (subst-ρ-< ι₁<ι₂) (subst-ρ-< ι₁<ι₂') = refl
    subst-σ-unique (subst-ρ-< ι₁<ι₂) (subst-ρ-> ι₁>ι₂)
      with NP.1+n≰n (NP.<-trans ι₁<ι₂ ι₁>ι₂)
    ... | ()
    subst-σ-unique (subst-ρ-> ι>ι) subst-ρ-≡
      with NP.1+n≰n ι>ι
    ... | ()
    subst-σ-unique (subst-ρ-> ι₁>ι₂) (subst-ρ-< ι₁<ι₂)
      with NP.1+n≰n (NP.<-trans ι₁<ι₂ ι₁>ι₂)
    ... | ()
    subst-σ-unique (subst-ρ-> ι₁>ι₂) (subst-ρ-> ι₁>ι₂') = refl
    subst-σ-unique subst-[] subst-[] = refl
    subst-σ-unique (subst-∷ sub-τ₁ sub-σ₁) (subst-∷ sub-τ₂ sub-σ₂) =
      cong₂ _∷_ (subst-τ-unique sub-τ₁ sub-τ₂) (subst-σ-unique sub-σ₁ sub-σ₂)

    subst-Γ-unique : substᵗ-unique _⟦_/_⟧Γ≡_
    subst-Γ-unique (subst-registerₐ sub-sp₁ sub-regs₁)
                   (subst-registerₐ sub-sp₂ sub-regs₂) =
      cong₂ registerₐ (subst-σ-unique sub-sp₁ sub-sp₂)
                      (subst-regs-unique sub-regs₁ sub-regs₂)

    subst-regs-unique : ∀ {m} → substᵗ-unique (_⟦_/_⟧regs≡_ {m})
    subst-regs-unique subst-[] subst-[] = refl
    subst-regs-unique (subst-∷ sub-τ₁ sub-τs₁) (subst-∷ sub-τ₂ sub-τs₂) =
      cong₂ _∷_ (subst-τ-unique sub-τ₁ sub-τ₂)
                (subst-regs-unique sub-τs₁ sub-τs₂)

  mutual
    _⟦_/_⟧τ? : ∀ τ i ι → Dec (∃ λ τ' → τ ⟦ i / ι ⟧τ≡ τ')
    α⁼ ι₁ ⟦ i / ι₂ ⟧τ? with Nat-cmp ι₁ ι₂
    α⁼ ι₁ ⟦ i / ι₂ ⟧τ? | tri< ι₁<ι₂ _ _ = yes (α⁼ ι₁ , subst-α-< ι₁<ι₂)
    α⁼ ι ⟦ inst-ρ σ / .ι ⟧τ? | tri≈ _ refl _ = no help
      where help : ∀ {ι σ} → ¬ (∃ λ τ' → α⁼ ι ⟦ inst-ρ σ / ι ⟧τ≡ τ')
            help (._ , subst-α-< ι<ι) = NP.1+n≰n ι<ι
            help (._ , subst-α-> ι>ι) = NP.1+n≰n ι>ι
    α⁼ ι ⟦ inst-α τ / .ι ⟧τ? | tri≈ _ refl _ = yes (τ , subst-α-≡)
    α⁼ zero ⟦ i / ι₂ ⟧τ? | tri> _ _ ()
    α⁼ (suc ι₁) ⟦ i / ι₂ ⟧τ? | tri> _ _ ι₁>ι₂ = yes (α⁼ ι₁ , subst-α-> ι₁>ι₂)
    int ⟦ i / ι ⟧τ? = yes (int , subst-int)
    ns ⟦ i / ι ⟧τ? = yes (ns , subst-ns)
    (∀[ Δ ] Γ) ⟦ i / ι ⟧τ? with Γ ⟦ i / length Δ + ι ⟧Γ?
    (∀[ Δ ] Γ) ⟦ i / ι ⟧τ? | yes (Γ' , sub-Γ) =
      yes (∀[ Δ ] Γ' , subst-∀ sub-Γ)
    (∀[ Δ ] Γ) ⟦ i / ι ⟧τ? | no ¬sub-Γ =
      no (λ { (._ , subst-∀ sub-Γ) → ¬sub-Γ (_ , sub-Γ) })
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

    _⟦_/_⟧τs⁻? : ∀ {m} (τs⁻ : Vec InitType m) i ι →
                   Dec (∃ λ τs⁻' → τs⁻ ⟦ i / ι ⟧τs⁻≡ τs⁻')
    [] ⟦ i / ι ⟧τs⁻? = yes ([] , subst-[])
    (τ⁻ ∷ τs⁻) ⟦ i / ι ⟧τs⁻? with τ⁻ ⟦ i / ι ⟧τ⁻? | τs⁻ ⟦ i / ι ⟧τs⁻?
    ... | yes (τ⁻' , sub-τ⁻) | yes (τs⁻' , sub-τs⁻) =
      yes (τ⁻' ∷ τs⁻' , subst-∷ sub-τ⁻ sub-τs⁻)
    ... | no ¬sub-τ⁻ | _ =
      no (λ { (._ , subst-∷ sub-τ⁻ sub-τs⁻) → ¬sub-τ⁻ (_ , sub-τ⁻) })
    ... | _ | no ¬sub-τs⁻ =
      no (λ { (._ , subst-∷ sub-τ⁻ sub-τs⁻) → ¬sub-τs⁻ (_ , sub-τs⁻) })

    _⟦_/_⟧σ? : ∀ σ i ι → Dec (∃ λ σ' → σ ⟦ i / ι ⟧σ≡ σ')
    ρ⁼ ι₁ ⟦ i / ι₂ ⟧σ? with Nat-cmp ι₁ ι₂
    ρ⁼ ι₁ ⟦ i / ι₂ ⟧σ? | tri< ι₁<ι₂ _ _ = yes (ρ⁼ ι₁ , subst-ρ-< ι₁<ι₂)
    ρ⁼ ι  ⟦ inst-ρ σ / .ι ⟧σ? | tri≈ _ refl _ = yes (σ , subst-ρ-≡)
    ρ⁼ ι  ⟦ inst-α τ / .ι ⟧σ? | tri≈ _ refl _ = no help
      where help : ∀ {ι τ} → ¬ (∃ λ σ' → ρ⁼ ι ⟦ inst-α τ / ι ⟧σ≡ σ')
            help (._ , subst-ρ-< ι<ι) = NP.1+n≰n ι<ι
            help (._ , subst-ρ-> ι>ι) = NP.1+n≰n ι>ι
    ρ⁼ zero ⟦ i / ι₂ ⟧σ? | tri> _ _ ()
    ρ⁼ (suc ι₁) ⟦ i / ι₂ ⟧σ? | tri> _ _ ι₁>ι₂ = yes (ρ⁼ ι₁ , subst-ρ-> ι₁>ι₂)
    nil ⟦ i / ι ⟧σ? = yes (nil , subst-[])
    (τ ∷ σ) ⟦ i / ι ⟧σ? with τ ⟦ i / ι ⟧τ? | σ ⟦ i / ι ⟧σ?
    ... | yes (τ' , sub-τ) | yes (σ' , sub-σ) =
      yes (τ' ∷ σ' , subst-∷ sub-τ sub-σ)
    ... | no ¬sub-τ | _ =
      no (λ { (._ , subst-∷ sub-τ sub-σ) → ¬sub-τ (_ , sub-τ) })
    ... | _ | no ¬sub-σ =
      no (λ { (._ , subst-∷ sub-τ sub-σ) → ¬sub-σ (_ , sub-σ) })

    _⟦_/_⟧Γ? : ∀ Γ i ι → Dec (∃ λ Γ' → Γ ⟦ i / ι ⟧Γ≡ Γ')
    registerₐ sp regs ⟦ i / ι ⟧Γ? with sp ⟦ i / ι ⟧σ? | regs ⟦ i / ι ⟧regs?
    ... | yes (sp' , sub-sp) | yes (regs' , sub-regs) =
      yes (registerₐ sp' regs' , subst-registerₐ sub-sp sub-regs)
    ... | no ¬sub-sp | _ =
      no (λ { (._ , subst-registerₐ sub-sp sub-regs) → ¬sub-sp (_ , sub-sp) })
    ... | _ | no ¬sub-regs = no
      (λ {(._ , subst-registerₐ sub-sp sub-regs) → ¬sub-regs (_ , sub-regs) })

    _⟦_/_⟧regs? : ∀ {m} (regs : Vec Type m) i ι →
                    Dec (∃ λ regs' → regs ⟦ i / ι ⟧regs≡ regs')
    [] ⟦ i / ι ⟧regs? = yes ([] , subst-[])
    (τ ∷ τs) ⟦ i / ι ⟧regs? with τ ⟦ i / ι ⟧τ? | τs ⟦ i / ι ⟧regs?
    ... | yes (τ' , sub-τ) | yes (τs' , sub-τs) =
      yes (τ' ∷ τs' , subst-∷ sub-τ sub-τs)
    ... | no ¬sub-τ | _ =
      no (λ { (._ , subst-∷ sub-τ sub-τs) → ¬sub-τ (_ , sub-τ) })
    ... | _ | no ¬sub-τs =
      no (λ { (._ , subst-∷ sub-τ sub-τs) → ¬sub-τs (_ , sub-τs) })

record Substitution (A : Set) : Set1 where
  constructor substitution
  field
    _⟦_/_⟧≡_ : A → InstantiationValue → AssignmentIndex → A → Set
    subst-unique : ∀ {v v₁ v₂ i ι} → v ⟦ i / ι ⟧≡ v₁ →
                                     v ⟦ i / ι ⟧≡ v₂ →
                                     v₁ ≡ v₂
    _⟦_/_⟧? : ∀ v i ι → Dec (∃ λ v' → v ⟦ i / ι ⟧≡ v')

-- These two should do the same, but they do not
-- open Substitution {{...}} public
infix 5 _⟦_/_⟧≡_ _⟦_/_⟧?
_⟦_/_⟧≡_ : ∀ {A} {{_ : Substitution A}} →
             A → InstantiationValue → AssignmentIndex → A → Set
_⟦_/_⟧≡_ {{s}} = Substitution._⟦_/_⟧≡_ s
subst-unique : ∀ {A} {{_ : Substitution A}} →
                 ∀ {v v₁ v₂ : A} {i ι} → v ⟦ i / ι ⟧≡ v₁ →
                                         v ⟦ i / ι ⟧≡ v₂ →
                                         v₁ ≡ v₂
subst-unique {{s}} = Substitution.subst-unique s
_⟦_/_⟧? : ∀ {A} {{_ : Substitution A}} →
             ∀ (v : A) i ι → Dec (∃ λ v' → v ⟦ i / ι ⟧≡ v')
_⟦_/_⟧? {{s}} = Substitution._⟦_/_⟧? s


instance
  Type-substitution : Substitution Type
  Type-substitution = substitution _⟦_/_⟧τ≡_ subst-τ-unique _⟦_/_⟧τ?

  InitType-substitution : Substitution InitType
  InitType-substitution = substitution _⟦_/_⟧τ⁻≡_ subst-τ⁻-unique _⟦_/_⟧τ⁻?

  StackType-substitution : Substitution StackType
  StackType-substitution = substitution _⟦_/_⟧σ≡_ subst-σ-unique _⟦_/_⟧σ?

  RegisterAssignment-substitution : Substitution RegisterAssignment
  RegisterAssignment-substitution =
    substitution _⟦_/_⟧Γ≡_ subst-Γ-unique _⟦_/_⟧Γ?

  Vec-substitution : ∀ {A} {m} {{s : Substitution A}} → Substitution (Vec A m)
  Vec-substitution = substitution
      _⟦_/_⟧xs≡_
      unique
      dec

    where _⟦_/_⟧xs≡_ : ∀ {A} {{s : Substitution A}} {m} →
                         Vec A m → InstantiationValue → AssignmentIndex →
                         Vec A m → Set
          xs ⟦ i / ι ⟧xs≡ xs' =
            Allᵥ (λ { (x , x') → x ⟦ i / ι ⟧≡ x' }) (Vec-zip xs xs')

          unique : ∀ {A i ι m} {xs xs₁ xs₂ : Vec A m}
                     {{s : Substitution A}} →
                     xs ⟦ i / ι ⟧xs≡ xs₁ →
                     xs ⟦ i / ι ⟧xs≡ xs₂ →
                     xs₁ ≡ xs₂
          unique {xs = []} {[]} {[]} [] [] = refl
          unique {xs = x ∷ xs} {x₁ ∷ xs₁} {x₂ ∷ xs₂} {{s}}
                 (sub-x₁ ∷ sub-xs₁) (sub-x₂ ∷ sub-xs₂) =
            cong₂ _∷_ (subst-unique sub-x₁ sub-x₂) (unique sub-xs₁ sub-xs₂)

          dec : ∀ {A m} {{s : Substitution A}} (xs : Vec A m) i ι →
                  Dec (∃ λ xs' → xs ⟦ i / ι ⟧xs≡ xs')
          dec [] i ι = yes ([] , [])
          dec (x ∷ xs) i ι with x ⟦ i / ι ⟧? | dec xs i ι
          dec (x ∷ xs) i ι | yes (x' , sub-x) | yes (xs' , sub-xs) =
            yes ((x' ∷ xs') , sub-x ∷ sub-xs)
          dec (x ∷ xs) i ι | no ¬sub-x | _ = no (help ¬sub-x)
            where help : ∀ {A} {{s : Substitution A}}
                           {i ι m x} {xs : Vec A m} →
                           ¬ (∃ λ x' → x ⟦ i / ι ⟧≡ x') →
                           ¬ (∃ λ xs' → (x ∷ xs) ⟦ i / ι ⟧xs≡ xs')
                  help ¬sub-x (x' ∷ xs' , sub-x ∷ sub-xs) = ¬sub-x (_ , sub-x)
          dec (x ∷ xs) i ι | _ | no ¬sub-xs = no (help ¬sub-xs)
            where help : ∀ {A} {{s : Substitution A}}
                           {i ι m x} {xs : Vec A m} →
                           ¬ (∃ λ xs' → xs ⟦ i / ι ⟧xs≡ xs') →
                           ¬ (∃ λ xs' → (x ∷ xs) ⟦ i / ι ⟧xs≡ xs')
                  help ¬sub-xs (x' ∷ xs' , sub-x ∷ sub-xs) =
                    ¬sub-xs (_ , sub-xs)

  List-substitution : ∀ {A} {{s : Substitution A}} → Substitution (List A)
  List-substitution = substitution
      _⟦_/_⟧xs≡_
      unique
      dec

    where _⟦_/_⟧xs≡_ : ∀ {A} {{s : Substitution A}} →
                         List A → InstantiationValue → AssignmentIndex →
                         List A → Set
          xs ⟦ i / ι ⟧xs≡ xs' =
            length xs ≡ length xs' ×
            All (λ { (x , x') → x ⟦ i / ι ⟧≡ x' }) (zip xs xs')

          unique : ∀ {A i ι} {xs xs₁ xs₂ : List A}
                     {{s : Substitution A}} →
                     xs ⟦ i / ι ⟧xs≡ xs₁ →
                     xs ⟦ i / ι ⟧xs≡ xs₂ →
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

          dec : ∀ {A} {{s : Substitution A}} (xs : List A) i ι →
                  Dec (∃ λ xs' → xs ⟦ i / ι ⟧xs≡ xs')
          dec [] i ι = yes ([] , (refl , []))
          dec (x ∷ xs) i ι with x ⟦ i / ι ⟧? | dec xs i ι
          dec (x ∷ xs) i ι | yes (x' , sub-x) | yes (xs' , (eq , sub-xs)) =
            yes (x' ∷ xs' , (cong suc eq) , sub-x ∷ sub-xs)
          dec (x ∷ xs) i ι | no ¬sub-x | _ = no (help ¬sub-x)
            where help : ∀ {A} {{s : Substitution A}}
                           {i ι x} {xs : List A} →
                           ¬ (∃ λ x' → x ⟦ i / ι ⟧≡ x') →
                           ¬ (∃ λ xs' → (x ∷ xs) ⟦ i / ι ⟧xs≡ xs')
                  help ¬sub-x ([] , () , _)
                  help ¬sub-x (x' ∷ xs' , (eq , sub-x ∷ sub-xs)) =
                    ¬sub-x (x' , sub-x)
          dec (x ∷ xs) i ι | _ | no ¬sub-xs = no (help ¬sub-xs)
            where help : ∀ {A} {{s : Substitution A}}
                           {i ι x} {xs : List A} →
                           ¬ (∃ λ xs' → xs ⟦ i / ι ⟧xs≡ xs') →
                           ¬ (∃ λ xs' → (x ∷ xs) ⟦ i / ι ⟧xs≡ xs')
                  help ¬sub-xs ([] , () , _)
                  help ¬sub-xs (x' ∷ xs' , eq , sub-x ∷ sub-xs) =
                    ¬sub-xs (xs' , (NP.cancel-+-left 1 eq) , sub-xs)
