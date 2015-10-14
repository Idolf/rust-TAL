open import Grammar
open import Util
import Data.Nat as N
import Data.Nat.Properties as NP
import Relation.Binary as B

mutual
  substᵗ : Set → Set1
  substᵗ A = A → WeakCast → A → Set

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
      α⁼ ι  ⟦ inst (α τ) / ι ⟧τ≡ τ'

    subst-α-inst-> :
                  ∀ {ι₁ ι₂ i} →
                  suc ι₁ > ι₂ →
      -------------------------------------
      α⁼ (suc ι₁) ⟦ inst i / ι₂ ⟧τ≡ α⁼ ι₁

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
            ∀ {Δ Δ' Γ Γ' cᵥ ι} →
            Δ ⟦ cᵥ / ι ⟧Δ≡ Δ' →
      Γ ⟦ cᵥ / length Δ + ι ⟧Γ≡ Γ' →
      -------------------------------
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
    subst-ρ-< :
           ∀ {ι₁ ι₂ cᵥ} →
             ι₁ < ι₂ →
      -----------------------
      ρ⁼ ι₁ ⟦ cᵥ / ι₂ ⟧σ≡ ρ⁼ ι₁

    subst-ρ-inst-≡ :
               ∀ {ι σ σ'} →
      σ ⟦ weaken ι / zero ⟧σ≡ σ' →
      ----------------------------
      ρ⁼ ι  ⟦ inst (ρ σ) / ι ⟧σ≡ σ'

    subst-ρ-inst-> :
                  ∀ {ι₁ ι₂ i} →
                  suc ι₁ > ι₂ →
      -------------------------------------
      ρ⁼ (suc ι₁) ⟦ inst i / ι₂ ⟧σ≡ ρ⁼ ι₁

    subst-ρ-weaken-≥ :
               ∀ {ι₁ ι₂ n} →
                 ι₁ ≥ ι₂ →
      -------------------------------------
      ρ⁼ ι₁ ⟦ weaken n / ι₂ ⟧σ≡ ρ⁼ (n + ι₁)

    subst-nil :
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

  infix 5 _⟦_⟧cᵥ≡_
  data _⟦_⟧cᵥ≡_ : substᵗ StrongCastValue where
    subst-inst :
           ∀ {i i' c} →
          i ⟦ c ⟧i≡ i' →
      -----------------------
      inst i ⟦ c ⟧cᵥ≡ inst i'

    subst-weaken :
             ∀ {Δ⁺ Δ⁺' c} →
            Δ⁺ ⟦ c ⟧Δ≡ Δ⁺' →
      -----------------------------
      weaken Δ⁺ ⟦ c ⟧cᵥ≡ weaken Δ⁺'

  infix 5 _⟦_⟧c≡_
  data _⟦_⟧c≡_ : substᵗ StrongCast where
    subst-/ :
         ∀ {cᵥ cᵥ' ι c} →
        cᵥ ⟦ c ⟧cᵥ≡ cᵥ' →
      ----------------------
      cᵥ / ι ⟦ c ⟧c≡ cᵥ' / ι

  infix 5 _⟦_⟧w≡_
  data _⟦_⟧w≡_ : substᵗ WordValue where
    subst-globval :
               ∀ {l c} →
      ---------------------------
      globval l ⟦ c ⟧w≡ globval l

    subst-heapval :
               ∀ {lₕ c} →
      -----------------------------
      heapval lₕ ⟦ c ⟧w≡ heapval lₕ

    subst-const :
            ∀ {n c} →
      -----------------------
      const n ⟦ c ⟧w≡ const n

    subst-ns :
        ∀ {c} →
      -------------
      ns ⟦ c ⟧w≡ ns

    subst-uninit :
             ∀ {τ τ' c} →
            τ ⟦ c ⟧τ≡ τ' →
      --------------------------
      uninit τ ⟦ c ⟧w≡ uninit τ'

    subst-inst :
             ∀ {w₁ w₂ c₁ c₂ c} →
               w₁ ⟦ c ⟧w≡ w₂ →
               c₁ ⟦ c ⟧c≡ c₂ →
      -------------------------------
      (w₁ ⟦ c₁ ⟧) ⟦ c ⟧w≡ (w₂ ⟦ c₂ ⟧)

  infix 5 _⟦_⟧v≡_
  data _⟦_⟧v≡_ : substᵗ SmallValue where
    subst-reg :
           ∀ {♯r c} →
      ---------------------
      reg ♯r ⟦ c ⟧v≡ reg ♯r

    subst-word :
           ∀ {w w' c} →
          w ⟦ c ⟧w≡ w' →
      ----------------------
      word w ⟦ c ⟧v≡ word w'

    subst-inst :
             ∀ {v₁ v₂ c₁ c₂ c} →
               v₁ ⟦ c ⟧v≡ v₂ →
               c₁ ⟦ c ⟧c≡ c₂ →
      -------------------------------
      (v₁ ⟦ c₁ ⟧ᵥ) ⟦ c ⟧v≡ (v₂ ⟦ c₂ ⟧ᵥ)

  infix 5 _⟦_⟧ι≡_
  data _⟦_⟧ι≡_ : substᵗ Instruction where
    subst-add :
              ∀ {♯rd ♯rs v v' c} →
                v ⟦ c ⟧v≡ v' →
      ------------------------------------
      add ♯rd ♯rs v ⟦ c ⟧ι≡ add ♯rd ♯rs v'

    subst-sub :
              ∀ {♯rd ♯rs v v' c} →
                v ⟦ c ⟧v≡ v' →
      ------------------------------------
      sub ♯rd ♯rs v ⟦ c ⟧ι≡ sub ♯rd ♯rs v'

    subst-push :
           ∀ {v v' c} →
          v ⟦ c ⟧v≡ v' →
      ----------------------
      push v ⟦ c ⟧ι≡ push v'

    subst-pop :
         ∀ {c} →
      ---------------
      pop ⟦ c ⟧ι≡ pop

    subst-sld :
            ∀ {♯rd i c} →
      ---------------------------
      sld ♯rd i ⟦ c ⟧ι≡ sld ♯rd i

    subst-sst :
             ∀ {i ♯rs c} →
      ---------------------------
      sst i ♯rs ⟦ c ⟧ι≡ sst i ♯rs

    subst-ld :
              ∀ {♯rd ♯rs i c} →
      ---------------------------------
      ld ♯rd ♯rs i ⟦ c ⟧ι≡ ld ♯rd ♯rs i

    subst-st :
              ∀ {♯rd ♯rs i c} →
      ---------------------------------
      st ♯rd i ♯rs ⟦ c ⟧ι≡ st ♯rd i ♯rs

    subst-malloc :
                  ∀ {♯rd τs τs' c} →
      AllZip (λ τ τ' → τ ⟦ c ⟧τ≡ τ') τs τs' →
      -----------------------------------------
        malloc ♯rd τs ⟦ c ⟧ι≡ malloc ♯rd τs'

    subst-mov :
           ∀ {♯rd v v' c} →
            v ⟦ c ⟧v≡ v' →
      ----------------------------
      mov ♯rd v ⟦ c ⟧ι≡ mov ♯rd v'

    subst-beq :
           ∀ {♯r v v' c} →
           v ⟦ c ⟧v≡ v' →
      --------------------------
      beq ♯r v ⟦ c ⟧ι≡ beq ♯r v'

  infix 5 _⟦_⟧I≡_
  data _⟦_⟧I≡_ : substᵗ InstructionSequence where
    subst-~> :
         ∀ {ι ι' I I' c} →
           ι ⟦ c ⟧ι≡ ι' →
           I ⟦ c ⟧I≡ I' →
      -----------------------
      ι ~> I ⟦ c ⟧I≡ ι' ~> I'

    subst-jmp :
         ∀ {v v' c} →
         v ⟦ c ⟧v≡ v' →
      --------------------
      jmp v ⟦ c ⟧I≡ jmp v'

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
      with NP.1+n≰n (Nat-≤-trans ι₁≥sucι₂ ι₁≤sucι₂)
    ... | ()
    subst-τ-unique (subst-α-inst-≡ sub-τ) (subst-α-< ι<ι)
      with NP.1+n≰n ι<ι
    ... | ()
    subst-τ-unique (subst-α-inst-≡ sub-τ) (subst-α-inst-≡ sub-τ') =
      subst-τ-unique sub-τ sub-τ'
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
      with NP.1+n≰n (Nat-≤-trans ι₁≥sucι₂ ι₁≤sucι₂)
    ... | ()
    subst-τ-unique (subst-α-weaken-≥ ι₁≥ι₂) (subst-α-weaken-≥ ι₁≥ι₂') = refl
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
    subst-σ-unique (subst-ρ-< ι₁<ι₂) (subst-ρ-< ι₁<ι₂') = refl
    subst-σ-unique (subst-ρ-< ι<ι) (subst-ρ-inst-≡ sub-σ)
      with NP.1+n≰n ι<ι
    ... | ()
    subst-σ-unique (subst-ρ-< ι₁<ι₂) (subst-ρ-inst-> ι₁>ι₂)
      with NP.1+n≰n (NP.<-trans ι₁<ι₂ ι₁>ι₂)
    ... | ()
    subst-σ-unique (subst-ρ-< (s≤s ι₁≤sucι₂)) (subst-ρ-weaken-≥ ι₁≥sucι₂)
      with NP.1+n≰n (Nat-≤-trans ι₁≥sucι₂ ι₁≤sucι₂)
    ... | ()
    subst-σ-unique (subst-ρ-inst-≡ sub-σ) (subst-ρ-< ι<ι)
      with NP.1+n≰n ι<ι
    ... | ()
    subst-σ-unique (subst-ρ-inst-≡ sub-σ) (subst-ρ-inst-≡ sub-σ') =
      subst-σ-unique sub-σ sub-σ'
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
      with NP.1+n≰n (Nat-≤-trans ι₁≥sucι₂ ι₁≤sucι₂)
    ... | ()
    subst-σ-unique (subst-ρ-weaken-≥ ι₁≥ι₂) (subst-ρ-weaken-≥ ι₁≥ι₂') = refl
    subst-σ-unique subst-nil subst-nil = refl
    subst-σ-unique (subst-∷ sub-τ₁ sub-σ₁) (subst-∷ sub-τ₂ sub-σ₂) =
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
    can-weaken-τ : ∀ τ n ι → ∃ λ τ' → τ ⟦ weaken n / ι ⟧τ≡ τ'
    can-weaken-τ (α⁼ ι₁) n ι₂ with ι₂ ≤? ι₁
    ... | yes ι₁≥ι₂ = α⁼ (n + ι₁) , subst-α-weaken-≥ ι₁≥ι₂
    ... | no ι₁≱ι₂ = α⁼ ι₁ , subst-α-< (NP.≰⇒> ι₁≱ι₂)
    can-weaken-τ int n ι = int , subst-int
    can-weaken-τ ns n ι = ns , subst-ns
    can-weaken-τ (∀[ Δ ] Γ) n ι with can-weaken-Δ Δ n ι
                                   | can-weaken-Γ Γ n (length Δ + ι)
    ... | Δ' , sub-Δ | Γ' , sub-Γ = ∀[ Δ' ] Γ' , subst-∀ sub-Δ sub-Γ
    can-weaken-τ (tuple τs) n ι with can-weaken-τs⁻ τs n ι
    ... | τs' , sub-τs = tuple τs' , subst-tuple sub-τs

    can-weaken-τ⁻ : ∀ τ⁻ n ι → ∃ λ τ⁻' → τ⁻ ⟦ weaken n / ι ⟧τ⁻≡ τ⁻'
    can-weaken-τ⁻ (τ , φ) n ι with can-weaken-τ τ n ι
    ... | τ' , sub-τ = (τ' , φ) , subst-τ⁻ sub-τ

    can-weaken-τs⁻ : ∀ τs⁻ n ι → ∃ λ τs⁻' → τs⁻ ⟦ weaken n / ι ⟧τs⁻≡ τs⁻'
    can-weaken-τs⁻ [] n ι = [] , []
    can-weaken-τs⁻ (τ⁻ ∷ τs⁻) n ι
      with can-weaken-τ⁻ τ⁻ n ι | can-weaken-τs⁻ τs⁻ n ι
    ... | τ⁻' , sub-τ⁻ | τs⁻' , sub-τs⁻ = τ⁻' ∷ τs⁻' , sub-τ⁻ ∷ sub-τs⁻

    can-weaken-σ : ∀ σ n ι → ∃ λ σ' → σ ⟦ weaken n / ι ⟧σ≡ σ'
    can-weaken-σ (ρ⁼ ι₁) n ι₂ with ι₂ ≤? ι₁
    ... | yes ι₁≥ι₂ = ρ⁼ (n + ι₁) , subst-ρ-weaken-≥ ι₁≥ι₂
    ... | no ι₁≱ι₂ = ρ⁼ ι₁ , subst-ρ-< (NP.≰⇒> ι₁≱ι₂)
    can-weaken-σ nil n ι = nil , subst-nil
    can-weaken-σ (τ ∷ σ) n ι with can-weaken-τ τ n ι | can-weaken-σ σ n ι
    ... | τ' , sub-τ | σ' , sub-σ = τ' ∷ σ' , subst-∷ sub-τ sub-σ

    can-weaken-Γ : ∀ Γ n ι → ∃ λ Γ' → Γ ⟦ weaken n / ι ⟧Γ≡ Γ'
    can-weaken-Γ (registerₐ sp regs) n ι
      with can-weaken-σ sp n ι | can-weaken-regs regs n ι
    ... | sp' , sub-sp | regs' , sub-regs =
          registerₐ sp' regs' , subst-registerₐ sub-sp sub-regs

    can-weaken-regs : ∀ {m} (regs : Vec Type m) n ι →
                        ∃ λ regs' → regs ⟦ weaken n / ι ⟧regs≡ regs'
    can-weaken-regs [] n ι = [] , []
    can-weaken-regs (τ ∷ τs) n ι
      with can-weaken-τ τ n ι | can-weaken-regs τs n ι
    ... | τ' , sub-τ | τs' , sub-τs = τ' ∷ τs' , sub-τ ∷ sub-τs

    can-weaken-Δ : ∀ Δ n ι → ∃ λ Δ' → Δ ⟦ weaken n / ι ⟧Δ≡ Δ'
    can-weaken-Δ [] n ι = [] , []
    can-weaken-Δ (a ∷ Δ) n ι with can-weaken-a a n (length Δ + ι)
                                | can-weaken-Δ Δ n ι
    ... | a' , sub-a | Δ' , sub-Δ = a' ∷ Δ' , sub-a ∷ sub-Δ

    can-weaken-a : ∀ a n ι → ∃ λ a' → a ⟦ weaken n / ι ⟧a≡ a'
    can-weaken-a α n ι = α , subst-α
    can-weaken-a ρ n ι = ρ , subst-ρ

  mutual
    _⟦_⟧τ? : ∀ τ c → Dec (∃ λ τ' → τ ⟦ c ⟧τ≡ τ')
    α⁼ ι₁ ⟦ cᵥ / ι₂ ⟧τ? with Nat-cmp ι₁ ι₂
    α⁼ ι₁ ⟦ cᵥ / ι₂ ⟧τ? | tri< ι₁<ι₂ _ _ = yes (α⁼ ι₁ , subst-α-< ι₁<ι₂)
    α⁼ ι  ⟦ inst (α τ) / .ι ⟧τ? | tri≈ _ refl _ with can-weaken-τ τ ι 0
    ... | τ' , sub-τ = yes (τ' , subst-α-inst-≡ sub-τ)
    α⁼ ι  ⟦ inst (ρ σ) / .ι ⟧τ? | tri≈ _ refl _ = no help
      where help : ∀ {ι σ} → ¬ (∃ λ τ' → α⁼ ι ⟦ inst (ρ σ) / ι ⟧τ≡ τ')
            help (._ , subst-α-< ι<ι) = NP.1+n≰n ι<ι
            help (._ , subst-α-inst-> ι>ι) = NP.1+n≰n ι>ι
    α⁼ ι  ⟦ weaken n / .ι ⟧τ? | tri≈ _ refl _ =
      yes (α⁼ (n + ι) , subst-α-weaken-≥ (Nat-≤-refl ι))
    α⁼ zero ⟦ inst i / ι₂ ⟧τ? | tri> _ _ ()
    α⁼ (suc ι₁) ⟦ inst i / ι₂ ⟧τ? | tri> _ _ sucι₁>ι₂ =
      yes (α⁼ ι₁ , subst-α-inst-> sucι₁>ι₂)
    α⁼ ι₁ ⟦ weaken n / ι₂ ⟧τ? | tri> _ _ ι₁>ι₂ =
      yes (α⁼ (n + ι₁) , subst-α-weaken-≥ (NP.≤⇒pred≤ _ _ ι₁>ι₂))
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
    ρ⁼ ι₁ ⟦ cᵥ / ι₂ ⟧σ? with Nat-cmp ι₁ ι₂
    ρ⁼ ι₁ ⟦ cᵥ / ι₂ ⟧σ? | tri< ι₁<ι₂ _ _ = yes (ρ⁼ ι₁ , subst-ρ-< ι₁<ι₂)
    ρ⁼ ι  ⟦ inst (ρ σ) / .ι ⟧σ? | tri≈ _ refl _ with can-weaken-σ σ ι 0
    ... | σ' , sub-σ = yes (σ' , subst-ρ-inst-≡ sub-σ)
    ρ⁼ ι  ⟦ inst (α τ) / .ι ⟧σ? | tri≈ _ refl _ = no help
      where help : ∀ {ι τ} → ¬ (∃ λ σ' → ρ⁼ ι ⟦ inst (α τ) / ι ⟧σ≡ σ')
            help (._ , subst-ρ-< ι<ι) = NP.1+n≰n ι<ι
            help (._ , subst-ρ-inst-> ι>ι) = NP.1+n≰n ι>ι
    ρ⁼ ι  ⟦ weaken n / .ι ⟧σ? | tri≈ _ refl _ =
      yes (ρ⁼ (n + ι) , subst-ρ-weaken-≥ (Nat-≤-refl ι))
    ρ⁼ zero ⟦ inst i / ι₂ ⟧σ? | tri> _ _ ()
    ρ⁼ (suc ι₁) ⟦ inst i / ι₂ ⟧σ? | tri> _ _ sucι₁>ι₂ =
      yes (ρ⁼ ι₁ , subst-ρ-inst-> sucι₁>ι₂)
    ρ⁼ ι₁ ⟦ weaken n / ι₂ ⟧σ? | tri> _ _ ι₁>ι₂ =
      yes (ρ⁼ (n + ι₁) , subst-ρ-weaken-≥ (NP.≤⇒pred≤ _ _ ι₁>ι₂))
    nil ⟦ c ⟧σ? = yes (nil , subst-nil)
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
    τ-weaken-0 : ∀ τ {ι} → τ ⟦ weaken 0 / ι ⟧τ≡ τ
    τ-weaken-0 (α⁼ ι₁) {ι₂} with suc ι₁ ≤? ι₂
    ... | yes ι₁<ι₂ = subst-α-< ι₁<ι₂
    ... | no ι₁≮ι₂ with NP.≰⇒> ι₁≮ι₂
    ... | s≤s ι₁≥ι₂ = subst-α-weaken-≥ ι₁≥ι₂
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
    σ-weaken-0 (ρ⁼ ι₁) {ι₂} with suc ι₁ ≤? ι₂
    ... | yes ι₁<ι₂ = subst-ρ-< ι₁<ι₂
    ... | no ι₁≮ι₂ with NP.≰⇒> ι₁≮ι₂
    ... | s≤s ι₁≥ι₂ = subst-ρ-weaken-≥ ι₁≥ι₂
    σ-weaken-0 nil = subst-nil
    σ-weaken-0 (τ ∷ σ) = subst-∷ (τ-weaken-0 τ) (σ-weaken-0 σ)

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

  Instantiation-Substitution : Substitution Instantiation ℕ
  Instantiation-Substitution = substitution 0
      _⟦_⟧i≡_ unique can-weak dec weak0
    where unique : ∀ {i i₁ i₂ c} →
                     i ⟦ c ⟧i≡ i₁ →
                     i ⟦ c ⟧i≡ i₂ →
                     i₁ ≡ i₂
          unique (subst-α sub-τ₁) (subst-α sub-τ₂) =
            cong α (subst-unique sub-τ₁ sub-τ₂)
          unique (subst-ρ sub-σ₁) (subst-ρ sub-σ₂) =
            cong ρ (subst-unique sub-σ₁ sub-σ₂)

          can-weak : ∀ i w ι →
                       ∃ λ i' → i ⟦ weaken w / ι ⟧i≡ i'
          can-weak (α τ) w ι with can-weaken τ w ι
          ... | τ' , sub-τ = α τ' , subst-α sub-τ
          can-weak (ρ σ) w ι with can-weaken σ w ι
          ... | σ' , sub-σ = ρ σ' , subst-ρ sub-σ

          dec : ∀ i c → Dec (∃ λ i' → i ⟦ c ⟧i≡ i')
          dec (α τ) c with τ ⟦ c ⟧?
          ... | yes (τ' , sub-τ) = yes (α τ' , subst-α sub-τ)
          ... | no ¬sub-τ =
            no (λ { (α τ' , subst-α sub-τ) → ¬sub-τ (τ' , sub-τ) })
          dec (ρ σ) c with σ ⟦ c ⟧?
          ... | yes (σ' , sub-σ) = yes (ρ σ' , subst-ρ sub-σ)
          ... | no ¬sub-σ =
            no (λ { (ρ σ' , subst-ρ sub-σ) → ¬sub-σ (σ' , sub-σ) })

          weak0 : ∀ i {ι} → i ⟦ weaken 0 / ι ⟧i≡ i
          weak0 (α τ) = subst-α (weaken-0 τ)
          weak0 (ρ σ) = subst-ρ (weaken-0 σ)

  StrongCastValue-Substitution : Substitution StrongCastValue ℕ
  StrongCastValue-Substitution = substitution 0
      _⟦_⟧cᵥ≡_ unique can-weak dec weak0
    where unique : ∀ {cᵥ cᵥ₁ cᵥ₂ c} →
                     cᵥ ⟦ c ⟧cᵥ≡ cᵥ₁ →
                     cᵥ ⟦ c ⟧cᵥ≡ cᵥ₂ →
                     cᵥ₁ ≡ cᵥ₂
          unique (subst-inst sub-i₁) (subst-inst sub-i₂) =
            cong inst (subst-unique sub-i₁ sub-i₂)
          unique (subst-weaken sub-Δ⁺₁) (subst-weaken sub-Δ⁺₂) =
            cong weaken (subst-unique sub-Δ⁺₁ sub-Δ⁺₂)

          can-weak : ∀ cᵥ w ι →
                       ∃ λ cᵥ' → cᵥ ⟦ weaken w / ι ⟧cᵥ≡ cᵥ'
          can-weak (inst i) w ι with can-weaken i w ι
          ... | i' , sub-i = inst i' , subst-inst sub-i
          can-weak (weaken Δ⁺) w ι with can-weaken Δ⁺ w ι
          ... | Δ⁺' , sub-Δ⁺ = weaken Δ⁺' , subst-weaken sub-Δ⁺

          dec : ∀ cᵥ c → Dec (∃ λ cᵥ' → cᵥ ⟦ c ⟧cᵥ≡ cᵥ')
          dec (inst i) c with i ⟦ c ⟧?
          ... | yes (i' , sub-i) = yes (inst i' , subst-inst sub-i)
          ... | no ¬sub-i =
            no (λ { (inst i' , subst-inst sub-i) → ¬sub-i (i' , sub-i) })
          dec (weaken Δ⁺) c with Δ⁺ ⟦ c ⟧?
          ... | yes (Δ⁺' , sub-Δ⁺) = yes (weaken Δ⁺' , subst-weaken sub-Δ⁺)
          ... | no ¬sub-Δ⁺ =
            no (λ {
              (weaken Δ⁺' , subst-weaken sub-Δ⁺) → ¬sub-Δ⁺ (Δ⁺' , sub-Δ⁺)
            })

          weak0 : ∀ cᵥ {ι} → cᵥ ⟦ weaken 0 / ι ⟧cᵥ≡ cᵥ
          weak0 (inst i) = subst-inst (weaken-0 i)
          weak0 (weaken Δ⁺) = subst-weaken (weaken-0 Δ⁺)

  StrongCast-Substitution : Substitution StrongCast ℕ
  StrongCast-Substitution = substitution 0 _⟦_⟧c≡_ unique can-weak dec weak0
    where unique : ∀ {c c₁ c₂ c⋆} →
                     c ⟦ c⋆ ⟧c≡ c₁ →
                     c ⟦ c⋆ ⟧c≡ c₂ →
                     c₁ ≡ c₂
          unique (subst-/ sub-cᵥ₁) (subst-/ sub-cᵥ₂) =
            cong₂ _/_ (subst-unique sub-cᵥ₁ sub-cᵥ₂) refl

          can-weak : ∀ c w ι →
                       ∃ λ c' → c ⟦ weaken w / ι ⟧c≡ c'
          can-weak (cᵥ / ι₁) w ι₂ with can-weaken cᵥ w ι₂
          ... | cᵥ' , sub-cᵥ = cᵥ' / ι₁ , subst-/ sub-cᵥ

          dec : ∀ c c⋆ → Dec (∃ λ c' → c ⟦ c⋆ ⟧c≡ c')
          dec (cᵥ / ι) c⋆ with cᵥ ⟦ c⋆ ⟧?
          ... | yes (cᵥ' , sub-cᵥ) = yes (cᵥ' / ι , subst-/ sub-cᵥ)
          ... | no ¬sub-cᵥ =
            no (λ { (cᵥ' / .ι , subst-/ sub-cᵥ) → ¬sub-cᵥ (cᵥ' , sub-cᵥ) })

          weak0 : ∀ c {ι} → c ⟦ weaken 0 / ι ⟧c≡ c
          weak0 (cᵥ / ι) = subst-/ (weaken-0 cᵥ)

  WordValue-Substitution : Substitution WordValue ℕ
  WordValue-Substitution = substitution 0 _⟦_⟧w≡_ unique can-weak dec weak0
    where unique : ∀ {w w₁ w₂ c} →
                     w ⟦ c ⟧w≡ w₁ →
                     w ⟦ c ⟧w≡ w₂ →
                     w₁ ≡ w₂
          unique subst-globval subst-globval = refl
          unique subst-heapval subst-heapval = refl
          unique subst-const subst-const = refl
          unique subst-ns subst-ns = refl
          unique (subst-uninit sub-τ₁) (subst-uninit sub-τ₂) =
            cong uninit (subst-unique sub-τ₁ sub-τ₂)
          unique (subst-inst sub-w₁ sub-i₁) (subst-inst sub-w₂ sub-i₂) =
            cong₂ _⟦_⟧ (unique sub-w₁ sub-w₂) (subst-unique sub-i₁ sub-i₂)
          can-weak : ∀ w n ι →
                       ∃ λ w' → w ⟦ weaken n / ι ⟧w≡ w'
          can-weak (globval l) n ι = globval l , subst-globval
          can-weak (heapval lₕ) n ι = heapval lₕ , subst-heapval
          can-weak (const n₁) n₂ ι = const n₁ , subst-const
          can-weak ns n ι = ns , subst-ns
          can-weak (uninit τ) n ι with can-weaken τ n ι
          ... | τ' , sub-τ = uninit τ' , subst-uninit sub-τ
          can-weak (w ⟦ i ⟧) n ι with can-weak w n ι | can-weaken i n ι
          ... | w' , sub-w | i' , sub-i = w' ⟦ i' ⟧ , subst-inst sub-w sub-i
          dec : ∀ w c → Dec (∃ λ w' → w ⟦ c ⟧w≡ w')
          dec (globval l) c = yes (globval l , subst-globval)
          dec (heapval lₕ) c = yes (heapval lₕ , subst-heapval)
          dec (const n) c = yes (const n , subst-const)
          dec ns c = yes (ns , subst-ns)
          dec (uninit τ) c with τ ⟦ c ⟧?
          ... | yes (τ' , sub-τ) = yes (uninit τ' , subst-uninit sub-τ)
          ... | no ¬sub-τ =
            no (λ { (uninit τ' , subst-uninit sub-τ) → ¬sub-τ (τ' , sub-τ) })
          dec (w ⟦ i ⟧) c with dec w c | i ⟦ c ⟧?
          ... | yes (w' , sub-w) | yes (i' , sub-i) =
            yes (w' ⟦ i' ⟧ , subst-inst sub-w sub-i)
          ... | no ¬sub-w | _ =
            no (λ {
              (w' ⟦ i' ⟧ , subst-inst sub-w sub-i) → ¬sub-w (w' , sub-w)
            })
          ... | _ | no ¬sub-i =
            no (λ {
              (w' ⟦ i' ⟧ , subst-inst sub-w sub-i) → ¬sub-i (i' , sub-i)
            })
          weak0 : ∀ w {ι} → w ⟦ weaken 0 / ι ⟧w≡ w
          weak0 (globval l) = subst-globval
          weak0 (heapval lₕ) = subst-heapval
          weak0 (const n) = subst-const
          weak0 ns = subst-ns
          weak0 (uninit τ) = subst-uninit (weaken-0 τ)
          weak0 (w ⟦ i ⟧) = subst-inst (weak0 w) (weaken-0 i)

  SmallValue-Substitution : Substitution SmallValue ℕ
  SmallValue-Substitution = substitution 0 _⟦_⟧v≡_ unique can-weak dec weak0
    where unique : ∀ {v v₁ v₂ c} →
                     v ⟦ c ⟧v≡ v₁ →
                     v ⟦ c ⟧v≡ v₂ →
                     v₁ ≡ v₂
          unique subst-reg subst-reg = refl
          unique (subst-word sub-w₁) (subst-word sub-w₂) =
            cong word (subst-unique sub-w₁ sub-w₂)
          unique (subst-inst sub-v₁ sub-i₁) (subst-inst sub-v₂ sub-i₂) =
            cong₂ _⟦_⟧ᵥ (unique sub-v₁ sub-v₂) (subst-unique sub-i₁ sub-i₂)
          can-weak : ∀ v n ι →
                       ∃ λ v' → v ⟦ weaken n / ι ⟧v≡ v'
          can-weak (reg ♯r) n ι = reg ♯r , subst-reg
          can-weak (word w) n ι with can-weaken w n ι
          ... | w' , sub-w = word w' , subst-word sub-w
          can-weak (v ⟦ i ⟧ᵥ) n ι with can-weak v n ι | can-weaken i n ι
          ... | v' , sub-v | i' , sub-i = v' ⟦ i' ⟧ᵥ , subst-inst sub-v sub-i
          dec : ∀ v c → Dec (∃ λ v' → v ⟦ c ⟧v≡ v')
          dec (reg ♯r) c = yes (reg ♯r , subst-reg)
          dec (word w) c with w ⟦ c ⟧?
          ... | yes (w' , sub-w) = yes (word w' , subst-word sub-w)
          ... | no ¬sub-w =
            no (λ {(word w' , subst-word sub-w) → ¬sub-w (w' , sub-w)})
          dec (v ⟦ i ⟧ᵥ) c with dec v c | i ⟦ c ⟧?
          ... | yes (v' , sub-v) | yes (i' , sub-i) =
            yes (v' ⟦ i' ⟧ᵥ , subst-inst sub-v sub-i)
          ... | no ¬sub-v | _ =
            no (λ {
              (v' ⟦ i' ⟧ᵥ , subst-inst sub-v sub-i) → ¬sub-v (v' , sub-v)
            })
          ... | _ | no ¬sub-i =
            no (λ {
              (v' ⟦ i' ⟧ᵥ , subst-inst sub-v sub-i) → ¬sub-i (i' , sub-i)
            })
          weak0 : ∀ v {ι} → v ⟦ weaken 0 / ι ⟧v≡ v
          weak0 (reg ♯r) = subst-reg
          weak0 (word w) = subst-word (weaken-0 w)
          weak0 (v ⟦ i ⟧ᵥ) = subst-inst (weak0 v) (weaken-0 i)

  Instruction-Substitution : Substitution Instruction ℕ
  Instruction-Substitution = substitution 0 _⟦_⟧ι≡_ unique can-weak dec weak0
    where unique : ∀ {ι ι₁ ι₂ c} →
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
          unique (subst-malloc sub-τs₁) (subst-malloc sub-τs₂) =
            cong₂ malloc refl (subst-unique sub-τs₁ sub-τs₂)
          unique (subst-mov sub-v₁) (subst-mov sub-v₂)
            rewrite subst-unique sub-v₁ sub-v₂ = refl
          unique (subst-beq sub-v₁) (subst-beq sub-v₂)
            rewrite subst-unique sub-v₁ sub-v₂ = refl

          can-weak : ∀ ι n ι⋆ →
                       ∃ λ ι' → ι ⟦ weaken n / ι⋆ ⟧ι≡ ι'
          can-weak (add ♯rd ♯rs v) n ι⋆
            with can-weaken v n ι⋆
          ... | v' , sub-v = add ♯rd ♯rs v' , subst-add sub-v
          can-weak (sub ♯rd ♯rs v) n ι⋆
            with can-weaken v n ι⋆
          ... | v' , sub-v = sub ♯rd ♯rs v' , subst-sub sub-v
          can-weak (push v) n ι⋆
            with can-weaken v n ι⋆
          ... | v' , sub-v = push v' , subst-push sub-v
          can-weak pop n ι⋆ = pop , subst-pop
          can-weak (sld ♯rd i) n ι⋆ = sld ♯rd i , subst-sld
          can-weak (sst i ♯rs) n ι⋆ = sst i ♯rs , subst-sst
          can-weak (ld ♯rd ♯rs i) n ι⋆ = ld ♯rd ♯rs i , subst-ld
          can-weak (st ♯rd i ♯rs) n ι⋆ = st ♯rd i ♯rs , subst-st
          can-weak (malloc ♯rd τs) n ι⋆
            with can-weaken τs n ι⋆
          ... | τs' , sub-τs = malloc ♯rd τs' , subst-malloc sub-τs
          can-weak (mov ♯rd v) n ι⋆
            with can-weaken v n ι⋆
          ... | v' , sub-v = mov ♯rd v' , subst-mov sub-v
          can-weak (beq ♯r v) n ι⋆
            with can-weaken v n ι⋆
          ... | v' , sub-v = beq ♯r v' , subst-beq sub-v

          dec : ∀ ι c → Dec (∃ λ ι' → ι ⟦ c ⟧ι≡ ι')
          dec (add ♯rd ♯rs v) c
            with v ⟦ c ⟧?
          ... | yes (v' , sub-v) = yes (add ♯rd ♯rs v' , subst-add sub-v)
          ... | no ¬sub-v =
            no (λ {(._ , subst-add sub-v) → ¬sub-v (_ , sub-v) })
          dec (sub ♯rd ♯rs v) c
            with v ⟦ c ⟧?
          ... | yes (v' , sub-v) = yes (sub ♯rd ♯rs v' , subst-sub sub-v)
          ... | no ¬sub-v =
            no (λ {(._ , subst-sub sub-v) → ¬sub-v (_ , sub-v) })
          dec (push v) c
            with v ⟦ c ⟧?
          ... | yes (v' , sub-v) = yes (push v' , subst-push sub-v)
          ... | no ¬sub-v =
            no (λ {(._ , subst-push sub-v) → ¬sub-v (_ , sub-v) })
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
            no (λ {
              (._ , subst-malloc sub-τs) → ¬sub-τs (_ , sub-τs)
            })
          dec (mov ♯rd v) c
            with v ⟦ c ⟧?
          ... | yes (v' , sub-v) = yes (mov ♯rd v' , subst-mov sub-v)
          ... | no ¬sub-v =
            no (λ {(._ , subst-mov sub-v) → ¬sub-v (_ , sub-v) })
          dec (beq ♯r v) c
            with v ⟦ c ⟧?
          ... | yes (v' , sub-v) = yes (beq ♯r v' , subst-beq sub-v)
          ... | no ¬sub-v =
            no (λ {(._ , subst-beq sub-v) → ¬sub-v (_ , sub-v) })

          weak0 : ∀ ι {ι⋆} → ι ⟦ weaken 0 / ι⋆ ⟧ι≡ ι
          weak0 (add ♯rd ♯rs v) = subst-add (weaken-0 v)
          weak0 (sub ♯rd ♯rs v) = subst-sub (weaken-0 v)
          weak0 (push v) = subst-push (weaken-0 v)
          weak0 pop = subst-pop
          weak0 (sld ♯rd i) = subst-sld
          weak0 (sst i ♯rs) = subst-sst
          weak0 (ld ♯rd ♯rs i) = subst-ld
          weak0 (st ♯rd i ♯rs) = subst-st
          weak0 (malloc ♯rd τs) = subst-malloc (weaken-0 τs)
          weak0 (mov ♯rd v) = subst-mov (weaken-0 v)
          weak0 (beq ♯r v) = subst-beq (weaken-0 v)

  InstructionSequence-Substitution : Substitution InstructionSequence ℕ
  InstructionSequence-Substitution = substitution 0
      _⟦_⟧I≡_ unique can-weak dec weak0
    where unique : ∀ {I I₁ I₂ c} →
                     I ⟦ c ⟧I≡ I₁ →
                     I ⟦ c ⟧I≡ I₂ →
                     I₁ ≡ I₂
          unique (subst-~> sub-ι₁ sub-I₁) (subst-~> sub-ι₂ sub-I₂) =
            cong₂ _~>_ (subst-unique sub-ι₁ sub-ι₂) (unique sub-I₁ sub-I₂)
          unique (subst-jmp sub-v₁) (subst-jmp sub-v₂) =
            cong jmp (subst-unique sub-v₁ sub-v₂)
          can-weak : ∀ I n ι →
                       ∃ λ I' → I ⟦ weaken n / ι ⟧I≡ I'
          can-weak (ι ~> I) n ι⋆ with can-weaken ι n ι⋆ | can-weak I n ι⋆
          ... | ι' , sub-ι | I' , sub-I = ι' ~> I' , subst-~> sub-ι sub-I
          can-weak (jmp v) n ι with can-weaken v n ι
          ... | v' , sub-v = jmp v' , subst-jmp sub-v
          dec : ∀ I c → Dec (∃ λ I' → I ⟦ c ⟧I≡ I')
          dec (ι ~> I) c with ι ⟦ c ⟧? | dec I c
          ... | yes (ι' , sub-ι) | yes (I' , sub-I) =
            yes (ι' ~> I' , subst-~> sub-ι sub-I)
          ... | no ¬sub-ι | _ =
            no (λ { (ι' ~> I' , subst-~> sub-ι sub-I) → ¬sub-ι (ι' , sub-ι) })
          ... | _ | no ¬sub-I =
            no (λ { (ι' ~> I' , subst-~> sub-ι sub-I) → ¬sub-I (I' , sub-I) })
          dec (jmp v) c with v ⟦ c ⟧?
          ... | yes (v' , sub-v) = yes (jmp v' , subst-jmp sub-v)
          ... | no ¬sub-v =
            no (λ { (jmp v' , subst-jmp sub-v) → ¬sub-v (v' , sub-v) })
          weak0 : ∀ I {ι} → I ⟦ weaken 0 / ι ⟧I≡ I
          weak0 (ι ~> I) = subst-~> (weaken-0 ι) (weak0 I)
          weak0 (jmp v) = subst-jmp (weaken-0 v)

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
