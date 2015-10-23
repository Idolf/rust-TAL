open import Grammar
open import Util
import Data.Nat as N
import Data.Nat.Properties as NP
import Relation.Binary as B

wctx-length : WordValue → ℕ
wctx-length (globval l ♯a) = ♯a
wctx-length (w ⟦ inst i / ι ⟧) = pred (wctx-length w)
wctx-length (w ⟦ weaken Δ⁺ / ι ⟧) = length Δ⁺ + wctx-length w
wctx-length _ = 0

vctx-length : SmallValue → ℕ
vctx-length (word w) = wctx-length w
vctx-length (v ⟦ inst i / ι ⟧ᵥ) = pred (vctx-length v)
vctx-length (v ⟦ weaken Δ⁺ / ι ⟧ᵥ) = length Δ⁺ + vctx-length v
vctx-length _ = 0

mutual
  private

    substᵗ : Set → Set1
    substᵗ A = A → WeakCast → A → Set


  infix 3 _⟦_⟧n≡_
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

  infix 3 _⟦_⟧τ≡_
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

  infix 3 _⟦_⟧τ⁻≡_
  data _⟦_⟧τ⁻≡_ : substᵗ InitType where
    subst-τ⁻ :
            ∀ {φ τ τ' c} →
            τ ⟦ c ⟧τ≡ τ' →
      -------------------------
      (τ , φ) ⟦ c ⟧τ⁻≡ (τ' , φ)

  infix 3 _⟦_⟧τs⁻≡_
  _⟦_⟧τs⁻≡_ : substᵗ (List InitType)
  τs⁻ ⟦ c ⟧τs⁻≡ τs⁻' =
    AllZip (λ τ⁻ τ⁻' → τ⁻ ⟦ c ⟧τ⁻≡ τ⁻') τs⁻ τs⁻'

  infix 3 _⟦_⟧σ≡_
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

  infix 3 _⟦_⟧Γ≡_
  data _⟦_⟧Γ≡_ : substᵗ RegisterAssignment where
    subst-registerₐ :
              ∀ {regs regs' sp sp' c} →
                  sp ⟦ c ⟧σ≡ sp' →
               regs ⟦ c ⟧regs≡ regs' →
      ---------------------------------------------
      registerₐ sp regs ⟦ c ⟧Γ≡ registerₐ sp' regs'

  infix 3 _⟦_⟧regs≡_
  _⟦_⟧regs≡_ : ∀ {m} → substᵗ (Vec Type m)
  τs ⟦ c ⟧regs≡ τs' = AllZipᵥ (λ τ τ' → τ ⟦ c ⟧τ≡ τ') τs τs'

  infix 3 _⟦_⟧Δ≡_
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

  infix 3 _⟦_⟧a≡_
  data _⟦_⟧a≡_ : substᵗ TypeAssignmentValue where
    subst-α : ∀ {c} → α ⟦ c ⟧a≡ α
    subst-ρ : ∀ {c} → ρ ⟦ c ⟧a≡ ρ

  infix 3 _⟦_⟧i≡_
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

  infix 3 _⟦_⟧cᵥ≡_
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

  infix 3 _⟦_⟧c≡_
  data _⟦_⟧c≡_ : substᵗ StrongCast where
    subst-/ :
           ∀ {cᵥ₁ cᵥ₂ cᵥ ι₁ ι₁' ι₂} →
         cᵥ₁ ⟦ cᵥ / ι₁' ⟧cᵥ≡ cᵥ₂ →
              ι₁' ≡ ι₂ + ι₁ →
      -------------------------------
      cᵥ₁ / ι₂ ⟦ cᵥ / ι₁ ⟧c≡ cᵥ₂ / ι₂

  infix 3 _⟦_⟧w≡_
  data _⟦_⟧w≡_ : substᵗ WordValue where
    subst-globval :
               ∀ {l ♯a c} →
      ---------------------------------
      globval l ♯a ⟦ c ⟧w≡ globval l ♯a

    subst-heapval :
              ∀ {l c} →
      ---------------------------
      heapval l ⟦ c ⟧w≡ heapval l

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

    subst-⟦⟧ :
              ∀ {w₁ w₂ c₁ c₂ cᵥ ι} →
               w₁ ⟦ cᵥ / ι ⟧w≡ w₂ →
      c₁ ⟦ cᵥ / (wctx-length w₁ + ι) ⟧c≡ c₂ →
      ---------------------------------------
        (w₁ ⟦ c₁ ⟧) ⟦ cᵥ / ι ⟧w≡ (w₂ ⟦ c₂ ⟧)

  infix 3 _⟦_⟧v≡_
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

    subst-⟦⟧ :
             ∀ {v₁ v₂ c₁ c₂ cᵥ ι} →
              v₁ ⟦ cᵥ / ι ⟧v≡ v₂ →
       c₁ ⟦ cᵥ / (vctx-length v₁ + ι) ⟧c≡ c₂ →
      ----------------------------------------
       (v₁ ⟦ c₁ ⟧ᵥ) ⟦ cᵥ / ι ⟧v≡ (v₂ ⟦ c₂ ⟧ᵥ)

  infix 3 _⟦_⟧ι≡_
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
             ∀ {♯rs i c} →
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
      ---------------------------------------
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

  infix 3 _⟦_⟧I≡_
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
  subst-n-≢-inst : ∀ {i ι₁ ι₂} → ¬ (ι₁ ⟦ inst i / ι₁ ⟧n≡ ι₂)
  subst-n-≢-inst (subst-< ι₁<ι₁) = NP.1+n≰n ι₁<ι₁
  subst-n-≢-inst (subst-inst-> ι₁>ι₁) = NP.1+n≰n ι₁>ι₁

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
  infix 3 _⟦_⟧≡_ _⟦_⟧?

  weaken-0-unique : ∀ {v₁ v₂ ι} → v₁ ⟦ weaken W₀ / ι ⟧≡ v₂ →
                                  v₁ ≡ v₂
  weaken-0-unique {v₁} = subst-unique (weaken-0 v₁)

open Substitution {{...}} public

Vec-Substitution : ∀ {A W} {m} {{s : Substitution A W}} →
                     Substitution (Vec A m) W
Vec-Substitution {A} {W} = substitution
    W₀
    _⟦_⟧xs≡_
    unique
    weak
    dec
    xs-weaken-0

  where _⟦_⟧xs≡_ : ∀ {m} → Vec A m → Cast W → Vec A m → Set
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

        xs-weaken-0 : ∀ {m} (xs : Vec A m) {ι} → xs ⟦ weaken W₀ / ι ⟧xs≡ xs
        xs-weaken-0 [] = []
        xs-weaken-0 (x ∷ xs) = weaken-0 x ∷ xs-weaken-0 xs

List-Substitution : ∀ {A W} {{s : Substitution A W}} → Substitution (List A) W
List-Substitution {A} {W} = substitution
    W₀
    _⟦_⟧xs≡_
    unique
    weak
    dec
    xs-weaken-0

  where _⟦_⟧xs≡_ : List A → Cast W → List A → Set
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

        xs-weaken-0 : ∀ (xs : List A) {ι} → xs ⟦ weaken W₀ / ι ⟧xs≡ xs
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
  Instantiation-Substitution = substitution 0 _⟦_⟧i≡_ unique weak dec i-weaken-0
    where unique : ∀ {c} {i i₁ i₂} →
                     i ⟦ c ⟧i≡ i₁ →
                     i ⟦ c ⟧i≡ i₂ →
                     i₁ ≡ i₂
          unique (subst-α sub-τ₁) (subst-α sub-τ₂) = cong α (subst-unique sub-τ₁ sub-τ₂)
          unique (subst-ρ sub-σ₁) (subst-ρ sub-σ₂) = cong ρ (subst-unique sub-σ₁ sub-σ₂)

          weak : ∀ i w ι → ∃ λ i' → i ⟦ weaken w / ι ⟧i≡ i'
          weak (α τ) w ι = Σ-map α subst-α (can-weaken τ w ι)
          weak (ρ σ) w ι = Σ-map ρ subst-ρ (can-weaken σ w ι)

          dec : ∀ i c → Dec (∃ λ i' → i ⟦ c ⟧i≡ i')
          dec (α τ) c with τ ⟦ c ⟧?
          ... | yes (τ' , sub-τ) = yes (α τ' , subst-α sub-τ)
          ... | no ¬sub-τ = no (λ { (α τ' , subst-α sub-τ) → ¬sub-τ (τ' , sub-τ) })
          dec (ρ σ) c with σ ⟦ c ⟧?
          ... | yes (σ' , sub-σ) = yes (ρ σ' , subst-ρ sub-σ)
          ... | no ¬sub-σ = no (λ { (ρ σ' , subst-ρ sub-σ) → ¬sub-σ (σ' , sub-σ) })

          i-weaken-0 : ∀ i {ι} → i ⟦ weaken 0 / ι ⟧i≡ i
          i-weaken-0 (α τ) = subst-α (weaken-0 τ)
          i-weaken-0 (ρ σ) = subst-ρ (weaken-0 σ)

  StrongCastValue-Substitution : Substitution StrongCastValue ℕ
  StrongCastValue-Substitution = substitution 0 _⟦_⟧cᵥ≡_ unique weak dec cᵥ-weaken-0
    where unique : ∀ {c} {cᵥ cᵥ₁ cᵥ₂} →
                     cᵥ ⟦ c ⟧cᵥ≡ cᵥ₁ →
                     cᵥ ⟦ c ⟧cᵥ≡ cᵥ₂ →
                     cᵥ₁ ≡ cᵥ₂
          unique (subst-inst sub-i₁) (subst-inst sub-i₂) = cong inst (subst-unique sub-i₁ sub-i₂)
          unique (subst-weaken sub-Δ⁺₁) (subst-weaken sub-Δ⁺₂) = cong weaken (subst-unique sub-Δ⁺₁ sub-Δ⁺₂)

          weak : ∀ cᵥ w ι → ∃ λ cᵥ' → cᵥ ⟦ weaken w / ι ⟧cᵥ≡ cᵥ'
          weak (inst i) w ι = Σ-map inst subst-inst (can-weaken i w ι)
          weak (weaken Δ⁺) w ι = Σ-map weaken subst-weaken (can-weaken Δ⁺ w ι)

          dec : ∀ cᵥ c → Dec (∃ λ cᵥ' → cᵥ ⟦ c ⟧cᵥ≡ cᵥ')
          dec (inst i) c with i ⟦ c ⟧?
          ... | yes (i' , sub-i) = yes (inst i' , subst-inst sub-i)
          ... | no ¬sub-i = no (λ { (inst i' , subst-inst sub-i) → ¬sub-i (i' , sub-i) })
          dec (weaken Δ⁺) c with Δ⁺ ⟦ c ⟧?
          ... | yes (Δ⁺' , sub-Δ⁺) = yes (weaken Δ⁺' , subst-weaken sub-Δ⁺)
          ... | no ¬sub-Δ⁺ = no (λ { (weaken Δ⁺' , subst-weaken sub-Δ⁺) → ¬sub-Δ⁺ (Δ⁺' , sub-Δ⁺) })

          cᵥ-weaken-0 : ∀ cᵥ {ι} → cᵥ ⟦ weaken 0 / ι ⟧cᵥ≡ cᵥ
          cᵥ-weaken-0 (inst i) = subst-inst (weaken-0 i)
          cᵥ-weaken-0 (weaken Δ⁺) = subst-weaken (weaken-0 Δ⁺)

  StrongCast-Substitution : Substitution StrongCast ℕ
  StrongCast-Substitution = substitution 0 _⟦_⟧c≡_ unique weak dec c-weaken-0
    where unique : ∀ {c⋆} {c c₁ c₂} →
                     c ⟦ c⋆ ⟧c≡ c₁ →
                     c ⟦ c⋆ ⟧c≡ c₂ →
                     c₁ ≡ c₂
          unique (subst-/ sub-cᵥ₁ refl) (subst-/ sub-cᵥ₂ refl) = cong₂ _/_ (subst-unique sub-cᵥ₁ sub-cᵥ₂) refl

          weak : ∀ c w ι → ∃ λ c' → c ⟦ weaken w / ι ⟧c≡ c'
          weak (cᵥ / ι) w ι⋆ with can-weaken cᵥ w (ι + ι⋆)
          ... | cᵥ' , sub-cᵥ = cᵥ' / ι , subst-/ sub-cᵥ refl

          dec : ∀ c c⋆ → Dec (∃ λ c' → c ⟦ c⋆ ⟧c≡ c')
          dec (cᵥ / ι) (cᵥ⋆ / ι⋆) with cᵥ ⟦ cᵥ⋆ / ι + ι⋆ ⟧?
          ... | yes (cᵥ' , sub-cᵥ) = yes (cᵥ' / ι , subst-/ sub-cᵥ refl)
          ... | no ¬sub-cᵥ =
            no (λ { (cᵥ' / .ι , subst-/ sub-cᵥ refl) →
              ¬sub-cᵥ (cᵥ' , sub-cᵥ) })

          c-weaken-0 : ∀ c {ι} → c ⟦ weaken 0 / ι ⟧c≡ c
          c-weaken-0 (cᵥ / ι) = subst-/ (weaken-0 cᵥ) refl

  WordValue-Substitution : Substitution WordValue ℕ
  WordValue-Substitution = substitution 0 _⟦_⟧w≡_ unique weak dec w-weaken-0
    where unique : ∀ {c} {w w₁ w₂} →
                     w ⟦ c ⟧w≡ w₁ →
                     w ⟦ c ⟧w≡ w₂ →
                     w₁ ≡ w₂
          unique subst-globval subst-globval = refl
          unique subst-heapval subst-heapval = refl
          unique subst-const subst-const = refl
          unique subst-ns subst-ns = refl
          unique (subst-uninit sub-τ₁) (subst-uninit sub-τ₂) = cong uninit (subst-unique sub-τ₁ sub-τ₂)
          unique (subst-⟦⟧ sub-w₁ sub-c₁) (subst-⟦⟧ sub-w₂ sub-c₂)
            = cong₂ _⟦_⟧ (unique sub-w₁ sub-w₂) (subst-unique sub-c₁ sub-c₂)

          weak : ∀ w w⋆ ι → ∃ λ w' → w ⟦ weaken w⋆ / ι ⟧w≡ w'
          weak (globval l ♯a) w⋆ ι = globval l ♯a , subst-globval
          weak (heapval lₕ) w⋆ ι = heapval lₕ , subst-heapval
          weak (const n) w⋆ ι = const n , subst-const
          weak ns w⋆ ι = ns , subst-ns
          weak (uninit τ) w⋆ ι = Σ-map uninit subst-uninit (can-weaken τ w⋆ ι)
          weak (w ⟦ c ⟧) w⋆ ι = Σ-zip _⟦_⟧ subst-⟦⟧ (weak w w⋆ ι) (can-weaken c w⋆ (wctx-length w + ι))

          dec : ∀ w c → Dec (∃ λ w' → w ⟦ c ⟧w≡ w')
          dec (globval l ♯a) c = yes (globval l ♯a , subst-globval)
          dec (heapval lₕ) c = yes (heapval lₕ , subst-heapval)
          dec (const n) c = yes (const n , subst-const)
          dec ns c = yes (ns , subst-ns)
          dec (uninit τ) c with τ ⟦ c ⟧?
          ... | yes (τ' , sub-τ) = yes (uninit τ' , subst-uninit sub-τ)
          ... | no ¬sub-τ = no (λ { (uninit τ' , subst-uninit sub-τ) → ¬sub-τ (τ' , sub-τ) })
          dec (w ⟦ c ⟧) (cᵥ / ι) with dec w (cᵥ / ι) | c ⟦ cᵥ / (wctx-length w + ι) ⟧?
          ... | yes (w' , sub-w) | yes (c' , sub-c) = yes (w' ⟦ c' ⟧ , subst-⟦⟧ sub-w sub-c)
          ... | no ¬sub-w | _ = no (λ { (w' ⟦ c' ⟧ , subst-⟦⟧ sub-w sub-c ) → ¬sub-w (w' , sub-w)})
          ... | _ | no ¬sub-c = no (λ { (w' ⟦ c' ⟧ , subst-⟦⟧ sub-w sub-c ) → ¬sub-c (c' , sub-c)})

          w-weaken-0 : ∀ w {ι} → w ⟦ weaken 0 / ι ⟧w≡ w
          w-weaken-0 (globval l ♯a) = subst-globval
          w-weaken-0 (heapval lₕ) = subst-heapval
          w-weaken-0 (const n) = subst-const
          w-weaken-0 ns = subst-ns
          w-weaken-0 (uninit τ) = subst-uninit (weaken-0 τ)
          w-weaken-0 (w ⟦ c ⟧) = subst-⟦⟧ (w-weaken-0 w) (weaken-0 c)

  SmallValue-Substitution : Substitution SmallValue ℕ
  SmallValue-Substitution = substitution 0 _⟦_⟧v≡_ unique weak dec v-weaken-0
    where unique : ∀ {c} {v v₁ v₂} →
                     v ⟦ c ⟧v≡ v₁ →
                     v ⟦ c ⟧v≡ v₂ →
                     v₁ ≡ v₂
          unique subst-reg subst-reg = refl
          unique (subst-word sub-w₁) (subst-word sub-w₂) = cong word (subst-unique sub-w₁ sub-w₂)
          unique (subst-⟦⟧ sub-v₁ sub-c₁) (subst-⟦⟧ sub-v₂ sub-c₂)
            = cong₂ _⟦_⟧ᵥ (unique sub-v₁ sub-v₂) (subst-unique sub-c₁ sub-c₂)

          weak : ∀ v w ι → ∃ λ v' → v ⟦ weaken w / ι ⟧v≡ v'
          weak (reg ♯r) w ι = reg ♯r , subst-reg
          weak (word w) w⋆ ι = Σ-map word subst-word (can-weaken w w⋆ ι)
          weak (v ⟦ c ⟧ᵥ) w ι = Σ-zip _⟦_⟧ᵥ subst-⟦⟧ (weak v w ι) (can-weaken c w (vctx-length v + ι))

          dec : ∀ v c → Dec (∃ λ v' → v ⟦ c ⟧v≡ v')
          dec (reg ♯r) c = yes (reg ♯r , subst-reg)
          dec (word w) c with w ⟦ c ⟧?
          ... | yes (w' , sub-w) = yes (word w' , subst-word sub-w)
          ... | no ¬sub-w = no (λ { (word w' , subst-word sub-w) → ¬sub-w (w' , sub-w)})
          dec (v ⟦ c ⟧ᵥ) (cᵥ / ι) with dec v (cᵥ / ι) | c ⟦ cᵥ / vctx-length v + ι ⟧?
          ... | yes (v' , sub-v) | yes (c' , sub-c) = yes (v' ⟦ c' ⟧ᵥ , subst-⟦⟧ sub-v sub-c)
          ... | no ¬sub-v | _ = no (λ { (v' ⟦ c' ⟧ᵥ , subst-⟦⟧ sub-v sub-c) → ¬sub-v (v' , sub-v)})
          ... | _ | no ¬sub-c = no (λ { (v' ⟦ c' ⟧ᵥ , subst-⟦⟧ sub-v sub-c) → ¬sub-c (c' , sub-c)})

          v-weaken-0 : ∀ v {ι} → v ⟦ weaken 0 / ι ⟧v≡ v
          v-weaken-0 (reg ♯r) = λ {ι} → subst-reg
          v-weaken-0 (word w) = subst-word (weaken-0 w)
          v-weaken-0 (v ⟦ c ⟧ᵥ) = subst-⟦⟧ (v-weaken-0 v) (weaken-0 c)

  Instruction-Substitution : Substitution Instruction ℕ
  Instruction-Substitution = substitution 0 _⟦_⟧ι≡_ unique weak dec ι-weaken-0
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
          weak (add ♯rd ♯rs v) w ι⋆ = Σ-map (add ♯rd ♯rs) subst-add (can-weaken v w ι⋆)
          weak (sub ♯rd ♯rs v) w ι⋆ = Σ-map (sub ♯rd ♯rs) subst-sub (can-weaken v w ι⋆)
          weak (push v) w ι⋆ = Σ-map push subst-push (can-weaken v w ι⋆)
          weak pop w ι⋆ = pop , subst-pop
          weak (sld ♯rd i) w ι⋆ = sld ♯rd i , subst-sld
          weak (sst i ♯rs) w ι⋆ = sst i ♯rs , subst-sst
          weak (ld ♯rd ♯rs i) w ι⋆ = ld ♯rd ♯rs i , subst-ld
          weak (st ♯rd i ♯rs) w ι⋆ = st ♯rd i ♯rs , subst-st
          weak (malloc ♯rd τs) w ι⋆ = Σ-map (malloc ♯rd) subst-malloc (can-weaken τs w ι⋆)
          weak (mov ♯rd v) w ι⋆ = Σ-map (mov ♯rd) subst-mov (can-weaken v w ι⋆)
          weak (beq ♯r v) w ι⋆ = Σ-map (beq ♯r) subst-beq (can-weaken v w ι⋆)

          dec : ∀ ι c → Dec (∃ λ ι' → ι ⟦ c ⟧ι≡ ι')
          dec (add ♯rd ♯rs v) c
            with v ⟦ c ⟧?
          ... | yes (v' , sub-v) = yes (add ♯rd ♯rs v' , subst-add sub-v)
          ... | no ¬sub-v = no (λ { (add .♯rd .♯rs v' , subst-add sub-v) → ¬sub-v (v' , sub-v) })
          dec (sub ♯rd ♯rs v) c
            with v ⟦ c ⟧?
          ... | yes (v' , sub-v) = yes (sub ♯rd ♯rs v' , subst-sub sub-v)
          ... | no ¬sub-v = no (λ { (sub .♯rd .♯rs v' , subst-sub sub-v) → ¬sub-v (v' , sub-v) })
          dec (push v) c
            with v ⟦ c ⟧?
          ... | yes (v' , sub-v) = yes (push v' , subst-push sub-v)
          ... | no ¬sub-v = no (λ { (push v' , subst-push sub-v) → ¬sub-v (v' , sub-v) })
          dec pop c = yes (pop , subst-pop)
          dec (sld ♯rd i) c = yes (sld ♯rd i , subst-sld)
          dec (sst i ♯rs) c = yes (sst i ♯rs , subst-sst)
          dec (ld ♯rd ♯rs i) c = yes (ld ♯rd ♯rs i , subst-ld)
          dec (st ♯rd i ♯rs) c = yes (st ♯rd i ♯rs , subst-st)
          dec (malloc ♯rd τs) c
            with τs ⟦ c ⟧?
          ... | yes (τs' , sub-τs) = yes (malloc ♯rd τs' , subst-malloc sub-τs)
          ... | no ¬sub-τs = no (λ { (malloc .♯rd τs' , subst-malloc sub-τs) → ¬sub-τs (τs' , sub-τs) })
          dec (mov ♯rd v) c
            with v ⟦ c ⟧?
          ... | yes (v' , sub-v) = yes (mov ♯rd v' , subst-mov sub-v)
          ... | no ¬sub-v = no (λ { (mov .♯rd v' , subst-mov sub-v) → ¬sub-v (v' , sub-v) })
          dec (beq ♯r v) c
            with v ⟦ c ⟧?
          ... | yes (v' , sub-v) = yes (beq ♯r v' , subst-beq sub-v)
          ... | no ¬sub-v = no (λ { (beq .♯r v' , subst-beq sub-v) → ¬sub-v (v' , sub-v) })

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

  InstructionSequence-Substitution : Substitution InstructionSequence ℕ
  InstructionSequence-Substitution = substitution 0 _⟦_⟧I≡_ unique weak dec I-weaken-0
    where unique : ∀ {c} {I I₁ I₂} →
                     I ⟦ c ⟧I≡ I₁ →
                     I ⟦ c ⟧I≡ I₂ →
                     I₁ ≡ I₂
          unique (subst-~> sub-ι₁ sub-I₁) (subst-~> sub-ι₂ sub-I₂)
            = cong₂ _~>_ (subst-unique sub-ι₁ sub-ι₂) (unique sub-I₁ sub-I₂)
          unique (subst-jmp sub-v₁) (subst-jmp sub-v₂)
            = cong jmp (subst-unique sub-v₁ sub-v₂)

          weak : ∀ I w ι → ∃ λ I' → I ⟦ weaken w / ι ⟧I≡ I'
          weak (ι ~> I) w ι⋆ = Σ-zip _~>_ subst-~> (can-weaken ι w ι⋆) (weak I w ι⋆)
          weak (jmp v) w ι = Σ-map jmp subst-jmp (can-weaken v w ι)

          dec : ∀ I c → Dec (∃ λ I' → I ⟦ c ⟧I≡ I')
          dec (ι ~> I) c with ι ⟦ c ⟧? | dec I c
          ... | yes (ι' , sub-ι) | yes (I' , sub-I) = yes (ι' ~> I' , subst-~> sub-ι sub-I)
          ... | no ¬sub-ι | _ = no (λ { (ι' ~> I' , subst-~> sub-ι sub-I) → ¬sub-ι (ι' , sub-ι)})
          ... | _ | no ¬sub-I = no (λ { (ι' ~> I' , subst-~> sub-ι sub-I) → ¬sub-I (I' , sub-I)})
          dec (jmp v) c with v ⟦ c ⟧?
          ... | yes (v' , sub-v) = yes (jmp v' , subst-jmp sub-v)
          ... | no ¬sub-v = no (λ { (jmp v' , subst-jmp sub-v) → ¬sub-v (v' , sub-v)})

          I-weaken-0 : ∀ I {ι} → I ⟦ weaken 0 / ι ⟧I≡ I
          I-weaken-0 (ι ~> I) = subst-~> (weaken-0 ι) (I-weaken-0 I)
          I-weaken-0 (jmp v) = subst-jmp (weaken-0 v)

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


infix 3 Run_⟦_⟧≡_
data Run_⟦_⟧≡_ : TypeAssignment → StrongCast → TypeAssignment → Set where
  run-inst :
               ∀ {a Δ i} →
    -------------------------------
    Run a ∷ Δ ⟦ inst i / zero ⟧≡ Δ

  run-weaken :
               ∀ {Δ Δ⁺} →
    -----------------------------------
    Run Δ ⟦ weaken Δ⁺ / zero ⟧≡ Δ⁺ ++ Δ

  run-suc :
        ∀ {a a' : TypeAssignmentValue}
          {Δ Δ' : TypeAssignment}
          {cᵥ : StrongCastValue} {ι} →
         a ⟦ cᵥ / ι ⟧≡ a' →
         Run Δ ⟦ cᵥ / ι ⟧≡ Δ' →
    ---------------------------------
    Run a ∷ Δ ⟦ cᵥ / suc ι ⟧≡ a' ∷ Δ'

run-unique : ∀ {Δ Δ₁ Δ₂ c} →
               Run Δ ⟦ c ⟧≡ Δ₁ →
               Run Δ ⟦ c ⟧≡ Δ₂ →
               Δ₁ ≡ Δ₂
run-unique run-inst run-inst = refl
run-unique run-weaken run-weaken = refl
run-unique (run-suc sub-a₁ run-Δ₁) (run-suc sub-a₂ run-Δ₂) =
  cong₂ _∷_ (subst-unique {W = TypeAssignment} sub-a₁ sub-a₂)
            (run-unique run-Δ₁ run-Δ₂)

infix 3 Run_⟦_⟧?
Run_⟦_⟧? : ∀ Δ c → Dec (∃ λ Δ' → Run Δ ⟦ c ⟧≡ Δ')
Run [] ⟦ inst i / ι ⟧? = no (λ { (_ , ()) })
Run [] ⟦ weaken Δ⁺ / zero ⟧? = yes (Δ⁺ ++ [] , run-weaken)
Run [] ⟦ weaken Δ⁺ / suc ι ⟧? = no (λ { (_ , ()) })
Run a ∷ Δ ⟦ inst i / zero ⟧? = yes (Δ , run-inst)
Run a ∷ Δ ⟦ weaken Δ⁺ / zero ⟧? = yes (Δ⁺ ++ a ∷ Δ , run-weaken)
Run a ∷ Δ ⟦ cᵥ / suc ι ⟧? with a ⟦ cᵥ / ι ⟧? | Run Δ ⟦ cᵥ / ι ⟧?
... | yes (a' , sub-a) | yes (Δ' , run-Δ) = yes (a' ∷ Δ' , run-suc sub-a run-Δ)
... | no ¬sub-a | _ = no (λ { (a' ∷ Δ' , run-suc sub-a run-Δ) → ¬sub-a (a' , sub-a)})
... | _ | no ¬run-Δ = no (λ { (a' ∷ Δ' , run-suc sub-a run-Δ) → ¬run-Δ (Δ' , run-Δ)})
