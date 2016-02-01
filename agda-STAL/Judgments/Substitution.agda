module Judgments.Substitution where

open import Util
open import Judgments.Grammar
open HighGrammar

-- The purpose of this file is
-- to include instances of this record.
-- While weaken could have been expressed
-- as a judgment, it was easier to make it
-- a function.
record Substitution (A : Set) : Set1 where
  constructor substitution
  infix 3 _⟦_/_⟧≡_
  field
    weaken : ℕ → ℕ → A → A
    _⟦_/_⟧≡_ : A → Instantiation → ℕ → A → Set
  infix 3 _⟦_/_⟧many≡_
  infixr 5 _∷_
  data _⟦_/_⟧many≡_ : A → Instantiations → ℕ → A → Set where
    [] :
           ∀ {v n} →
      -------------------
      v ⟦ [] / n ⟧many≡ v

    _∷_ :
        ∀ {v v' vₑ i is n} →
         v ⟦ i / n ⟧≡ v' →
       v' ⟦ is / n ⟧many≡ vₑ →
      ------------------------
      v ⟦ i ∷ is / n ⟧many≡ vₑ
open Substitution {{...}} public

data InstantiationMatch : Instantiation → TypeAssumptionValue → Set where
  match-α : ∀ {τ} → InstantiationMatch (α τ) α
  match-ρ : ∀ {σ} → InstantiationMatch (ρ σ) ρ

mutual
  weaken-τ : ℕ → ℕ → Type → Type
  weaken-τ pos inc (α⁼ ι) with pos ≤? ι
  ... | yes pos≤ι = α⁼ (inc + ι)
  ... | no pos≰ι = α⁼ ι
  weaken-τ pos inc int = int
  weaken-τ pos inc ns = ns
  weaken-τ pos inc (∀[ Δ ] Γ) = ∀[ Δ ] (weaken-Γ (length Δ + pos) inc Γ)
  weaken-τ pos inc (tuple τs⁻) = tuple (weaken-τs⁻ pos inc τs⁻)

  weaken-τ⁻ : ℕ → ℕ → InitType → InitType
  weaken-τ⁻ pos inc (τ , φ) = weaken-τ pos inc τ , φ

  weaken-τs⁻ : ℕ → ℕ → List InitType → List InitType
  weaken-τs⁻ pos inc [] = []
  weaken-τs⁻ pos inc (τ⁻ ∷ τs⁻) = weaken-τ⁻ pos inc τ⁻ ∷ weaken-τs⁻ pos inc τs⁻

  weaken-σ : ℕ → ℕ → StackType → StackType
  weaken-σ pos inc (ρ⁼ ι) with pos ≤? ι
  ... | yes pos≤ι = ρ⁼ (inc + ι)
  ... | no pos≰ι = ρ⁼ ι
  weaken-σ pos inc [] = []
  weaken-σ pos inc (τ ∷ σ) = weaken-τ pos inc τ ∷ weaken-σ pos inc σ

  weaken-Γ : ℕ → ℕ → RegisterAssignment → RegisterAssignment
  weaken-Γ pos inc (registerₐ sp regs) = registerₐ (weaken-σ pos inc sp) (weaken-regs pos inc regs)

  weaken-regs : ∀ {n} → ℕ → ℕ → Vec Type n → Vec Type n
  weaken-regs pos inc [] = []
  weaken-regs pos inc (τ ∷ τs) = weaken-τ pos inc τ ∷ weaken-regs pos inc τs

  weaken-i : ℕ → ℕ → Instantiation → Instantiation
  weaken-i pos inc (α τ) = α (weaken-τ pos inc τ)
  weaken-i pos inc (ρ σ) = ρ (weaken-σ pos inc σ)

  weaken-is : ℕ → ℕ → Instantiations → Instantiations
  weaken-is pos inc [] = []
  weaken-is pos inc (i ∷ is) = weaken-i (length is + pos) inc i ∷ weaken-is pos inc is

mutual
  infix 3 _⟦_/_⟧τ≡_
  data _⟦_/_⟧τ≡_ : Type → Instantiation → ℕ → Type → Set where
    subst-α-> :
              ∀ {ι₁ ι₂ i} →
                ι₁ > ι₂ →
      -------------------------------
      α⁼ ι₁ ⟦ i / ι₂ ⟧τ≡ α⁼ (pred ι₁)

    subst-α-≡ :
            ∀ {τ ι} →
      ---------------------------------
      α⁼ ι ⟦ α τ / ι ⟧τ≡ weaken-τ 0 ι τ

    subst-α-< :
          ∀ {ι₁ ι₂ i} →
            ι₁ < ι₂ →
      ------------------------
      α⁼ ι₁ ⟦ i / ι₂ ⟧τ≡ α⁼ ι₁


    subst-int :
            ∀ {i ι} →
      -------------------
      int ⟦ i / ι ⟧τ≡ int

    subst-ns :
           ∀ {i ι} →
      -----------------
      ns ⟦ i / ι ⟧τ≡ ns

    subst-∀ :
              ∀ {Δ Γ Γ' i ι} →
      Γ ⟦ i / length Δ + ι ⟧Γ≡ Γ' →
      ------------------------------
      ∀[ Δ ] Γ ⟦ i / ι ⟧τ≡ ∀[ Δ ] Γ'

    subst-tuple :
            ∀ {i ι τs τs'} →
           τs ⟦ i / ι ⟧τs⁻≡ τs' →
      ------------------------------
      tuple τs ⟦ i / ι ⟧τ≡ tuple τs'

  infix 3 _⟦_/_⟧τ⁻≡_
  data _⟦_/_⟧τ⁻≡_ : InitType → Instantiation → ℕ → InitType → Set where
    subst-τ⁻ :
             ∀ {φ τ τ' i ι} →
            τ ⟦ i / ι ⟧τ≡ τ' →
      -----------------------------
      (τ , φ) ⟦ i / ι ⟧τ⁻≡ (τ' , φ)

  infix 3 _⟦_/_⟧τs⁻≡_
  _⟦_/_⟧τs⁻≡_ : List InitType → Instantiation → ℕ → List InitType → Set
  τs⁻ ⟦ i / ι ⟧τs⁻≡ τs⁻' =
    AllZip (λ τ⁻ τ⁻' → τ⁻ ⟦ i / ι ⟧τ⁻≡ τ⁻') τs⁻ τs⁻'

  infix 3 _⟦_/_⟧σ≡_
  infixr 5 _∷_
  data _⟦_/_⟧σ≡_ : StackType → Instantiation → ℕ → StackType → Set where
    subst-ρ-> :
              ∀ {ι₁ ι₂ i} →
                ι₁ > ι₂ →
      -------------------------------
      ρ⁼ ι₁ ⟦ i / ι₂ ⟧σ≡ ρ⁼ (pred ι₁)

    subst-ρ-≡ :
                  ∀ {σ ι} →
      ---------------------------------
      ρ⁼ ι ⟦ ρ σ / ι ⟧σ≡ weaken-σ 0 ι σ

    subst-ρ-< :
            ∀ {ι₁ ι₂ i} →
              ι₁ < ι₂ →
      ------------------------
      ρ⁼ ι₁ ⟦ i / ι₂ ⟧σ≡ ρ⁼ ι₁

    [] :
          ∀ {i ι} →
      -----------------
      [] ⟦ i / ι ⟧σ≡ []

    _∷_ :
         ∀ {τ τ' σ σ' i ι} →
          τ ⟦ i / ι ⟧τ≡ τ' →
          σ ⟦ i / ι ⟧σ≡ σ' →
      -------------------------
      τ ∷ σ ⟦ i / ι ⟧σ≡ τ' ∷ σ'

  infix 3 _⟦_/_⟧Γ≡_
  data _⟦_/_⟧Γ≡_ : RegisterAssignment → Instantiation → ℕ →
                   RegisterAssignment → Set where
    subst-registerₐ :
                 ∀ {regs regs' sp sp' i ι} →
                     sp ⟦ i / ι ⟧σ≡ sp' →
                  regs ⟦ i / ι ⟧regs≡ regs' →
      -------------------------------------------------
      registerₐ sp regs ⟦ i / ι ⟧Γ≡ registerₐ sp' regs'

  infix 3 _⟦_/_⟧regs≡_
  _⟦_/_⟧regs≡_ : ∀ {m} → Vec Type m → Instantiation → ℕ → Vec Type m → Set
  τs ⟦ i / ι ⟧regs≡ τs' = AllZipᵥ (λ τ τ' → τ ⟦ i / ι ⟧τ≡ τ') τs τs'

infix 3 _⟦_/_⟧i≡_
data _⟦_/_⟧i≡_ : Instantiation → Instantiation → ℕ → Instantiation → Set where
  subst-α :
      ∀ {τ τ' i ι} →
     τ ⟦ i / ι ⟧τ≡ τ' →
    --------------------
    α τ ⟦ i / ι ⟧i≡ α τ'

  subst-ρ :
      ∀ {σ σ' i ι} →
     σ ⟦ i / ι ⟧σ≡ σ' →
    --------------------
    ρ σ ⟦ i / ι ⟧i≡ ρ σ'

infix 3 _⟦_/_⟧is≡_
data _⟦_/_⟧is≡_ : Instantiations → Instantiation → ℕ → Instantiations → Set where
  [] :
        ∀ {i ι} →
    ------------------
    [] ⟦ i / ι ⟧is≡ []

  _∷_ :
         ∀ {i ι i₁ i₂ is₁ is₂} →
    i₁ ⟦ i / length is₁ + ι ⟧i≡ i₂ →
         is₁ ⟦ i / ι ⟧is≡ is₂ →
    --------------------------------
     i₁ ∷ is₁ ⟦ i / ι ⟧is≡ i₂ ∷ is₂

infix 3 _⟦_/_⟧v≡_
data _⟦_/_⟧v≡_ : SmallValueₕ → Instantiation → ℕ → SmallValueₕ → Set where
  subst-reg :
          ∀ {♯r i ι} →
    -------------------------
    reg ♯r ⟦ i / ι ⟧v≡ reg ♯r

  subst-globval :
             ∀ {l i ι} →
    -------------------------------
    globval l ⟦ i / ι ⟧v≡ globval l

  subst-int :
         ∀ {n i ι} →
    -----------------------
    int n ⟦ i / ι ⟧v≡ int n

  subst-ns :
       ∀ {i ι} →
    -----------------
    ns ⟦ i / ι ⟧v≡ ns

  subst-uninit :
           ∀ {τ τ' i ι} →
          τ ⟦ i / ι ⟧τ≡ τ' →
    ------------------------------
    uninit τ ⟦ i / ι ⟧v≡ uninit τ'

  subst-Λ :
                ∀ {Δ v v' is is' i ι} →
                  v ⟦ i / ι ⟧v≡ v' →
           is ⟦ i / length Δ + ι ⟧is≡ is' →
    ----------------------------------------------
    (Λ Δ ∙ v ⟦ is ⟧) ⟦ i / ι ⟧v≡ (Λ Δ ∙ v' ⟦ is' ⟧)

infix 3 _⟦_/_⟧ι≡_
data _⟦_/_⟧ι≡_ : Instructionₕ → Instantiation → ℕ → Instructionₕ → Set where
  subst-add :
           ∀ {♯rd ♯rs v v' i ι} →
               v ⟦ i / ι ⟧v≡ v' →
    ------------------------------------
    add ♯rd ♯rs v ⟦ i / ι ⟧ι≡ add ♯rd ♯rs v'

  subst-sub :
           ∀ {♯rd ♯rs v v' i ι} →
               v ⟦ i / ι ⟧v≡ v' →
    ------------------------------------
    sub ♯rd ♯rs v ⟦ i / ι ⟧ι≡ sub ♯rd ♯rs v'

  subst-salloc :
             ∀ {n i ι} →
    -----------------------------
    salloc n ⟦ i / ι ⟧ι≡ salloc n

  subst-sfree :
             ∀ {n i ι} →
    ---------------------------
    sfree n ⟦ i / ι ⟧ι≡ sfree n

  subst-sld :
           ∀ {♯rd pos i ι} →
    ---------------------------
    sld ♯rd pos ⟦ i / ι ⟧ι≡ sld ♯rd pos

  subst-sst :
           ∀ {♯rs pos i ι} →
    -----------------------------------
    sst pos ♯rs ⟦ i / ι ⟧ι≡ sst pos ♯rs

  subst-ld :
             ∀ {♯rd ♯rs pos i ι} →
    -----------------------------------------
    ld ♯rd ♯rs pos ⟦ i / ι ⟧ι≡ ld ♯rd ♯rs pos

  subst-st :
             ∀ {♯rd ♯rs pos i ι} →
    ---------------------------------
    st ♯rd pos ♯rs ⟦ i / ι ⟧ι≡ st ♯rd pos ♯rs

  subst-malloc :
             ∀ {♯rd τs τs' i ι} →
    AllZip (λ τ τ' → τ ⟦ i / ι ⟧τ≡ τ') τs τs' →
    ---------------------------------------
      malloc ♯rd τs ⟦ i / ι ⟧ι≡ malloc ♯rd τs'

  subst-mov :
         ∀ {♯rd v v' i ι} →
          v ⟦ i / ι ⟧v≡ v' →
    ----------------------------
    mov ♯rd v ⟦ i / ι ⟧ι≡ mov ♯rd v'

  subst-beq :
          ∀ {♯r v v' i ι} →
           v ⟦ i / ι ⟧v≡ v' →
    --------------------------
    beq ♯r v ⟦ i / ι ⟧ι≡ beq ♯r v'

infix 3 _⟦_/_⟧I≡_
data _⟦_/_⟧I≡_ : InstructionSequenceₕ → Instantiation → ℕ →
                 InstructionSequenceₕ → Set where
  subst-~> :
        ∀ {ι ι' I I' i ιₚ} →
         ι ⟦ i / ιₚ ⟧ι≡ ι' →
         I ⟦ i / ιₚ ⟧I≡ I' →
    -----------------------
    ι ~> I ⟦ i / ιₚ ⟧I≡ ι' ~> I'

  subst-jmp :
        ∀ {v v' i ι} →
       v ⟦ i / ι ⟧v≡ v' →
    --------------------
    jmp v ⟦ i / ι ⟧I≡ jmp v'

  subst-halt :
          ∀ {i ι} →
    ---------------------
    halt ⟦ i / ι ⟧I≡ halt

Vec-Substitution : ∀ A {{S : Substitution A}} m → Substitution (Vec A m)
Vec-Substitution A m =
    substitution weaken-xs (λ xs i ι xs' → AllZipᵥ (λ x x' → x ⟦ i / ι ⟧≡ x') xs xs')
  where weaken-xs : ∀ {n} → ℕ → ℕ → Vec A n → Vec A n
        weaken-xs pos inc [] = []
        weaken-xs pos inc (x ∷ xs) = weaken pos inc x ∷ weaken-xs pos inc xs

List-Substitution : ∀ A {{s : Substitution A}} → Substitution (List A)
List-Substitution A =
    substitution weaken-xs (λ xs i ι xs' → AllZip (λ x x' → x ⟦ i / ι ⟧≡ x') xs xs')
  where weaken-xs : ℕ → ℕ → List A → List A
        weaken-xs pos inc [] = []
        weaken-xs pos inc (x ∷ xs) = weaken pos inc x ∷ weaken-xs pos inc xs

instance
  Type-Substitution : Substitution Type
  Type-Substitution = substitution weaken-τ _⟦_/_⟧τ≡_

  TypeVec-Substitution : ∀ {n} → Substitution (Vec Type n)
  TypeVec-Substitution = substitution weaken-regs _⟦_/_⟧regs≡_

  TypeList-Substitution : Substitution (List Type)
  TypeList-Substitution = List-Substitution Type

  InitType-Substitution : Substitution InitType
  InitType-Substitution = substitution weaken-τ⁻ _⟦_/_⟧τ⁻≡_

  InitTypeVec-Substitution : ∀ {n} → Substitution (Vec InitType n)
  InitTypeVec-Substitution = Vec-Substitution InitType _

  InitTypeList-Substitution : Substitution (List InitType)
  InitTypeList-Substitution = substitution weaken-τs⁻ _⟦_/_⟧τs⁻≡_

  StackType-Substitution : Substitution StackType
  StackType-Substitution = substitution weaken-σ _⟦_/_⟧σ≡_

  RegisterAssignment-Substitution : Substitution RegisterAssignment
  RegisterAssignment-Substitution = substitution weaken-Γ _⟦_/_⟧Γ≡_

  Instantiation-Substitution : Substitution Instantiation
  Instantiation-Substitution = substitution weaken-i _⟦_/_⟧i≡_

  Instantiations-Substitution : Substitution Instantiations
  Instantiations-Substitution = substitution weaken-is _⟦_/_⟧is≡_

  SmallValue-Substitution : Substitution SmallValueₕ
  SmallValue-Substitution = substitution weaken-v _⟦_/_⟧v≡_
    where weaken-v : ℕ → ℕ → SmallValueₕ → SmallValueₕ
          weaken-v pos inc (reg ♯r) = reg ♯r
          weaken-v pos inc (globval l) = globval l
          weaken-v pos inc (int i) = int i
          weaken-v pos inc ns = ns
          weaken-v pos inc (uninit τ) = uninit (weaken pos inc τ)
          weaken-v pos inc (Λ Δ ∙ v ⟦ is ⟧) = Λ Δ ∙ weaken-v pos inc v ⟦ weaken (length Δ + pos) inc is ⟧

  Instruction-Substitution : Substitution Instructionₕ
  Instruction-Substitution = substitution weaken-ι _⟦_/_⟧ι≡_
    where weaken-ι : ℕ → ℕ → Instructionₕ → Instructionₕ
          weaken-ι pos inc (add ♯rd ♯rs v) = add ♯rd ♯rs (weaken pos inc v)
          weaken-ι pos inc (sub ♯rd ♯rs v) = sub ♯rd ♯rs (weaken pos inc v)
          weaken-ι pos inc (salloc i) = salloc i
          weaken-ι pos inc (sfree i) = sfree i
          weaken-ι pos inc (sld ♯rd i) = sld ♯rd i
          weaken-ι pos inc (sst i ♯rs) = sst i ♯rs
          weaken-ι pos inc (ld ♯rd ♯rs i) = ld ♯rd ♯rs i
          weaken-ι pos inc (st ♯rd i ♯rs) = st ♯rd i ♯rs
          weaken-ι pos inc (malloc ♯rd τs) = malloc ♯rd (weaken pos inc τs)
          weaken-ι pos inc (mov ♯rd v) = mov ♯rd (weaken pos inc v)
          weaken-ι pos inc (beq ♯r v) = beq ♯r (weaken pos inc v)

  InstructionSequence-Substitution : Substitution InstructionSequenceₕ
  InstructionSequence-Substitution = substitution weaken-I _⟦_/_⟧I≡_
    where weaken-I : ℕ → ℕ → InstructionSequenceₕ → InstructionSequenceₕ
          weaken-I pos inc (ι ~> I) = weaken pos inc ι ~> weaken-I pos inc I
          weaken-I pos inc (jmp v) = jmp (weaken pos inc v)
          weaken-I pos inc halt = halt
