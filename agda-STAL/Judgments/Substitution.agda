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
        ∀ {v v' vₑ θ θs n} →
         v ⟦ θ / n ⟧≡ v' →
       v' ⟦ θs / n ⟧many≡ vₑ →
      ------------------------
      v ⟦ θ ∷ θs / n ⟧many≡ vₑ
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

  weaken-θ : ℕ → ℕ → Instantiation → Instantiation
  weaken-θ pos inc (α τ) = α (weaken-τ pos inc τ)
  weaken-θ pos inc (ρ σ) = ρ (weaken-σ pos inc σ)

  weaken-θs : ℕ → ℕ → Instantiations → Instantiations
  weaken-θs pos inc [] = []
  weaken-θs pos inc (θ ∷ θs) = weaken-θ (length θs + pos) inc θ ∷ weaken-θs pos inc θs

mutual
  infix 3 _⟦_/_⟧τ≡_
  data _⟦_/_⟧τ≡_ : Type → Instantiation → ℕ → Type → Set where
    subst-α-> :
              ∀ {ι₁ ι₂ θ} →
                ι₁ > ι₂ →
      -------------------------------
      α⁼ ι₁ ⟦ θ / ι₂ ⟧τ≡ α⁼ (pred ι₁)

    subst-α-≡ :
            ∀ {τ ι} →
      ---------------------------------
      α⁼ ι ⟦ α τ / ι ⟧τ≡ weaken-τ 0 ι τ

    subst-α-< :
          ∀ {ι₁ ι₂ θ} →
            ι₁ < ι₂ →
      ------------------------
      α⁼ ι₁ ⟦ θ / ι₂ ⟧τ≡ α⁼ ι₁


    subst-int :
            ∀ {θ ι} →
      -------------------
      int ⟦ θ / ι ⟧τ≡ int

    subst-ns :
           ∀ {θ ι} →
      -----------------
      ns ⟦ θ / ι ⟧τ≡ ns

    subst-∀ :
              ∀ {Δ Γ Γ' θ ι} →
      Γ ⟦ θ / length Δ + ι ⟧Γ≡ Γ' →
      ------------------------------
      ∀[ Δ ] Γ ⟦ θ / ι ⟧τ≡ ∀[ Δ ] Γ'

    subst-tuple :
            ∀ {θ ι τs τs'} →
           τs ⟦ θ / ι ⟧τs⁻≡ τs' →
      ------------------------------
      tuple τs ⟦ θ / ι ⟧τ≡ tuple τs'

  infix 3 _⟦_/_⟧τ⁻≡_
  data _⟦_/_⟧τ⁻≡_ : InitType → Instantiation → ℕ → InitType → Set where
    subst-τ⁻ :
             ∀ {φ τ τ' θ ι} →
            τ ⟦ θ / ι ⟧τ≡ τ' →
      -----------------------------
      (τ , φ) ⟦ θ / ι ⟧τ⁻≡ (τ' , φ)

  infix 3 _⟦_/_⟧τs⁻≡_
  _⟦_/_⟧τs⁻≡_ : List InitType → Instantiation → ℕ → List InitType → Set
  τs⁻ ⟦ θ / ι ⟧τs⁻≡ τs⁻' =
    AllZip (λ τ⁻ τ⁻' → τ⁻ ⟦ θ / ι ⟧τ⁻≡ τ⁻') τs⁻ τs⁻'

  infix 3 _⟦_/_⟧σ≡_
  infixr 5 _∷_
  data _⟦_/_⟧σ≡_ : StackType → Instantiation → ℕ → StackType → Set where
    subst-ρ-> :
              ∀ {ι₁ ι₂ θ} →
                ι₁ > ι₂ →
      -------------------------------
      ρ⁼ ι₁ ⟦ θ / ι₂ ⟧σ≡ ρ⁼ (pred ι₁)

    subst-ρ-≡ :
                  ∀ {σ ι} →
      ---------------------------------
      ρ⁼ ι ⟦ ρ σ / ι ⟧σ≡ weaken-σ 0 ι σ

    subst-ρ-< :
            ∀ {ι₁ ι₂ θ} →
              ι₁ < ι₂ →
      ------------------------
      ρ⁼ ι₁ ⟦ θ / ι₂ ⟧σ≡ ρ⁼ ι₁

    [] :
          ∀ {θ ι} →
      -----------------
      [] ⟦ θ / ι ⟧σ≡ []

    _∷_ :
         ∀ {τ τ' σ σ' θ ι} →
          τ ⟦ θ / ι ⟧τ≡ τ' →
          σ ⟦ θ / ι ⟧σ≡ σ' →
      -------------------------
      τ ∷ σ ⟦ θ / ι ⟧σ≡ τ' ∷ σ'

  infix 3 _⟦_/_⟧Γ≡_
  data _⟦_/_⟧Γ≡_ : RegisterAssignment → Instantiation → ℕ →
                   RegisterAssignment → Set where
    subst-registerₐ :
                 ∀ {regs regs' sp sp' θ ι} →
                     sp ⟦ θ / ι ⟧σ≡ sp' →
                  regs ⟦ θ / ι ⟧regs≡ regs' →
      -------------------------------------------------
      registerₐ sp regs ⟦ θ / ι ⟧Γ≡ registerₐ sp' regs'

  infix 3 _⟦_/_⟧regs≡_
  _⟦_/_⟧regs≡_ : ∀ {m} → Vec Type m → Instantiation → ℕ → Vec Type m → Set
  τs ⟦ θ / ι ⟧regs≡ τs' = AllZipᵥ (λ τ τ' → τ ⟦ θ / ι ⟧τ≡ τ') τs τs'

infix 3 _⟦_/_⟧θ≡_
data _⟦_/_⟧θ≡_ : Instantiation → Instantiation → ℕ → Instantiation → Set where
  subst-α :
      ∀ {τ τ' θ ι} →
     τ ⟦ θ / ι ⟧τ≡ τ' →
    --------------------
    α τ ⟦ θ / ι ⟧θ≡ α τ'

  subst-ρ :
      ∀ {σ σ' θ ι} →
     σ ⟦ θ / ι ⟧σ≡ σ' →
    --------------------
    ρ σ ⟦ θ / ι ⟧θ≡ ρ σ'

infix 3 _⟦_/_⟧θs≡_
data _⟦_/_⟧θs≡_ : Instantiations → Instantiation → ℕ → Instantiations → Set where
  [] :
        ∀ {θ ι} →
    ------------------
    [] ⟦ θ / ι ⟧θs≡ []

  _∷_ :
         ∀ {θ ι θ₁ θ₂ θs₁ θs₂} →
    θ₁ ⟦ θ / length θs₁ + ι ⟧θ≡ θ₂ →
         θs₁ ⟦ θ / ι ⟧θs≡ θs₂ →
    --------------------------------
     θ₁ ∷ θs₁ ⟦ θ / ι ⟧θs≡ θ₂ ∷ θs₂

infix 3 _⟦_/_⟧v≡_
data _⟦_/_⟧v≡_ : SmallValueₕ → Instantiation → ℕ → SmallValueₕ → Set where
  subst-reg :
          ∀ {♯r θ ι} →
    -------------------------
    reg ♯r ⟦ θ / ι ⟧v≡ reg ♯r

  subst-globval :
               ∀ {lab θ ι} →
    -----------------------------------
    globval lab ⟦ θ / ι ⟧v≡ globval lab

  subst-int :
         ∀ {n θ ι} →
    -----------------------
    int n ⟦ θ / ι ⟧v≡ int n

  subst-Λ :
                ∀ {Δ v v' θs θs' θ ι} →
                  v ⟦ θ / ι ⟧v≡ v' →
           θs ⟦ θ / length Δ + ι ⟧θs≡ θs' →
    ----------------------------------------------
    (Λ Δ ∙ v ⟦ θs ⟧) ⟦ θ / ι ⟧v≡ (Λ Δ ∙ v' ⟦ θs' ⟧)

infix 3 _⟦_/_⟧ι≡_
data _⟦_/_⟧ι≡_ : Instructionₕ → Instantiation → ℕ → Instructionₕ → Set where
  subst-add :
           ∀ {♯rd ♯rs v v' θ ι} →
               v ⟦ θ / ι ⟧v≡ v' →
    ----------------------------------------
    add ♯rd ♯rs v ⟦ θ / ι ⟧ι≡ add ♯rd ♯rs v'

  subst-sub :
           ∀ {♯rd ♯rs v v' θ ι} →
               v ⟦ θ / ι ⟧v≡ v' →
    ----------------------------------------
    sub ♯rd ♯rs v ⟦ θ / ι ⟧ι≡ sub ♯rd ♯rs v'

  subst-salloc :
             ∀ {n θ ι} →
    -----------------------------
    salloc n ⟦ θ / ι ⟧ι≡ salloc n

  subst-sfree :
             ∀ {n θ ι} →
    ---------------------------
    sfree n ⟦ θ / ι ⟧ι≡ sfree n

  subst-sld :
           ∀ {♯rd pos θ ι} →
    -----------------------------------
    sld ♯rd pos ⟦ θ / ι ⟧ι≡ sld ♯rd pos

  subst-sst :
           ∀ {♯rs pos θ ι} →
    -----------------------------------
    sst pos ♯rs ⟦ θ / ι ⟧ι≡ sst pos ♯rs

  subst-ld :
             ∀ {♯rd ♯rs pos θ ι} →
    -----------------------------------------
    ld ♯rd ♯rs pos ⟦ θ / ι ⟧ι≡ ld ♯rd ♯rs pos

  subst-st :
             ∀ {♯rd ♯rs pos θ ι} →
    -----------------------------------------
    st ♯rd pos ♯rs ⟦ θ / ι ⟧ι≡ st ♯rd pos ♯rs

  subst-malloc :
             ∀ {♯rd τs τs' θ ι} →
    AllZip (λ τ τ' → τ ⟦ θ / ι ⟧τ≡ τ') τs τs' →
    -------------------------------------------
      malloc ♯rd τs ⟦ θ / ι ⟧ι≡ malloc ♯rd τs'

  subst-mov :
         ∀ {♯rd v v' θ ι} →
          v ⟦ θ / ι ⟧v≡ v' →
    --------------------------------
    mov ♯rd v ⟦ θ / ι ⟧ι≡ mov ♯rd v'

  subst-beq :
          ∀ {♯r v v' θ ι} →
           v ⟦ θ / ι ⟧v≡ v' →
    ------------------------------
    beq ♯r v ⟦ θ / ι ⟧ι≡ beq ♯r v'

infix 3 _⟦_/_⟧I≡_
data _⟦_/_⟧I≡_ : InstructionSequenceₕ → Instantiation → ℕ →
                 InstructionSequenceₕ → Set where
  subst-~> :
        ∀ {ι ι' I I' θ ιₚ} →
         ι ⟦ θ / ιₚ ⟧ι≡ ι' →
         I ⟦ θ / ιₚ ⟧I≡ I' →
    -----------------------
    ι ~> I ⟦ θ / ιₚ ⟧I≡ ι' ~> I'

  subst-jmp :
        ∀ {v v' θ ι} →
       v ⟦ θ / ι ⟧v≡ v' →
    --------------------
    jmp v ⟦ θ / ι ⟧I≡ jmp v'

  subst-halt :
          ∀ {θ ι} →
    ---------------------
    halt ⟦ θ / ι ⟧I≡ halt

List-Substitution : ∀ A {{_ : Substitution A}} → Substitution (List A)
List-Substitution A = substitution
  (λ pos inc xs → map (weaken pos inc) xs)
  (λ xs θ ι xs' → AllZip (λ x x' → x ⟦ θ / ι ⟧≡ x') xs xs')

instance
  Type-Substitution : Substitution Type
  Type-Substitution = substitution weaken-τ _⟦_/_⟧τ≡_

  TypeVec-Substitution : ∀ {n} → Substitution (Vec Type n)
  TypeVec-Substitution = substitution weaken-regs _⟦_/_⟧regs≡_

  TypeList-Substitution : Substitution (List Type)
  TypeList-Substitution = List-Substitution Type

  InitType-Substitution : Substitution InitType
  InitType-Substitution = substitution weaken-τ⁻ _⟦_/_⟧τ⁻≡_

  InitTypeList-Substitution : Substitution (List InitType)
  InitTypeList-Substitution = substitution weaken-τs⁻ _⟦_/_⟧τs⁻≡_

  StackType-Substitution : Substitution StackType
  StackType-Substitution = substitution weaken-σ _⟦_/_⟧σ≡_

  RegisterAssignment-Substitution : Substitution RegisterAssignment
  RegisterAssignment-Substitution = substitution weaken-Γ _⟦_/_⟧Γ≡_

  Instantiation-Substitution : Substitution Instantiation
  Instantiation-Substitution = substitution weaken-θ _⟦_/_⟧θ≡_

  Instantiations-Substitution : Substitution Instantiations
  Instantiations-Substitution = substitution weaken-θs _⟦_/_⟧θs≡_

  SmallValue-Substitution : Substitution SmallValueₕ
  SmallValue-Substitution = substitution weaken-v _⟦_/_⟧v≡_
    where weaken-v : ℕ → ℕ → SmallValueₕ → SmallValueₕ
          weaken-v pos inc (reg ♯r) = reg ♯r
          weaken-v pos inc (globval l) = globval l
          weaken-v pos inc (int i) = int i
          weaken-v pos inc (Λ Δ ∙ v ⟦ θs ⟧) = Λ Δ ∙ weaken-v pos inc v ⟦ weaken (length Δ + pos) inc θs ⟧

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
