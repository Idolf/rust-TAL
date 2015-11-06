module Judgments.Substitution where

open import Util
open import Judgments.Grammar

-- The purpose of this file is
-- to include instances of this record.
record Substitution (A : Set) : Set1 where
  constructor substitution
  infix 3 _⟦_⟧≡_
  field
    _⟦_⟧≡_ : A → WeakCast → A → Set

-- It would be really nice if these were equivalent, but they are
-- apparently not.
-- open Substitution {{...}} public
infix 3 _⟦_⟧≡_
_⟦_⟧≡_ : ∀ {A} {{S : Substitution A}} →
           A → WeakCast → A → Set
_⟦_⟧≡_ {{S}} = Substitution._⟦_⟧≡_ S

wctx-length : WordValue → ℕ
wctx-length (globval l ♯a) = ♯a
wctx-length (w ⟦ inst i / ι ⟧) = pred (wctx-length w)
wctx-length (w ⟦ weaken Δ⁺ / ι ⟧) = wctx-length w + length Δ⁺
wctx-length _ = 0

vctx-length : SmallValue → ℕ
vctx-length (word w) = wctx-length w
vctx-length (v ⟦ inst i / ι ⟧) = pred (vctx-length v)
vctx-length (v ⟦ weaken Δ⁺ / ι ⟧) = length Δ⁺ + vctx-length v
vctx-length _ = 0

mutual
  infix 3 _⟦_⟧n≡_
  data _⟦_⟧n≡_ : ℕ → WeakCast → ℕ → Set where
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
  data _⟦_⟧τ≡_ : Type → WeakCast → Type → Set where
    subst-α-¬inst :
          ∀ {ι₁ ι₁' ι₂ cᵥ} →
         ι₁ ⟦ cᵥ / ι₂ ⟧n≡ ι₁' →
      --------------------------
      α⁼ ι₁ ⟦ cᵥ / ι₂ ⟧τ≡ α⁼ ι₁'

    subst-α-inst :
             ∀ {ι τ τ'} →
      τ ⟦ weaken ι / zero ⟧τ≡ τ' →
      -----------------------------
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
  data _⟦_⟧τ⁻≡_ : InitType → WeakCast → InitType → Set where
    subst-τ⁻ :
            ∀ {φ τ τ' c} →
            τ ⟦ c ⟧τ≡ τ' →
      -------------------------
      (τ , φ) ⟦ c ⟧τ⁻≡ (τ' , φ)

  infix 3 _⟦_⟧τs⁻≡_
  _⟦_⟧τs⁻≡_ : List InitType → WeakCast → List InitType → Set
  τs⁻ ⟦ c ⟧τs⁻≡ τs⁻' =
    AllZip (λ τ⁻ τ⁻' → τ⁻ ⟦ c ⟧τ⁻≡ τ⁻') τs⁻ τs⁻'

  infix 3 _⟦_⟧σ≡_
  data _⟦_⟧σ≡_ : StackType → WeakCast → StackType → Set where
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

    subst-[] :
         ∀ {c} →
      -------------
      [] ⟦ c ⟧σ≡ []

    _∷_ :
        ∀ {τ τ' σ σ' c} →
         τ ⟦ c ⟧τ≡ τ' →
         σ ⟦ c ⟧σ≡ σ' →
      ---------------------
      τ ∷ σ ⟦ c ⟧σ≡ τ' ∷ σ'

  infix 3 _⟦_⟧Δ≡_
  infixr 5 _∷_
  data _⟦_⟧Δ≡_ : TypeAssignment → WeakCast → TypeAssignment → Set where
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
  data _⟦_⟧a≡_ : TypeAssignmentValue → WeakCast →
                 TypeAssignmentValue → Set where
    subst-α :
         ∀ {c} →
      -----------
      α ⟦ c ⟧a≡ α

    subst-ρ :
        ∀ {c} →
      -----------
      ρ ⟦ c ⟧a≡ ρ

  infix 3 _⟦_⟧Γ≡_
  data _⟦_⟧Γ≡_ : RegisterAssignment → WeakCast →
                 RegisterAssignment → Set where
    subst-registerₐ :
              ∀ {regs regs' sp sp' c} →
                  sp ⟦ c ⟧σ≡ sp' →
               regs ⟦ c ⟧regs≡ regs' →
      ---------------------------------------------
      registerₐ sp regs ⟦ c ⟧Γ≡ registerₐ sp' regs'

  infix 3 _⟦_⟧regs≡_
  _⟦_⟧regs≡_ : ∀ {m} → Vec Type m → WeakCast → Vec Type m → Set
  τs ⟦ c ⟧regs≡ τs' = AllZipᵥ (λ τ τ' → τ ⟦ c ⟧τ≡ τ') τs τs'

infix 3 _⟦_⟧i≡_
data _⟦_⟧i≡_ : Instantiation → WeakCast → Instantiation → Set where
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
data _⟦_⟧cᵥ≡_ : StrongCastValue → WeakCast → StrongCastValue → Set where
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
data _⟦_⟧c≡_ : StrongCast → WeakCast → StrongCast → Set where
  subst-/ :
         ∀ {cᵥ₁ cᵥ₂ cᵥ ι₁ ι₂} →
    cᵥ₁ ⟦ cᵥ / ι₁ ∸ suc ι₂ ⟧cᵥ≡ cᵥ₂ →
    ---------------------------------
     cᵥ₁ / ι₂ ⟦ cᵥ / ι₁ ⟧c≡ cᵥ₂ / ι₂

infix 3 _⟦_⟧w≡_
data _⟦_⟧w≡_ : WordValue → WeakCast → WordValue → Set where
  subst-globval :
             ∀ {l ♯a c} →
    ---------------------------------
    globval l ♯a ⟦ c ⟧w≡ globval l ♯a

  subst-heapval :
            ∀ {l c} →
    ---------------------------
    heapval l ⟦ c ⟧w≡ heapval l

  subst-int :
         ∀ {n c} →
    -------------------
    int n ⟦ c ⟧w≡ int n

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
           ∀ {w₁ w₂ cᵥ₁ cᵥ₂ ιₘ cᵥ ι} →
               w₁ ⟦ cᵥ / ι ⟧w≡ w₂ →
    cᵥ₁ ⟦ cᵥ / (wctx-length w₁ ∸ suc ιₘ) + ι ⟧cᵥ≡ cᵥ₂ →
    ---------------------------------------------------
      (w₁ ⟦ cᵥ₁ / ιₘ ⟧) ⟦ cᵥ / ι ⟧w≡ (w₂ ⟦ cᵥ₂ / ιₘ ⟧)

infix 3 _⟦_⟧v≡_
data _⟦_⟧v≡_ : SmallValue → WeakCast → SmallValue → Set where
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
     (v₁ ⟦ c₁ ⟧) ⟦ cᵥ / ι ⟧v≡ (v₂ ⟦ c₂ ⟧)

infix 3 _⟦_⟧ι≡_
data _⟦_⟧ι≡_ : Instruction → WeakCast → Instruction → Set where
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
data _⟦_⟧I≡_ : InstructionSequence → WeakCast →
               InstructionSequence → Set where
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

Vec-Substitution : ∀ A {{S : Substitution A}} m → Substitution (Vec A m)
Vec-Substitution A m =
  substitution (λ xs c xs' → AllZipᵥ (λ x x' → x ⟦ c ⟧≡ x') xs xs')

List-Substitution : ∀ A {{s : Substitution A}} → Substitution (List A)
List-Substitution A =
  substitution (λ xs c xs' → AllZip (λ x x' → x ⟦ c ⟧≡ x') xs xs')

instance
  ℕ-Substitution : Substitution ℕ
  ℕ-Substitution = substitution _⟦_⟧n≡_

  Type-Substitution : Substitution Type
  Type-Substitution = substitution _⟦_⟧τ≡_

  TypeVec-Substitution : ∀ {m} → Substitution (Vec Type m)
  TypeVec-Substitution = Vec-Substitution Type _

  TypeList-Substitution : Substitution (List Type)
  TypeList-Substitution = List-Substitution Type

  InitType-Substitution : Substitution InitType
  InitType-Substitution = substitution _⟦_⟧τ⁻≡_

  InitTypeVec-Substitution : ∀ {m} → Substitution (Vec InitType m)
  InitTypeVec-Substitution = Vec-Substitution InitType _

  InitTypeList-Substitution : Substitution (List InitType)
  InitTypeList-Substitution = List-Substitution InitType

  StackType-Substitution : Substitution StackType
  StackType-Substitution = substitution _⟦_⟧σ≡_

  RegisterAssignment-Substitution : Substitution RegisterAssignment
  RegisterAssignment-Substitution = substitution _⟦_⟧Γ≡_

  TypeAssignment-Substitution : Substitution TypeAssignment
  TypeAssignment-Substitution = substitution _⟦_⟧Δ≡_

  TypeAssignmentValue-Substitution : Substitution TypeAssignmentValue
  TypeAssignmentValue-Substitution = substitution _⟦_⟧a≡_

  Instantiation-Substitution : Substitution Instantiation
  Instantiation-Substitution = substitution _⟦_⟧i≡_

  StrongCastValue-Substitution : Substitution StrongCastValue
  StrongCastValue-Substitution = substitution _⟦_⟧cᵥ≡_

  StrongCast-Substitution : Substitution StrongCast
  StrongCast-Substitution = substitution _⟦_⟧c≡_

  WordValue-Substitution : Substitution WordValue
  WordValue-Substitution = substitution _⟦_⟧w≡_

  SmallValue-Substitution : Substitution SmallValue
  SmallValue-Substitution = substitution _⟦_⟧v≡_

  Instruction-Substitution : Substitution Instruction
  Instruction-Substitution = substitution _⟦_⟧ι≡_

  InstructionSequence-Substitution : Substitution InstructionSequence
  InstructionSequence-Substitution = substitution _⟦_⟧I≡_
