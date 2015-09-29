open import Util
open import Grammar

import Data.List as L
open import Relation.Nullary
open import Relation.Binary

α⁼-injective : ∀ {n₁ n₂} → α⁼ n₁ ≡ α⁼ n₂ → n₁ ≡ n₂
α⁼-injective refl = refl

∀-injective : ∀ {Δ₁ Δ₂ Γ₁ Γ₂} → ∀[ Δ₁ ] Γ₁ ≡ ∀[ Δ₂ ] Γ₂ → Δ₁ ≡ Δ₂ × Γ₁ ≡ Γ₂
∀-injective refl = refl , refl

tuple-injective : ∀ {τs₁ τs₂} → tuple τs₁ ≡ tuple τs₂ → τs₁ ≡ τs₂
tuple-injective refl = refl

ρ⁼-injective : ∀ {n₁ n₂} → ρ⁼ n₁ ≡ ρ⁼ n₂ → n₁ ≡ n₂
ρ⁼-injective refl = refl

∷-injective : ∀ {τ₁ τ₂ τs₁ τs₂} → τ₁ Grammar.∷ τs₁ ≡ τ₂ ∷ τs₂ → τ₁ ≡ τ₂ × τs₁ ≡ τs₂
∷-injective refl = refl , refl

,-injective : ∀ {Δ₁ Δ₂ a₁ a₂} → Δ₁ Grammar., a₁ ≡ Δ₂ , a₂ → Δ₁ ≡ Δ₂ × a₁ ≡ a₂
,-injective refl = refl , refl

registerₐ-injective : ∀ {σ₁ σ₂ regs₁ regs₂} → registerₐ σ₁ regs₁  ≡ registerₐ σ₂ regs₂ → σ₁ ≡ σ₂ × regs₁ ≡ regs₂
registerₐ-injective refl = refl , refl

inst-ρ-injective : ∀ {σ₁ σ₂} → inst-ρ σ₁ ≡ inst-ρ σ₂ → σ₁ ≡ σ₂
inst-ρ-injective refl = refl

inst-α-injective : ∀ {τ₁ τ₂} → inst-α τ₁ ≡ inst-α τ₂ → τ₁ ≡ τ₂
inst-α-injective refl = refl

globval-injective : ∀ {l₁ l₂} → globval l₁ ≡ globval l₂ → l₁ ≡ l₂
globval-injective refl = refl

heapval-injective : ∀ {lₕ₁ lₕ₂} → heapval lₕ₁ ≡ heapval lₕ₂ → lₕ₁ ≡ lₕ₂
heapval-injective refl = refl

const-injective : ∀ {n₁ n₂} → const n₁ ≡ const n₂ → n₁ ≡ n₂
const-injective refl = refl

uninit-injective : ∀ {τ₁ τ₂} → uninit τ₁ ≡ uninit τ₂ → τ₁ ≡ τ₂
uninit-injective refl = refl

inst-injective : ∀ {w₁ w₂ i₁ i₂} → w₁ [ i₁ ] ≡ w₂ [ i₂ ] → w₁ ≡ w₂ × i₁ ≡ i₂
inst-injective refl = refl , refl

reg-injective : ∀ {♯r₁ ♯r₂} → reg ♯r₁ ≡ reg ♯r₂ → ♯r₁ ≡ ♯r₂
reg-injective refl = refl

instᵥ-injective : ∀ {v₁ v₂ i₁ i₂} → v₁ [ i₁ ]ᵥ ≡ v₂ [ i₂ ]ᵥ → v₁ ≡ v₂ × i₁ ≡ i₂
instᵥ-injective refl = refl , refl

word-injective : ∀ {w₁ w₂} → word w₁ ≡ word w₂ → w₁ ≡ w₂
word-injective refl = refl

∀ᵢ-injective : ∀ {Δ₁ Δ₂ Γ₁ Γ₂ Is₁ Is₂} → ∀ᵢ[ Δ₁ ] Γ₁ ∙ Is₁ ≡ ∀ᵢ[ Δ₂ ] Γ₂ ∙ Is₂ → Δ₁ ≡ Δ₂ × Γ₁ ≡ Γ₂ × Is₁ ≡ Is₂
∀ᵢ-injective refl = refl , (refl , refl)

register-injective : ∀ {stack₁ stack₂ regs₁ regs₂} → register stack₁ regs₁  ≡ register stack₂ regs₂ → stack₁ ≡ stack₂ × regs₁ ≡ regs₂
register-injective refl = refl , refl

~>-injective : ∀ {I₁ I₂ Is₁ Is₂} → I₁ ~> Is₁  ≡ I₂ ~> Is₂ → I₁ ≡ I₂ × Is₁ ≡ Is₂
~>-injective refl = refl , refl

jmp-injective : ∀ {v₁ v₂} → jmp v₁ ≡ jmp v₂ → v₁ ≡ v₂
jmp-injective refl = refl

program-injective : ∀ {globs₁ globs₂ heap₁ heap₂ regs₁ regs₂ Is₁ Is₂} →
                      program globs₁ heap₁ regs₁ Is₁ ≡ program globs₂ heap₂ regs₂ Is₂ →
                      globs₁ ≡ globs₂ × heap₁ ≡ heap₂ × regs₁ ≡ regs₂ × Is₁ ≡ Is₂
program-injective refl = refl , (refl , (refl , refl))

private
  infix 4 _≟τ_ _≟τs_ _≟σ_ _≟Δ_ _≟a_ _≟Γ_ _≟regs_
  infix 4 _≟i_ _≟w_ _≟ws_ _≟wsᵥ_ _≟v_ _≟g_ _≟R_ _≟I_ _≟Is_ _≟P_

  mutual
    _≟τ_ : DecEqFun Type
    α⁼ ι₁ ≟τ α⁼ ι₂ = dec-inj α⁼-injective (ι₁ ≟ ι₂)
    α⁼ ι₁ ≟τ int = no (λ ())
    α⁼ ι₁ ≟τ ns = no (λ ())
    α⁼ ι₁ ≟τ ∀[ Δ₂ ] Γ₂ = no (λ ())
    α⁼ ι₁ ≟τ tuple τs₂ = no (λ ())
    int ≟τ α⁼ ι₂ = no (λ ())
    int ≟τ int = yes refl
    int ≟τ ns = no (λ ())
    int ≟τ ∀[ Δ₂ ] Γ₂ = no (λ ())
    int ≟τ tuple τs₂ = no (λ ())
    ns ≟τ α⁼ ι₂ = no (λ ())
    ns ≟τ int = no (λ ())
    ns ≟τ ns = yes refl
    ns ≟τ ∀[ Δ₂ ] Γ₂ = no (λ ())
    ns ≟τ tuple τs₂ = no (λ ())
    ∀[ Δ₁ ] Γ₁ ≟τ α⁼ ι₂ = no (λ ())
    ∀[ Δ₁ ] Γ₁ ≟τ int = no (λ ())
    ∀[ Δ₁ ] Γ₁ ≟τ ns = no (λ ())
    ∀[ Δ₁ ] Γ₁ ≟τ ∀[ Δ₂ ] Γ₂ = dec-inj₂ ∀-injective (Δ₁ ≟Δ Δ₂) (Γ₁ ≟Γ Γ₂)
    ∀[ Δ₁ ] Γ₁ ≟τ tuple τs₂ = no (λ ())
    tuple τs₁ ≟τ α⁼ ι₂ = no (λ ())
    tuple τs₁ ≟τ int = no (λ ())
    tuple τs₁ ≟τ ns = no (λ ())
    tuple τs₁ ≟τ ∀[ Δ₂ ] Γ₂ = no (λ ())
    tuple τs₁ ≟τ tuple τs₂ = dec-inj tuple-injective (τs₁ ≟τs τs₂)

    _≟τs_ : DecEqFun (List (Type × InitializationFlag))
    [] ≟τs [] = yes refl
    [] ≟τs (τ₂ , φ₂) ∷ τs₂ = no (λ ())
    (τ₁ , φ₁) ∷ τs₁ ≟τs [] = no (λ ())
    (τ₁ , φ₁) ∷ τs₁ ≟τs (τ₂ , φ₂) ∷ τs₂ = dec-inj₃ (×-assoc→ ∘ ×-map ×-,-injective id ∘ List-∷-injective) (τ₁ ≟τ τ₂) (φ₁ ≟ φ₂) (τs₁ ≟τs τs₂)

    _≟σ_ : DecEqFun StackType
    ρ⁼ ι₁ ≟σ ρ⁼ ι₂ = dec-inj ρ⁼-injective (ι₁ ≟ ι₂)
    ρ⁼ ι₁ ≟σ nil = no (λ ())
    ρ⁼ ι₁ ≟σ τ₂ ∷ σ₂ = no (λ ())
    nil ≟σ ρ⁼ ι₂ = no (λ ())
    nil ≟σ nil = yes refl
    nil ≟σ τ₂ ∷ σ₂ = no (λ ())
    τ₁ ∷ σ₁ ≟σ ρ⁼ ι₂ = no (λ ())
    τ₁ ∷ σ₁ ≟σ nil = no (λ ())
    τ₁ ∷ σ₁ ≟σ τ₂ ∷ σ₂ = dec-inj₂ ∷-injective (τ₁ ≟τ τ₂) (σ₁ ≟σ σ₂)

    _≟Δ_ : DecEqFun TypeAssignment
    ∙ ≟Δ ∙ = yes refl
    ∙ ≟Δ Δ₂ , a₂ = no (λ ())
    Δ₁ , a₁ ≟Δ ∙ = no (λ ())
    Δ₁ , a₁ ≟Δ Δ₂ , a₂ = dec-inj₂ ,-injective (Δ₁ ≟Δ Δ₂) (a₁ ≟a a₂)

    _≟a_ : DecEqFun TypeAssignmentValue
    α ≟a α = yes refl
    α ≟a ρ = no (λ ())
    ρ ≟a α = no (λ ())
    ρ ≟a ρ = yes refl

    _≟Γ_ : DecEqFun RegisterAssignment
    registerₐ σ₁ regs₁ ≟Γ registerₐ σ₂ regs₂ = dec-inj₂ registerₐ-injective (σ₁ ≟σ σ₂) (regs₁ ≟regs regs₂)

    _≟regs_ : ∀ {m} → DecEqFun (Vec Type m)
    [] ≟regs [] = yes refl
    τ₁ ∷ regs₁ ≟regs τ₂ ∷ regs₂ = dec-inj₂ Vec-∷-injective (τ₁ ≟τ τ₂) (regs₁ ≟regs regs₂)

    _≟i_ : DecEqFun InstantiationValue
    inst-ρ σ₁ ≟i inst-ρ σ₂ = dec-inj inst-ρ-injective (σ₁ ≟σ σ₂)
    inst-ρ σ₁ ≟i inst-α τ₂ = no (λ ())
    inst-α τ₁ ≟i inst-ρ σ₂ = no (λ ())
    inst-α τ₁ ≟i inst-α τ₂ = dec-inj inst-α-injective (τ₁ ≟τ τ₂)

    _≟w_ : DecEqFun WordValue
    globval l₁ ≟w globval l₂ = dec-inj globval-injective (l₁ ≟ l₂)
    globval l₁ ≟w heapval lₕ₂ = no (λ ())
    globval l₁ ≟w const n₂ = no (λ ())
    globval l₁ ≟w uninit τ₂ = no (λ ())
    globval l₁ ≟w w₂ [ i₂ ] = no (λ ())
    heapval lₕ₁ ≟w globval l₂ = no (λ ())
    heapval lₕ₁ ≟w heapval lₕ₂ = dec-inj heapval-injective (lₕ₁ ≟ lₕ₂)
    heapval lₕ₁ ≟w const n₂ = no (λ ())
    heapval lₕ₁ ≟w uninit τ₂ = no (λ ())
    heapval lₕ₁ ≟w w₂ [ i₂ ] = no (λ ())
    const n₁ ≟w globval l₂ = no (λ ())
    const n₁ ≟w heapval lₕ₂ = no (λ ())
    const n₁ ≟w const n₂ = dec-inj const-injective (n₁ ≟ n₂)
    const n₁ ≟w uninit τ₂ = no (λ ())
    const n₁ ≟w w₂ [ i₂ ] = no (λ ())
    uninit τ₁ ≟w globval l₂ = no (λ ())
    uninit τ₁ ≟w heapval lₕ₂ = no (λ ())
    uninit τ₁ ≟w const n₂ = no (λ ())
    uninit τ₁ ≟w uninit τ₂ = dec-inj uninit-injective (τ₁ ≟τ τ₂)
    uninit τ₁ ≟w w₂ [ i₂ ] = no (λ ())
    w₁ [ i₁ ] ≟w globval l₁ = no (λ ())
    w₁ [ i₁ ] ≟w heapval lₕ₁ = no (λ ())
    w₁ [ i₁ ] ≟w const n₂ = no (λ ())
    w₁ [ i₁ ] ≟w uninit τ₂ = no (λ ())
    w₁ [ i₁ ] ≟w w₂ [ i₂ ] = dec-inj₂ inst-injective (w₁ ≟w w₂) (i₁ ≟i i₂)

    _≟ws_ : DecEqFun (List WordValue)
    [] ≟ws [] = yes refl
    [] ≟ws w₂ ∷ ws₂ = no (λ ())
    w₁ ∷ ws₁ ≟ws [] = no (λ ())
    w₁ ∷ ws₁ ≟ws w₂ ∷ ws₂ = dec-inj₂ List-∷-injective (w₁ ≟w w₂) (ws₁ ≟ws ws₂)

    _≟wsᵥ_ : ∀ {n} → DecEqFun (Vec WordValue n)
    [] ≟wsᵥ [] = yes refl
    w₁ ∷ ws₁ ≟wsᵥ w₂ ∷ ws₂ = dec-inj₂ Vec-∷-injective (w₁ ≟w w₂) (ws₁ ≟wsᵥ ws₂)

    _≟v_ : DecEqFun SmallValue
    reg ♯r₁ ≟v reg ♯r₂ = dec-inj reg-injective (♯r₁ ≟ ♯r₂)
    reg ♯r₁ ≟v v₁ [ i₂ ]ᵥ = no (λ ())
    reg ♯r₁ ≟v word w₂ = no (λ ())
    v₁ [ i₁ ]ᵥ ≟v reg ♯r₂ = no (λ ())
    v₁ [ i₁ ]ᵥ ≟v v₂ [ i₂ ]ᵥ = dec-inj₂ instᵥ-injective (v₁ ≟v v₂) (i₁ ≟i i₂)
    v₁ [ i₁ ]ᵥ ≟v word w₂ = no (λ ())
    word w₁ ≟v reg ♯r₂ = no (λ ())
    word w₁ ≟v v₂ [ i₂ ]ᵥ = no (λ ())
    word w₁ ≟v word w₂ = dec-inj word-injective (w₁ ≟w w₂)

    _≟g_ : DecEqFun GlobalValue
    ∀ᵢ[ Δ₁ ] Γ₁ ∙ Is₁ ≟g ∀ᵢ[ Δ₂ ] Γ₂ ∙ Is₂ = dec-inj₃ ∀ᵢ-injective (Δ₁ ≟Δ Δ₂) (Γ₁ ≟Γ Γ₂) (Is₁ ≟Is Is₂)

    _≟gs_ : DecEqFun (List GlobalValue)
    [] ≟gs [] = yes refl
    [] ≟gs (g₂ ∷ gs₂) = no (λ ())
    (g₁ ∷ gs₁) ≟gs [] = no (λ ())
    (g₁ ∷ gs₁) ≟gs (g₂ ∷ gs₂) = dec-inj₂ List-∷-injective (g₁ ≟g g₂) (gs₁ ≟gs gs₂)

    _≟R_ : DecEqFun RegisterFile
    register stack₁ regs₁ ≟R register stack₂ regs₂ = dec-inj₂ register-injective (stack₁ ≟ws stack₂) (regs₁ ≟wsᵥ regs₂)

    _≟I_ : DecEqFun Instruction
    () ≟I ()

    _≟Is_ : DecEqFun InstructionSequence
    I₁ ~> Is₁ ≟Is I₂ ~> Is₂ = dec-inj₂ ~>-injective (I₁ ≟I I₂) (Is₁ ≟Is Is₂)
    I₁ ~> Is₁ ≟Is jmp v₂ = no (λ ())
    jmp v₁ ≟Is I₂ ~> Is₂ = no (λ ())
    jmp v₁ ≟Is jmp v₂ = dec-inj jmp-injective (v₁ ≟v v₂)

    _≟P_ : DecEqFun Program
    program globs₁ heap₁ regs₁ Is₁ ≟P program globs₂ heap₂ regs₂ Is₂ =
      dec-inj₄ program-injective (globs₁ ≟gs globs₂) (heap₁ ≟ws heap₂) (regs₁ ≟R regs₂) (Is₁ ≟Is Is₂)

instance
  Type-dec-eq : DecEq Type
  Type-dec-eq = decEq _≟τ_

  StackType-dec-eq : DecEq StackType
  StackType-dec-eq = decEq _≟σ_

  TypeAssignment-dec-eq : DecEq TypeAssignment
  TypeAssignment-dec-eq = decEq _≟Δ_

  TypeAssignmentValue-dec-eq : DecEq TypeAssignmentValue
  TypeAssignmentValue-dec-eq = decEq _≟a_

  RegisterAssignment-dec-eq : DecEq RegisterAssignment
  RegisterAssignment-dec-eq = decEq _≟Γ_

  InstantiationValue-dec-eq : DecEq InstantiationValue
  InstantiationValue-dec-eq = decEq _≟i_

  WordValue-dec-eq : DecEq WordValue
  WordValue-dec-eq = decEq _≟w_

  SmallValue-dec-eq : DecEq SmallValue
  SmallValue-dec-eq = decEq _≟v_

  GlobalValue-dec-eq : DecEq GlobalValue
  GlobalValue-dec-eq = decEq _≟g_

  RegisterFile-dec-eq : DecEq RegisterFile
  RegisterFile-dec-eq = decEq _≟R_

  Instruction-dec-eq : DecEq Instruction
  Instruction-dec-eq = decEq _≟I_

  InstructionSequence-dec-eq : DecEq InstructionSequence
  InstructionSequence-dec-eq = decEq _≟Is_

  Program-dec-eq : DecEq Program
  Program-dec-eq = decEq _≟P_
