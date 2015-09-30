open import Util

♯regs : ℕ
♯regs = 4

mutual
  -- Assignment index, ι
  AssignmentIndex : Set
  AssignmentIndex = ℕ

  -- Types, τ
  infix 7  ∀[_]_
  data Type : Set where
    α⁼    : AssignmentIndex → Type
    int   : Type
    ns    : Type
    ∀[_]_ : TypeAssignment → RegisterAssignment → Type
    tuple : List (Type × InitializationFlag) → Type

  -- Stack types, σ
  infixr 5 _∷_
  data StackType : Set where
    ρ⁼  : AssignmentIndex → StackType
    nil : StackType
    _∷_ : Type → StackType → StackType

  -- Initialization flags, φ
  InitializationFlag : Set
  InitializationFlag = Bool

  -- Label assignments, ψ
  LabelAssignment : Set
  LabelAssignment = List Type

  -- Type assignments, Δ
  infixr 6 _,_
  data TypeAssignment : Set where
    ∙ : TypeAssignment
    _,_ : TypeAssignmentValue → TypeAssignment → TypeAssignment

  -- Type assignment values, a
  data TypeAssignmentValue : Set where
    α : TypeAssignmentValue
    ρ : TypeAssignmentValue

  -- Register assignments, Γ
  record RegisterAssignment : Set where
    inductive
    constructor registerₐ
    field
      reg-types : Vec Type ♯regs
      stack-type : StackType

  -- Registers, ♯r
  Register : Set
  Register = Fin ♯regs

  -- Global labels, l
  GlobLabel : Set
  GlobLabel = ℕ

  -- Heap labels, lₕ
  HeapLabel : Set
  HeapLabel = ℕ

  -- Instantiating values, i
  data InstantiationValue : Set where
    inst-ρ : StackType → InstantiationValue
    inst-α : Type → InstantiationValue

  -- Word value, w
  infix 6 _⟦_⟧
  data WordValue : Set where
    globval : GlobLabel → WordValue
    heapval : HeapLabel → WordValue
    const   : ℕ → WordValue
    ns      : WordValue
    uninit  : Type → WordValue
    _⟦_⟧    : WordValue → InstantiationValue → WordValue

  -- Small values, v
  infix 6 _⟦_⟧ᵥ
  data SmallValue : Set where
    reg  : Register → SmallValue
    word : WordValue → SmallValue
    _⟦_⟧ᵥ : SmallValue → InstantiationValue → SmallValue

  -- Heap values, h
  HeapValue : Set
  HeapValue = List WordValue

  -- Heaps, H
  Heap : Set
  Heap = List HeapValue

  -- Global values, g
  infix 7 ∀ᵢ[_]_∙_
  data GlobalValue : Set where
    ∀ᵢ[_]_∙_ :
      TypeAssignment → RegisterAssignment → InstructionSequence → GlobalValue

  -- Global constants, G
  Globals : Set
  Globals = List GlobalValue

  -- Register files, R
  record RegisterFile : Set where
    inductive
    constructor register
    field
      regs  : Vec WordValue ♯regs
      stack : Stack

  -- Stacks, S
  Stack : Set
  Stack = List WordValue

  -- I
  data Instruction : Set where
    add  : Register → Register → SmallValue → Instruction
    sub  : Register → Register → SmallValue → Instruction
    mul  : Register → Register → SmallValue → Instruction
    push : SmallValue → Instruction
    pop  : Instruction
    sld  : Register → ℕ → Instruction
    sst  : ℕ → Register → Instruction
    ld   : Register → Register → ℕ → Instruction
    st   : Register → ℕ → Register → Instruction

  -- Is
  infixr 6 _~>_
  data InstructionSequence : Set where
    _~>_ : Instruction → InstructionSequence → InstructionSequence
    jmp : SmallValue → InstructionSequence

  -- P
  record Program : Set where
    inductive
    constructor program
    field
      globals      : Globals
      heap         : Heap
      registers    : RegisterFile
      instructions : InstructionSequence

open RegisterAssignment public
open RegisterFile public
open Program public

infixr 5 _++_
_++_ : TypeAssignment → TypeAssignment → TypeAssignment
∙ ++ Δ = Δ
a , Δ ++ Δ' = a , (Δ ++ Δ')

infix 4 _↓_⇒_
data _↓_⇒_ :
    TypeAssignment → AssignmentIndex → TypeAssignmentValue → Set where
  here :
        ∀ {Δ a} →
    ----------------
    a , Δ ↓ zero ⇒ a

  there :
      ∀ {Δ a a' ι} →
        Δ ↓ ι ⇒ a →
    ------------------
    a' , Δ ↓ suc ι ⇒ a
