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
    tuple : ∀ {m} → Vec InitType m → Type

  -- Stack types, σ
  infixr 5 _∷_
  data StackType : Set where
    ρ⁼  : AssignmentIndex → StackType
    nil : StackType
    _∷_ : Type → StackType → StackType

  -- Initialization flags, φ
  InitializationFlag : Set
  InitializationFlag = Bool

  -- Possible uninitialized type, τ⁻
  InitType : Set
  InitType = Type × InitializationFlag

  -- Label assignments, ψ
  LabelAssignment : Set
  LabelAssignment = List Type

  -- Type assignments, Δ
  TypeAssignment : Set
  TypeAssignment = List TypeAssignmentValue

  -- Type assignment values, a
  data TypeAssignmentValue : Set where
    α : TypeAssignmentValue
    ρ : TypeAssignmentValue

  -- Register assignments, Γ
  record RegisterAssignment : Set where
    inductive
    constructor registerₐ
    field
      stack-type : StackType
      reg-types : Vec Type ♯regs

  -- Registers, ♯r
  Register : Set
  Register = Fin ♯regs

  -- Global labels, l
  GlobLabel : Set
  GlobLabel = ℕ

  -- Heap labels, lₕ
  HeapLabel : Set
  HeapLabel = ℕ

  -- Instantion

  -- Instantiating values, i
  InstantiationValue : TypeAssignmentValue → Set
  InstantiationValue α = Type
  InstantiationValue ρ = StackType

  -- CastValue cᵥ
  data CastValue : Set where
    inst : (a : TypeAssignmentValue) → InstantiationValue a → CastValue
    weaken : TypeAssignmentValue → CastValue

  infix 6 _/_
  -- Casting c
  data Cast : Set where
    _/_ : CastValue → ℕ → Cast

  -- Word value, w
  infix 6 _⟦_⟧
  data WordValue : Set where
    globval : GlobLabel → WordValue
    heapval : HeapLabel → WordValue
    const   : ℕ → WordValue
    ns      : WordValue
    uninit  : Type → WordValue
    _⟦_⟧    : WordValue → Cast → WordValue

  -- Small values, v
  infix 6 _⟦_⟧ᵥ
  data SmallValue : Set where
    reg  : Register → SmallValue
    word : WordValue → SmallValue
    _⟦_⟧ᵥ : SmallValue → Cast → SmallValue

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
      stack : Stack
      regs  : Vec WordValue ♯regs

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
  record Program (G : Globals) : Set where
    inductive
    constructor program
    field
      heap         : Heap
      registers    : RegisterFile
      instructions : InstructionSequence

open RegisterAssignment public
open RegisterFile public
open Program public
