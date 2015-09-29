open import Util

♯regs : ℕ
♯regs = 4

infix 7  ∀[_]_ ∀ᵢ[_]_∙_
infixr 6 _,_ _∷_ _[_]

mutual
  -- Types, τ
  data Type : Set where
    α⁼    : AssignmentIndex → Type
    int   : Type
    ns    : Type
    ∀[_]_ : TypeAssignment → RegisterAssignment → Type
    tuple : List (Type × InitializationFlag) → Type

  -- Stack types, σ
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

  -- Assignment index, ι
  AssignmentIndex : Set
  AssignmentIndex = ℕ

  -- Type assignments, Δ
  data TypeAssignment : Set where
    ∙ : TypeAssignment
    _,_ : TypeAssignment → TypeAssignmentValue → TypeAssignment

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

  -- Instantiating values, i
  data InstantiationValue : Set where
    inst-ρ : StackType → InstantiationValue
    inst-α : Type → InstantiationValue

  -- Word value, w
  data WordValue : Set where
    globval : GlobLabel → WordValue
    heapval : HeapLabel → WordValue
    const   : ℕ → WordValue
    uninit  : Type → WordValue
    _[_]    : WordValue → InstantiationValue → WordValue

  -- Small values, v
  data SmallValue : Set where
    reg  : Register → SmallValue
    _[_]ᵥ : SmallValue → InstantiationValue → SmallValue
    word : WordValue → SmallValue

  -- Heap values, h
  HeapValue : Set
  HeapValue = WordValue

  -- Heaps, H
  Heap : Set
  Heap = List HeapValue

  -- Global values, g
  data GlobalValue : Set where
    ∀ᵢ[_]_∙_ : TypeAssignment → RegisterAssignment → InstructionSequence → GlobalValue

  -- Global constants
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
    -- TODO

  -- Is
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
