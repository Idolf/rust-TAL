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
    tuple : List InitType → Type

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

  -- Global label assignments, ψ₁
  GlobalLabelAssignment : Set
  GlobalLabelAssignment = List Type

  -- Heap label assignments, ψ₂
  HeapLabelAssignment : Set
  HeapLabelAssignment = List Type

  -- Label assignments, ψ
  LabelAssignment : Set
  LabelAssignment = GlobalLabelAssignment × HeapLabelAssignment

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

  -- Instantiations i
  data Instantiation : Set where
    α : Type → Instantiation
    ρ : StackType → Instantiation

  -- CastValue cᵥ
  data CastValue (W : Set) : Set where
    inst : Instantiation → CastValue W
    weaken : W → CastValue W
  WeakCastValue : Set
  WeakCastValue = CastValue ℕ
  StrongCastValue : Set
  StrongCastValue = CastValue TypeAssignment

  infix 6 _/_
  -- Casting c
  data Cast (W : Set) : Set where
    _/_ : CastValue W → ℕ → Cast W
  WeakCast : Set
  WeakCast = Cast ℕ
  StrongCast : Set
  StrongCast = Cast TypeAssignment

  -- Word value, w
  infix 6 _⟦_⟧
  data WordValue : Set where
    globval : GlobLabel → ℕ → WordValue
    heapval : HeapLabel → WordValue
    const   : ℕ → WordValue
    ns      : WordValue
    uninit  : Type → WordValue
    _⟦_⟧    : WordValue → StrongCast → WordValue

  -- Small values, v
  infix 6 _⟦_⟧ᵥ
  data SmallValue : Set where
    reg  : Register → SmallValue
    word : WordValue → SmallValue
    _⟦_⟧ᵥ : SmallValue → StrongCast → SmallValue

  -- Heap values, h
  data HeapValue : Set where
    tuple : List WordValue → HeapValue

  -- Heaps, H
  Heap : Set
  Heap = List HeapValue

  -- Global values, g
  infix 7 ∀[_]_∙_
  data GlobalValue : Set where
    ∀[_]_∙_ :
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

  -- ι
  data Instruction : Set where
    add    : Register → Register → SmallValue → Instruction
    sub    : Register → Register → SmallValue → Instruction
    push   : SmallValue → Instruction
    pop    : Instruction
    sld    : Register → ℕ → Instruction
    sst    : ℕ → Register → Instruction
    ld     : Register → Register → ℕ → Instruction
    st     : Register → ℕ → Register → Instruction
    malloc : Register → List Type → Instruction
    mov    : Register → SmallValue → Instruction
    beq    : Register → SmallValue → Instruction

  -- I
  infixr 6 _~>_
  data InstructionSequence : Set where
    _~>_ : Instruction → InstructionSequence → InstructionSequence
    jmp : SmallValue → InstructionSequence

  -- P
  Program : Set
  Program = Heap × RegisterFile × InstructionSequence

open RegisterAssignment public
open RegisterFile public
