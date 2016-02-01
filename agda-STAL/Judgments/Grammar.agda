module Judgments.Grammar where

open import Util

-- The purpose of this file is to introduce the base grammar
-- on which every other file depends.

♯regs : ℕ
♯regs = 4

-- Assignment index, ι
AssignmentIndex : Set
AssignmentIndex = ℕ

mutual
  -- Types, τ
  infix 7  ∀[_]_
  data Type : Set where
    α⁼    : AssignmentIndex → Type
    int   : Type
    ns    : Type
    ∀[_]_ : TypeAssumptions → RegisterAssignment → Type
    tuple : List InitType → Type

  -- Initialization flags, φ
  data InitializationFlag : Set where
    init : InitializationFlag
    uninit : InitializationFlag

  -- Possible uninitialized type, τ⁻
  InitType : Set
  InitType = Type × InitializationFlag

  -- Stack types, σ
  infixr 5 _∷_
  data StackType : Set where
    ρ⁼  : AssignmentIndex → StackType
    []  : StackType
    _∷_ : Type → StackType → StackType

  -- Type assignments, Δ
  TypeAssumptions : Set
  TypeAssumptions = List TypeAssumptionValue

  -- Type assignment values, a
  data TypeAssumptionValue : Set where
    α : TypeAssumptionValue
    ρ : TypeAssumptionValue

  -- Register assignments, Γ
  data RegisterAssignment : Set where
    registerₐ : StackType → Vec Type ♯regs → RegisterAssignment

-- Global label assignments, ψ₁
GlobalLabelAssignment : Set
GlobalLabelAssignment = List Type

-- Heap label assignments, ψ₂
HeapLabelAssignment : Set
HeapLabelAssignment = List Type

-- Label assignments, ψ
LabelAssignment : Set
LabelAssignment = GlobalLabelAssignment × HeapLabelAssignment

-- Registers, ♯r
Register : Set
Register = Fin ♯regs

-- Global labels, l
GlobLabel : Set
GlobLabel = ℕ

-- Heap labels, lₕ
HeapLabel : Set
HeapLabel = ℕ

-- Instantiation, i
data Instantiation : Set where
  α : Type → Instantiation
  ρ : StackType → Instantiation

-- Instantiations, is
Instantiations : Set
Instantiations = List Instantiation

-- Word value, w
infixl 6 Λ_∙_⟦_⟧
data WordValue : Set where
  globval : GlobLabel → WordValue
  heapval : HeapLabel → WordValue
  int     : ℕ → WordValue
  ns      : WordValue
  uninit  : Type → WordValue
  Λ_∙_⟦_⟧ : TypeAssumptions → WordValue → Instantiations → WordValue

-- Small values, v
data SmallValue : Set where
  reg     : Register → SmallValue
  globval : GlobLabel → SmallValue
  int     : ℕ → SmallValue
  ns      : SmallValue
  uninit  : Type → SmallValue
  Λ_∙_⟦_⟧ : TypeAssumptions → SmallValue → Instantiations → SmallValue

-- ι
data Instruction : Set where
  add    : Register → Register → SmallValue → Instruction
  sub    : Register → Register → SmallValue → Instruction
  salloc : ℕ → Instruction
  sfree  : ℕ → Instruction
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
  halt : InstructionSequence

-- Global values, g
infix 7 code[_]_∙_
data GlobalValue : Set where
  code[_]_∙_ :
    TypeAssumptions → RegisterAssignment → InstructionSequence → GlobalValue

-- Global constants, G
Globals : Set
Globals = List GlobalValue

-- Heap values, h
data HeapValue : Set where
  tuple : List WordValue → HeapValue

-- Heaps, H
Heap : Set
Heap = List HeapValue

-- Stacks, S
Stack : Set
Stack = List WordValue

-- Register files, R
data RegisterFile : Set where
  register : Stack → Vec WordValue ♯regs → RegisterFile

-- P
ProgramState : Set
ProgramState = Heap × RegisterFile × InstructionSequence

data Program : Set where
  going : Globals → ProgramState → Program
  halted : Program
