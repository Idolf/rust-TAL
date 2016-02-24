module Judgments.HighSyntax where

open import Util
open import Judgments.CommonSyntax public

-- The purpose of this file is to define the high syntax.

-- Assignment index, ι
AssignmentIndex : Set
AssignmentIndex = ℕ

mutual
  -- Types, τ
  infix 7  ∀[_]_
  data Type : Set where
    α⁼     : AssignmentIndex → Type
    int    : Type
    uninit : Type
    ∀[_]_  : TypeAssumptions → RegisterAssignment → Type
    tuple  : List InitType → Type

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

-- Instantiation, θ
data Instantiation : Set where
  α : Type → Instantiation
  ρ : StackType → Instantiation

-- Instantiations, θs
Instantiations : Set
Instantiations = List Instantiation

-- Word value, w
infixl 6 Λ_∙_⟦_⟧
data WordValueₕ : Set where
  globval : GlobLabel → WordValueₕ
  heapval : HeapLabel → WordValueₕ
  int     : ℕ → WordValueₕ
  uninit  : WordValueₕ
  Λ_∙_⟦_⟧ : TypeAssumptions → WordValueₕ → Instantiations → WordValueₕ

-- Small values, v
data SmallValueₕ : Set where
  reg     : Register → SmallValueₕ
  globval : GlobLabel → SmallValueₕ
  int     : ℕ → SmallValueₕ
  Λ_∙_⟦_⟧ : TypeAssumptions → SmallValueₕ → Instantiations → SmallValueₕ

-- ι
data Instructionₕ : Set where
  add    : Register → Register → SmallValueₕ → Instructionₕ
  sub    : Register → Register → SmallValueₕ → Instructionₕ
  salloc : ℕ → Instructionₕ
  sfree  : ℕ → Instructionₕ
  sld    : Register → ℕ → Instructionₕ
  sst    : ℕ → Register → Instructionₕ
  ld     : Register → Register → ℕ → Instructionₕ
  st     : Register → ℕ → Register → Instructionₕ
  malloc : Register → List Type → Instructionₕ
  mov    : Register → SmallValueₕ → Instructionₕ
  beq    : Register → SmallValueₕ → Instructionₕ

-- I
infixr 8 _~>_
data InstructionSequenceₕ : Set where
  _~>_ : Instructionₕ → InstructionSequenceₕ → InstructionSequenceₕ
  jmp : SmallValueₕ → InstructionSequenceₕ
  halt : InstructionSequenceₕ

-- Global values, g
infix 7 code[_]_∙_
data GlobalValueₕ : Set where
  code[_]_∙_ :
    TypeAssumptions → RegisterAssignment → InstructionSequenceₕ → GlobalValueₕ

-- Global constants, G
Globalsₕ : Set
Globalsₕ = List GlobalValueₕ

-- Heap values, h
data HeapValueₕ : Set where
  tuple : List Type → List WordValueₕ → HeapValueₕ

-- Heapₕs, H
Heapₕ : Set
Heapₕ = List HeapValueₕ

-- Stackₕs, S
Stackₕ : Set
Stackₕ = List WordValueₕ

-- Register files, R
data RegisterFileₕ : Set where
  register : Stackₕ → Vec WordValueₕ ♯regs → RegisterFileₕ

-- Program states, P
ProgramStateₕ : Set
ProgramStateₕ = Globalsₕ × Heapₕ × RegisterFileₕ × InstructionSequenceₕ

-- The mutable part of program states, Pₘ
MutProgramStateₕ : Set
MutProgramStateₕ = Heapₕ × RegisterFileₕ × InstructionSequenceₕ
