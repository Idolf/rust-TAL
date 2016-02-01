module Simple.Grammar where

open import Util

-- The purpose of this file is to introduce the base grammar
-- on which every other file depends.

♯regs : ℕ
♯regs = 4

-- Assignment index, ι
AssignmentIndex : Set
AssignmentIndex = ℕ

-- Registers, ♯r
Register : Set
Register = Fin ♯regs

-- Global labels, l
GlobLabel : Set
GlobLabel = ℕ

-- Heap labels, lₕ
HeapLabel : Set
HeapLabel = ℕ

-- Word value, w
data WordValue : Set where
  globval : GlobLabel → WordValue
  heapval : HeapLabel → WordValue
  int     : ℕ → WordValue
  ns      : WordValue
  uninit  : WordValue

-- Small values, v
data SmallValue : Set where
  reg     : Register → SmallValue
  globval : GlobLabel → SmallValue
  int     : ℕ → SmallValue
  ns      : SmallValue
  uninit  : SmallValue

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
  malloc : Register → ℕ → Instruction
  mov    : Register → SmallValue → Instruction
  beq    : Register → SmallValue → Instruction

-- I
infixr 6 _~>_
data InstructionSequence : Set where
  _~>_ : Instruction → InstructionSequence → InstructionSequence
  jmp : SmallValue → InstructionSequence
  halt   : InstructionSequence

-- Global values, g
data GlobalValue : Set where
  code : InstructionSequence → GlobalValue

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
