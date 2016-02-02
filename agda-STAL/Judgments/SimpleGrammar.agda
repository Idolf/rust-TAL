module Judgments.SimpleGrammar where

open import Util
open import Judgments.CommonGrammar public

-- The purpose of this file is to introduce the base grammar
-- on which every other file depends.

-- Word value, w
data WordValueₛ : Set where
  globval : GlobLabel → WordValueₛ
  heapval : HeapLabel → WordValueₛ
  int     : ℕ → WordValueₛ
  ns      : WordValueₛ
  uninit  : WordValueₛ

-- Small values, v
data SmallValueₛ : Set where
  reg     : Register → SmallValueₛ
  globval : GlobLabel → SmallValueₛ
  int     : ℕ → SmallValueₛ

-- ι
data Instructionₛ : Set where
  add    : Register → Register → SmallValueₛ → Instructionₛ
  sub    : Register → Register → SmallValueₛ → Instructionₛ
  salloc : ℕ → Instructionₛ
  sfree  : ℕ → Instructionₛ
  sld    : Register → ℕ → Instructionₛ
  sst    : ℕ → Register → Instructionₛ
  ld     : Register → Register → ℕ → Instructionₛ
  st     : Register → ℕ → Register → Instructionₛ
  malloc : Register → ℕ → Instructionₛ
  mov    : Register → SmallValueₛ → Instructionₛ
  beq    : Register → SmallValueₛ → Instructionₛ

-- I
infixr 6 _~>_
data InstructionSequenceₛ : Set where
  _~>_ : Instructionₛ → InstructionSequenceₛ → InstructionSequenceₛ
  jmp : SmallValueₛ → InstructionSequenceₛ
  halt   : InstructionSequenceₛ

-- Global values, g
data GlobalValueₛ : Set where
  code : InstructionSequenceₛ → GlobalValueₛ

-- Global constants, G
Globalsₛ : Set
Globalsₛ = List GlobalValueₛ

-- Heap values, h
data HeapValueₛ : Set where
  tuple : List WordValueₛ → HeapValueₛ

-- Heaps, H
Heapₛ : Set
Heapₛ = List HeapValueₛ

-- Stacks, S
Stackₛ : Set
Stackₛ = List WordValueₛ

-- Register files, R
data RegisterFileₛ : Set where
  register : Stackₛ → Vec WordValueₛ ♯regs → RegisterFileₛ

-- P
ProgramStateₛ : Set
ProgramStateₛ = Heapₛ × RegisterFileₛ × InstructionSequenceₛ

data Programₛ : Set where
  running : Globalsₛ → ProgramStateₛ → Programₛ
  halted : Programₛ
