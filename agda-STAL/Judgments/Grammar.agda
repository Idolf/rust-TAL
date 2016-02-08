module Judgments.Grammar where

open import Judgments.SimpleGrammar public
open import Judgments.HighGrammar public

-- The purpose of this file is to rename the
-- values in SimpleGrammar and HighGrammar

module SimpleGrammar where
  open import Judgments.SimpleGrammar

  WordValue : Set
  WordValue = WordValueₛ

  SmallValue : Set
  SmallValue = SmallValueₛ

  Instruction : Set
  Instruction = Instructionₛ

  InstructionSequence : Set
  InstructionSequence = InstructionSequenceₛ

  GlobalValue : Set
  GlobalValue = GlobalValueₛ

  Globals : Set
  Globals = Globalsₛ

  HeapValue : Set
  HeapValue = HeapValueₛ

  Heap : Set
  Heap = Heapₛ

  Stack : Set
  Stack = Stackₛ

  RegisterFile : Set
  RegisterFile = RegisterFileₛ

  ProgramState : Set
  ProgramState = ProgramStateₛ

  Program : Set
  Program = Programₛ

module HighGrammar where
  open import Judgments.HighGrammar

  WordValue : Set
  WordValue = WordValueₕ

  SmallValue : Set
  SmallValue = SmallValueₕ

  Instruction : Set
  Instruction = Instructionₕ

  InstructionSequence : Set
  InstructionSequence = InstructionSequenceₕ

  GlobalValue : Set
  GlobalValue = GlobalValueₕ

  Globals : Set
  Globals = Globalsₕ

  HeapValue : Set
  HeapValue = HeapValueₕ

  Heap : Set
  Heap = Heapₕ

  Stack : Set
  Stack = Stackₕ

  RegisterFile : Set
  RegisterFile = RegisterFileₕ

  ProgramState : Set
  ProgramState = ProgramStateₕ

  Program : Set
  Program = Programₕ
