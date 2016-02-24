module Judgments.Syntax where

open import Judgments.SimpleSyntax public
open import Judgments.HighSyntax public

-- The purpose of this file is to rename the
-- values in SimpleSyntax and HighSyntax

module SimpleSyntax where
  open import Judgments.SimpleSyntax

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

  MutProgramState : Set
  MutProgramState = MutProgramStateₛ

module HighSyntax where
  open import Judgments.HighSyntax

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

  MutProgramState : Set
  MutProgramState = MutProgramStateₕ
