module Judgments.Semantics where

open import Util
open import Judgments.Grammar

-- The purpose of this file is to rename the
-- values in SimpleSemantics and HighSemantics

module SimpleSemantics where
  open import Judgments.SimpleSemantics
  open SimpleGrammar

  evalSmallValue : Vec WordValue ♯regs → SmallValue → WordValue
  evalSmallValue = evalSmallValueₛ

  InstantiateGlobal : Globals → WordValue → InstructionSequence → Set
  InstantiateGlobal = InstantiateGlobalₛ

  infix 3 _⊢_⇒_
  _⊢_⇒_ : Globals → MutProgramState → MutProgramState → Set
  _⊢_⇒_ = _⊢ₛ_⇒_

  infix 3 ⊢_⇒_
  ⊢_⇒_ : ProgramState → ProgramState → Set
  ⊢_⇒_ = ⊢ₛ_⇒_

  ⊢_⇒ₙ_/_ : ProgramState → ℕ → ProgramState → Set
  ⊢_⇒ₙ_/_ = ⊢ₛ_⇒ₙ_/_

  Halting : ProgramState → Set
  Halting = Haltingₛ

  Progressing : ProgramState → Set
  Progressing = Progressingₛ

  GoodState : ProgramState → Set
  GoodState = GoodStateₛ

module HighSemantics where
  open import Judgments.HighSemantics
  open HighGrammar

  evalSmallValue : Vec WordValue ♯regs → SmallValue → WordValue
  evalSmallValue = evalSmallValueₕ

  InstantiateGlobal : Globals → WordValue → InstructionSequence → Set
  InstantiateGlobal = InstantiateGlobalₕ

  infix 3 _⊢_⇒_
  _⊢_⇒_ : Globals → MutProgramState → MutProgramState → Set
  _⊢_⇒_ = _⊢ₕ_⇒_

  infix 3 ⊢_⇒_
  ⊢_⇒_ : ProgramState → ProgramState → Set
  ⊢_⇒_ = ⊢ₕ_⇒_

  ⊢_⇒ₙ_/_ : ProgramState → ℕ → ProgramState → Set
  ⊢_⇒ₙ_/_ = ⊢ₕ_⇒ₙ_/_

  Halting : ProgramState → Set
  Halting = Haltingₕ

  Progressing : ProgramState → Set
  Progressing = Progressingₕ

  GoodState : ProgramState → Set
  GoodState = GoodStateₕ
