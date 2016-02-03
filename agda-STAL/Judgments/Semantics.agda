module Judgments.Semantics where

open import Util
open import Judgments.Grammar

module SimpleSemantics where
  open import Judgments.SimpleSemantics
  open SimpleGrammar

  evalSmallValue : Vec WordValue ♯regs → SmallValue → WordValue
  evalSmallValue = evalSmallValueₛ

  InstantiateGlobal : Globals → WordValue → InstructionSequence → Set
  InstantiateGlobal = InstantiateGlobalₛ

  infix 3 _⊢_⇒_
  _⊢_⇒_ : Globals → ProgramState → ProgramState → Set
  _⊢_⇒_ = _⊢ₛ_⇒_

  infix 3 ⊢_⇒_
  ⊢_⇒_ : Program → Program → Set
  ⊢_⇒_ = ⊢ₛ_⇒_

  ⊢_⇒ₙ_/_ : Program → ℕ → Program → Set
  ⊢_⇒ₙ_/_ = ⊢ₛ_⇒ₙ_/_

module HighSemantics where
  open import Judgments.HighSemantics
  open HighGrammar

  evalSmallValue : Vec WordValue ♯regs → SmallValue → WordValue
  evalSmallValue = evalSmallValueₕ

  InstantiateGlobal : Globals → WordValue → InstructionSequence → Set
  InstantiateGlobal = InstantiateGlobalₕ

  infix 3 _⊢_⇒_
  _⊢_⇒_ : Globals → ProgramState → ProgramState → Set
  _⊢_⇒_ = _⊢ₕ_⇒_

  infix 3 ⊢_⇒_
  ⊢_⇒_ : Program → Program → Set
  ⊢_⇒_ = ⊢ₕ_⇒_

  ⊢_⇒ₙ_/_ : Program → ℕ → Program → Set
  ⊢_⇒ₙ_/_ = ⊢ₕ_⇒ₙ_/_
