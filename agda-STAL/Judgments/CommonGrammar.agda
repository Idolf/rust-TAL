module Judgments.CommonGrammar where

open import Util

♯regs : ℕ
♯regs = 4

-- Registers, ♯r
Register : Set
Register = Fin ♯regs

-- Global labels, l
GlobLabel : Set
GlobLabel = ℕ

-- Heap labels, lₕ
HeapLabel : Set
HeapLabel = ℕ
