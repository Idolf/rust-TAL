module Judgments.CommonSyntax where

open import Util

-- This file introduces some definitions that are useful for
-- both the simple and high syntax.

♯regs : ℕ
♯regs = 4

-- Registers, ♯r
Register : Set
Register = Fin ♯regs

-- Global labels, lab
GlobLabel : Set
GlobLabel = ℕ

-- Heap labels, labₕ
HeapLabel : Set
HeapLabel = ℕ
