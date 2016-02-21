module Lemmas where

-- Step 5.1:
-- Desidibility and effectiveness lemmas for equality, typing,
-- subtyping and substitution along with properties such
-- that substitution preserves subtyping.
open import Lemmas.Equality using () public
open import Lemmas.Substitution public
open import Lemmas.Types public
open import Lemmas.TypeSubstitution public

-- Step 5.2:
-- Some substitution theorems about terms
open import Lemmas.TermWeaken public
open import Lemmas.TermSubstitution public

-- Step 5.3:
-- Terms can be casted using subtyping, and
-- we can make the heap more specific too.
open import Lemmas.TermCast public
open import Lemmas.TermHeapCast public

-- Step 5.4:
-- Determinism and decidibility the semantics
open import Lemmas.SimpleSemantics public
open import Lemmas.HighSemantics public

-- Step 5.5:
-- If a term has a specific type, then the type is valid
open import Lemmas.TermValidType public

-- Step 5.6: The proof itself
open import Lemmas.MallocStep public
open import Lemmas.HeapSteps public
open import Lemmas.Soundness public

-- Step 6:
-- Prove a bisimulation between the high and simple languages
open import Lemmas.EmbedSimulation public

-- Step 8:
-- Prove that type-checking is decidable
open import Lemmas.TermDec public
