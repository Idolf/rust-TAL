module Lemmas where

-- Step 5.1:
-- Desidibility and effectiveness lemmas for equality, typing,
-- subtyping and substitution along with properties such
-- that substitution preserves subtyping.
open import Lemmas.Substitution public
open import Lemmas.Equality public
open import Lemmas.Types public
open import Lemmas.TypeSubstitution public

-- Step 5.2:
-- Terms can be casted using subtyping
open import Lemmas.TermCasting public

-- Step 5.3:
-- Some substitution theorems about instructionsequences
open import Lemmas.InstructionSequenceWeaken public
open import Lemmas.InstructionSequenceSubstitution public

-- Step 5.3:
-- Determinism and decidibility the semantics
open import Lemmas.SimpleSemantics public
open import Lemmas.HighSemantics public

-- Step 5.4:
-- If a term has a specific type, then the type is valid
open import Lemmas.TermValidType public

-- Step 5.4: The proof itself
open import Lemmas.MallocStep public
open import Lemmas.HeapSteps public
open import Lemmas.Soundness public

-- Step 6
open import Lemmas.EmbedSimulation public
open import Lemmas.EmbedBisimulation public
