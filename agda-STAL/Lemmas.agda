module Lemmas where

-- Lemmas about lookup and update of StackTypes.
-- Includes uniqueness proofs and decidibility proofs.
open import Lemmas.StackOperations public

-- Equality is decidable for the base grammar
open import Lemmas.Equality public

-- Lemmas about types, substitutions and how they interact
open import Lemmas.Types public
open import Lemmas.Substitution public
open import Lemmas.TypeSubstitution public

-- Lemmas about the interaction between substitutions
-- and subtyping. The main result is that substitution
-- preserves subtyping.

-- Lemmas about determinism and decidibility of evaluation
-- of smallvalues along with stepping+execution of instructions.
open import Lemmas.SimpleSemantics public
open import Lemmas.HighSemantics public
open import Lemmas.Semantics public

open import Lemmas.Terms public
