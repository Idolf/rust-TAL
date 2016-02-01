module Lemmas where

-- Lemmas about lookup and update of StackTypes.
-- Includes uniqueness proofs and decidibility proofs.
open import Lemmas.StackLookup public

-- Equality is decidable for the base grammar
open import Lemmas.Equality public

-- Lemmas about types, primarily decidable validity
open import Lemmas.Types public

-- Lemmas about subtyping, primarily that
-- it is decidable, that it is a preorder and that
-- implies validity
open import Lemmas.Subtypes public

-- Lemmas about substitution, primarily
-- that it is decidable and unique
open import Lemmas.Substitution public

-- Lemmas about the interaction between substitutions
-- and type-validity. The main result is that a substitution
-- is always possible, given a valid substitution and
-- a valid type-like object.
open import Lemmas.TypeSubstitution public

-- Lemmas about the interaction between substitutions
-- and subtyping. The main result is that substitution
-- preserves subtyping.
open import Lemmas.SubtypeSubstitution public

-- Lemmas about determinism and decidibility of evaluation
-- of smallvalues along with stepping+execution of instructions.
open import Lemmas.Semantics public

open import Lemmas.Terms public
