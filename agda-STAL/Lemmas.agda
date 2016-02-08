module Lemmas where

-- Step 5 requirements:
-- Desidibility and effectiveness lemmas for equality, typing,
-- subtyping and substitution.
open import Lemmas.Equality public
open import Lemmas.Types public
open import Lemmas.Substitution public
open import Lemmas.TypeSubstitution public

open import Lemmas.Embed public


-- Lemmas about the interaction between substitutions
-- and subtyping. The main result is that substitution
-- preserves subtyping.

open import Lemmas.WeakenRight public
open import Lemmas.TermSubtyping public

-- Lemmas about determinism and decidibility of evaluation
-- of smallvalues along with stepping+execution of instructions.
open import Lemmas.SimpleSemantics public
open import Lemmas.HighSemantics public
open import Lemmas.Semantics public

open import Lemmas.Terms public
open import Lemmas.HeapPush public
open import Lemmas.HeapUpdate public
