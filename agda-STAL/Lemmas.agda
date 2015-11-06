module Lemmas where

-- Various small helper lemmas, that
-- does not fit in very well in other places
open import Lemmas.Misc public

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

-- Lemmas about updating TypeAssignment's using
-- substitutions. It contains a uniqueness-proof,
-- a decidibility-proof and a proof that it is always
-- possible to update with a valid substitution
open import Lemmas.Run public

-- Lemmas about lookup and update of StackTypes.
-- Includes uniqueness proofs and decidibility proofs.
open import Lemmas.StackLookup public
