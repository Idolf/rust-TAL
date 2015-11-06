module Judgments where

-- Has the base grammar on which everything depends
open import Judgments.Grammar public

-- Judgments showing if a type-like object is valid
open import Judgments.Types public

-- Judgments showing of a type-like object is a subtype of another
open import Judgments.Subtypes public

-- Substitution judgments
open import Judgments.Substitution public

-- "Run" judgments, i.e. updating an assumption list
-- by removing/adding assumptions
open import Judgments.Run public

-- The equivalent of _↓_⇒_ for StackTypes
open import Judgments.StackLookup public

-- Judgments to show if a term is valid
open import Judgments.Terms public

-- The small-step semantics for our language
open import Judgments.Semantics public
