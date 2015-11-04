module Wut where

open import Substitution
open import Grammar
open import TypeJudgments
open import Util
open import SubstitutionLemmas
import Data.Nat as N
import Data.Nat.Properties as NP
import Data.List as L
import Algebra as A
open A.CommutativeSemiring NP.commutativeSemiring using (+-comm ; +-assoc)
open NP.SemiringSolver
  using (prove; solve; _:=_; con; var; _:+_; _:*_; :-_; _:-_)
