module Util.Fin where

open import Data.Fin using (Fin ; zero ; suc) public
import Data.Fin.Properties as FP

open import Util.Dec

instance
  Fin-dec-eq : ∀ {n} → DecEq (Fin n)
  Fin-dec-eq = decEq FP._≟_
