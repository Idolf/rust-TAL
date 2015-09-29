module Util.Bool where

open import Data.Bool using (Bool ; true ; false) public
import Data.Bool as B

open import Util.Dec

instance
  Bool-dec-eq : DecEq Bool
  Bool-dec-eq = decEq B._≟_
