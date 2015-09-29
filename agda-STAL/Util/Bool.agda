module Util.Bool where

open import Data.Bool using (Bool ; true ; false) public
import Data.Bool as B

open import Util.Eq
open import Util.Tree
open import Util.Maybe

instance
  Bool-ToTree : ToTree Bool
  Bool-ToTree = tree (λ { true       → T₀ 0      ; false → T₀ 1 })
                     (λ { (node 0 _) → Just true ; _     → Just false })
                     (λ { true       → refl      ; false → refl })
