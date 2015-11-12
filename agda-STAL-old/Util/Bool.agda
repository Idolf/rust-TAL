module Util.Bool where

-- Re-exports
open import Data.Bool using (Bool ; true ; false) public

-- Local imports
open import Util.Maybe
open import Util.Eq
open import Util.Tree
open import Data.Product using (_,_)

instance
  Bool-ToTree : ToTree Bool
  Bool-ToTree = tree⋆ (λ { (node 0 _) → just true   ; _     → just false })
                      (λ { true       → T₀ 0 , refl ; false → T₀ 1 , refl})
