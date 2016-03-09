module Demo where

open import Util

data BinOp : Set where
  add : BinOp
  sub : BinOp
  mul : BinOp

{-
This is the same as the Haskell code:

data BinOp = add | sub | mul
-}
