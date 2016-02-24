module Judgments where

-- Step 1: Base Syntax
open import Judgments.CommonSyntax public
open import Judgments.SimpleSyntax public
open import Judgments.HighSyntax public
open import Judgments.Syntax public

-- Step 2: Language translations
open import Judgments.Erase public

-- Step 3 requirements: Substitution Judgments
-- (needed for the high semantics)
open import Judgments.Substitution public

-- Step 3: Semantics
open import Judgments.SimpleSemantics public
open import Judgments.HighSemantics public
open import Judgments.Semantics public

-- Step 4 requirements: Stack operations
-- (needed for the term judgments)
open import Judgments.StackOperations public

-- Step 4: Typing Judgments
open import Judgments.Types public
open import Judgments.Terms public
