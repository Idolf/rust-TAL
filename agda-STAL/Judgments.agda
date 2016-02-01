module Judgments where

-- Step 1: Base Grammar
open import Judgments.CommonGrammar public
open import Judgments.SimpleGrammar public
open import Judgments.HighGrammar public
open import Judgments.Grammar public

-- Step 2: Language translations
open import Judgments.Embed public

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
