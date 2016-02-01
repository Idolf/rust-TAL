module Judgments.Subtypes where

-- open import Util
-- open import Judgments.Grammar
-- open import Judgments.Types
-- open HighGrammar

-- -- This file contains judgments to determine subtyping
-- -- relations. As syntactic sugar, we include this record
-- -- and add instances for it:
-- record Subtype (A : Set) : Set1 where
--   constructor subtype
--   infix 3 _⊢_≤_
--   field
--     Subtype-junk : ⊤
-- open Subtype {{...}} public


-- Vec-Subtype : ∀ A m {{S : Subtype A}} → Subtype (Vec A m)
-- Vec-Subtype A m =
--   subtype (λ Δ xs₁ xs₂ → AllZipᵥ (λ x₁ x₂ → Δ ⊢ x₁ ≤ x₂) xs₁ xs₂) tt

-- List-Subtype : ∀ A {{S : Subtype A}} → Subtype (List A)
-- List-Subtype A =
--   subtype (λ Δ xs₁ xs₂ → AllZip (λ x₁ x₂ → Δ ⊢ x₁ ≤ x₂) xs₁ xs₂) tt

-- instance
--   Type-Subtype : Subtype Type
--   Type-Subtype = subtype _⊢_≤τ_ tt

--   TypeVec-Subtype : ∀ {n} → Subtype (Vec Type n)
--   TypeVec-Subtype = Vec-Subtype Type _

--   TypeList-Subtype : Subtype (List Type)
--   TypeList-Subtype = List-Subtype Type

--   InitType-Subtype : Subtype InitType
--   InitType-Subtype = subtype _⊢_≤τ⁻_ tt

--   InitTypeList-Subtype : Subtype (List InitType)
--   InitTypeList-Subtype = List-Subtype InitType

--   StackType-Subtype : Subtype StackType
--   StackType-Subtype = subtype _⊢_≤σ_ tt

--   RegisterAssignment-Subtype : Subtype RegisterAssignment
--   RegisterAssignment-Subtype = subtype _⊢_≤Γ_ tt
