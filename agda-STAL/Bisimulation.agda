module Bisimulation where

open import Util
open import Judgments
open import Lemmas
open import Soundness

private
  module S where
    open SimpleGrammar public
    open SimpleSemantics public
    open SimpleSemanticsLemmas public

  module H where
    open HighGrammar public
    open HighSemantics public
    open HighSemanticsLemmas public

Rel : Set → Set → Set₁
Rel A B = A → B → Set

record Bisimulation (A : Set) (B : Set) : Set₁ where
  constructor bisimulation
  field
    rel : Rel A B
    step-A : Rel A A
    step-B : Rel B B
    forward : ∀ {a a' b} → rel a b → step-A a a' →
                ∃ λ b' →
                    rel a' b' ×
                    step-B b b'
    backwards : ∀ {a b b'} → rel a b → step-B b b' →
                  ∃ λ a' →
                      rel a' b' ×
                      step-A a a'

EmbedBisimulation : Bisimulation H.Program S.Program
EmbedBisimulation = bisimulation embed-rel H.⊢_⇒_ S.⊢_⇒_ forwards backwards
  where embed-rel : Rel H.Program S.Program
        embed-rel ℒₚ ℒₛ = embed ℒₚ ≡ ℒₛ ×
                          ⊢ ℒₚ program

        forwards : ∀ {ℒₚ ℒₚ' ℒₛ} →
                     embed-rel ℒₚ ℒₛ →
                     H.⊢ ℒₚ ⇒ ℒₚ' →
                     ∃ λ ℒₛ' →
                         embed-rel ℒₚ' ℒₛ' ×
                         S.⊢ ℒₛ ⇒ ℒₛ'
        forwards (refl , ℒₚ⋆) step
          = _ , (refl , step-reduction ℒₚ⋆ step) , embed-step-prg step

        backwards : ∀ {ℒₚ ℒₛ ℒₛ'} →
                     embed-rel ℒₚ ℒₛ →
                     S.⊢ ℒₛ ⇒ ℒₛ' →
                     ∃ λ ℒₚ' →
                         embed-rel ℒₚ' ℒₛ' ×
                         H.⊢ ℒₚ ⇒ ℒₚ'
        backwards (refl , ℒₚ⋆) sstep
          with step-progress ℒₚ⋆
        ... | ℒₚ' , ℒₚ'⋆ , hstep
          with embed-step-prg hstep
        ... | sstep'
          rewrite step-prg-uniqueₛ sstep sstep'
            = _ , (refl , ℒₚ'⋆) , hstep

-- TODO
-- steps-soundness : ∀ {n ℒ₁ ℒ₂} →
--                     ⊢ ℒ₁ program →
--                     ⊢ embed ℒ₁ ⇒ₙ n / ℒ₂ →
--                     ∃ λ ℒ₃ →
--                       ⊢ ℒ₂ ⇒ ℒ₃
-- steps-soundness ℒ⋆ steps = step-progress (steps-reduction ℒ⋆ steps)
