module Lemmas.EmbedBisimulation where

open import Util
open import Judgments
open import Lemmas.SimpleSemantics
open import Lemmas.HighSemantics
open import Lemmas.Soundness
open import Lemmas.EmbedSimulation

-- The purpose of this module is to prove that two relations
-- between the high and simple grammar are bisimulations.
-- The two relations are:
-- * {(ℒₕ, embed ℒₕ) | ⊢ ℒₕ program}
-- * {(ℒₕ, embed ℒₕ) | ¬ Stuck ℒₕ}

Rel : Set → Set → Set₁
Rel A B = A → B → Set

record IsBisimulation {A B} (rel : Rel A B) (step-A : Rel A A) (step-B : Rel B B) : Set where
  constructor bisimulation
  field
    forward : ∀ {a a' b} → rel a b → step-A a a' →
                ∃ λ b' →
                    rel a' b' ×
                    step-B b b'
    backwards : ∀ {a b b'} → rel a b → step-B b b' →
                  ∃ λ a' →
                      rel a' b' ×
                      step-A a a'


private
  module S where
    open SimpleGrammar public
    open SimpleSemantics public

  module H where
    open HighGrammar public
    open HighSemantics public

bisim : Rel H.Program S.Program
bisim ℒₕ ℒₛ = embed ℒₕ ≡ ℒₛ × ⊢ ℒₕ program

EmbedBisimulation : IsBisimulation bisim H.⊢_⇒_ S.⊢_⇒_
EmbedBisimulation = bisimulation forwards backwards
  where forwards : ∀ {ℒₕ ℒₕ' ℒₛ} →
                     bisim ℒₕ ℒₛ →
                     H.⊢ ℒₕ ⇒ ℒₕ' →
                     ∃ λ ℒₛ' →
                         bisim ℒₕ' ℒₛ' ×
                         S.⊢ ℒₛ ⇒ ℒₛ'
        forwards (refl , ℒₕ⋆) step
          = _ , (refl , step-reduction ℒₕ⋆ step) , embed-step-prg step

        backwards : ∀ {ℒₕ ℒₛ ℒₛ'} →
                     bisim ℒₕ ℒₛ →
                     S.⊢ ℒₛ ⇒ ℒₛ' →
                     ∃ λ ℒₕ' →
                         bisim ℒₕ' ℒₛ' ×
                         H.⊢ ℒₕ ⇒ ℒₕ'
        backwards (refl , ℒₕ⋆) sstep
          with step-progress⁺ ℒₕ⋆
        ... | ℒₕ' , ℒₕ'⋆ , hstep
          rewrite step-prg-uniqueₛ sstep (embed-step-prg hstep)
            = _ , (refl , ℒₕ'⋆) , hstep

alt-bisim : Rel H.Program S.Program
alt-bisim ℒₕ ℒₛ = embed ℒₕ ≡ ℒₛ × ¬ H.Stuck ℒₕ

AltEmbedBisimulation : IsBisimulation alt-bisim H.⊢_⇒_ S.⊢_⇒_
AltEmbedBisimulation = bisimulation forwards backwards
  where forwards : ∀ {ℒₕ ℒₕ' ℒₛ} →
                     alt-bisim ℒₕ ℒₛ →
                     H.⊢ ℒₕ ⇒ ℒₕ' →
                     ∃ λ ℒₛ' →
                         alt-bisim ℒₕ' ℒₛ' ×
                         S.⊢ ℒₛ ⇒ ℒₛ'
        forwards (refl , ¬stuck) step
          = _ , (refl , (λ stuck → ¬stuck (there step stuck))) , embed-step-prg step

        backwards : ∀ {ℒₕ ℒₛ ℒₛ'} →
                     alt-bisim ℒₕ ℒₛ →
                     S.⊢ ℒₛ ⇒ ℒₛ' →
                     ∃ λ ℒₕ' →
                         alt-bisim ℒₕ' ℒₛ' ×
                         H.⊢ ℒₕ ⇒ ℒₕ'
        backwards  (refl , ¬stuck) sstep
          with ¬Stuck→stepₕ ¬stuck
        ... | ℒₕ' , hstep , ¬stuck'
          rewrite step-prg-uniqueₛ sstep (embed-step-prg hstep)
            = ℒₕ' , (refl , ¬stuck') , hstep
