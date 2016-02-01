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
        embed-rel HP SP = embed HP ≡ SP ×
                          ⊢ HP program

        forwards : ∀ {HP HP' SP} →
                     embed-rel HP SP →
                     H.⊢ HP ⇒ HP' →
                     ∃ λ SP' →
                         embed-rel HP' SP' ×
                         S.⊢ SP ⇒ SP'
        forwards (refl , HP⋆) step
          = _ , (refl , step-reduction HP⋆ step) , embed-step-prg step

        backwards : ∀ {HP SP SP'} →
                     embed-rel HP SP →
                     S.⊢ SP ⇒ SP' →
                     ∃ λ HP' →
                         embed-rel HP' SP' ×
                         H.⊢ HP ⇒ HP'
        backwards (refl , HP⋆) sstep
          with step-progress HP⋆
        ... | HP' , HP'⋆ , hstep
          with embed-step-prg hstep
        ... | sstep'
          rewrite step-prg-uniqueₛ sstep sstep'
            = _ , (refl , HP'⋆) , hstep

-- TODO
steps-soundness : ∀ {n P₁ P₂} →
                    ⊢ P₁ program →
                    ⊢ embed P₁ ⇒ₙ n / P₂ →
                    ∃ λ P₃ →
                      ⊢ P₂ ⇒ P₃
steps-soundness P⋆ steps = step-progress (steps-reduction P⋆ steps)
