module Simple.Bisimulation where

open import Util
open import Judgments
open import Soundness
open import Judgments.Grammar as H
open import Simple.Grammar as S
open import Judgments.Semantics as HS
open import Simple.Semantics as SS
open import Simple.SemanticsLemmas as SL
open import Simple.Embed
open import Simple.EmbedSemantics

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
EmbedBisimulation = bisimulation embed-rel HS.⊢_⇒_ SS.⊢_⇒_ forwards backwards
  where embed-rel : Rel H.Program S.Program
        embed-rel HP SP = embed HP ≡ SP ×
                          ⊢ HP program

        forwards : ∀ {HP HP' SP} →
                     embed-rel HP SP →
                     HS.⊢ HP ⇒ HP' →
                     ∃ λ SP' →
                         embed-rel HP' SP' ×
                         SS.⊢ SP ⇒ SP'
        forwards (refl , HP⋆) step
          = _ , (refl , step-reduction HP⋆ step) , embed-step-prg step

        backwards : ∀ {HP SP SP'} →
                     embed-rel HP SP →
                     SS.⊢ SP ⇒ SP' →
                     ∃ λ HP' →
                         embed-rel HP' SP' ×
                         HS.⊢ HP ⇒ HP'
        backwards (refl , HP⋆) sstep
          with step-progress HP⋆
        ... | HP' , HP'⋆ , hstep
          with embed-step-prg hstep
        ... | sstep'
          rewrite SL.step-prg-unique sstep sstep'
            = _ , (refl , HP'⋆) , hstep
