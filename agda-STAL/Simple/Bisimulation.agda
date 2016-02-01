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
EmbedBisimulation = bisimulation embed-rel step-H step-S forwards backwards
  where embed-rel : Rel H.Program S.Program
        embed-rel HP SP = embed HP ≡ SP ×
                          ⊢ HP program

        step-H : Rel H.Program H.Program
        step-H (G , P) (G' , P') = G ≡ G' × G HS.⊢ P ⇒ P'

        step-S : Rel S.Program S.Program
        step-S (G , P) (G' , P') = G ≡ G' × G SS.⊢ P ⇒ P'

        forwards : ∀ {HP HP' SP} →
                     embed-rel HP SP →
                     step-H HP HP' →
                     ∃ λ SP' →
                         embed-rel HP' SP' ×
                         step-S SP SP'
        forwards (refl , HP⋆) (refl , step)
          = _ , (refl , step-reduction HP⋆ step) , (refl , embed-step step)

        backwards : ∀ {HP SP SP'} →
                     embed-rel HP SP →
                     step-S SP SP' →
                     ∃ λ HP' →
                         embed-rel HP' SP' ×
                         step-H HP HP'
        backwards (refl , HP⋆) (refl , sstep)
          with step-progress HP⋆
        ... | HP' , HP'⋆ , hstep
          with embed-step hstep
        ... | sstep'
          rewrite SL.step-unique sstep sstep'
            = _ , (refl , HP'⋆) , (refl , hstep)
