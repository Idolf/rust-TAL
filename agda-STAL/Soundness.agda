module Soundness where

open import Util
open import Judgments
open import Lemmas
open import Semantics
open import TermSubtyping

weaken-w⋆ : ∀ {ψ₁ ψ₂ w τ} →
              ψ₁ , [] , [] ⊢ w of τ wval →
              ψ₁ , ψ₂ , [] ⊢ w of τ wval
weaken-w⋆ (of-globval l₁ τ₁≤τ₂ eq) = of-globval l₁ τ₁≤τ₂ eq
weaken-w⋆ (of-heapval () τ₁≤τ₂)
weaken-w⋆ of-int = of-int
weaken-w⋆ of-ns = of-ns
weaken-w⋆ (of-inst {Δ₁ = Δ₁} w⋆ c⋆ run-Δ sub-Γ Γ₁≤Γ₂)
  rewrite List-++-right-identity Δ₁ =
    of-inst (weaken-w⋆ w⋆) (valid-++ {A = StrongCast} c⋆) run-Δ sub-Γ Γ₁≤Γ₂

eval-reduction : ∀ {ψ₁ ψ₂ regs σ τs v τ} →
                   AllZipᵥ (λ w τ → ψ₁ , ψ₂ , [] ⊢ w of τ wval) regs τs →
                   ψ₁ , [] , registerₐ σ τs ⊢ v of τ vval →
                   ∃ λ τ' →
                     [] ⊢ τ' ≤ τ ×
                     ψ₁ , ψ₂ , [] ⊢ evalSmallValue regs v of τ' wval
eval-reduction {v = reg ♯r} regs⋆ (of-reg lookup≤τ) =
  _ , lookup≤τ , allzipᵥ-lookup ♯r regs⋆
eval-reduction regs⋆ (of-word w⋆) =
  _ , ≤-refl (wval-valid-type w⋆) , weaken-w⋆ w⋆
eval-reduction regs⋆ (of-inst {Δ₁ = Δ₁} {Δ₂} {Γ₁} {Γ₂} {Γ₃} v⋆ c⋆ run-Δ sub-Γ Γ₂≤Γ₃)
  with eval-reduction regs⋆ v⋆
... | ∀[ .Δ₁ ] Γ₁' , ∀-≤ Δ⋆ Γ₁'≤Γ₁ , eval
  with can-subst c⋆ (run-append run-Δ) (proj₁ (≤-valid Γ₁'≤Γ₁))
... | Γ₂' , sub-Γ' , Γ₂'⋆
  with valid-subtype c⋆ (run-append run-Δ)  Γ₁'≤Γ₁ sub-Γ' sub-Γ
... | Γ₂'≤Γ₂ = ∀[ Δ₂ ] Γ₂' , ∀-≤ (run-valid c⋆ Δ⋆ run-Δ) (≤-trans Γ₂'≤Γ₂ Γ₂≤Γ₃) , of-inst eval c⋆ run-Δ sub-Γ' (≤-refl (proj₁ (≤-valid Γ₂'≤Γ₂)))

stack-lookup-reduction : ∀ {ψ₁ ψ₂ sp σ i w τ} →
                           ψ₁ , ψ₂ ⊢ sp of σ stack →
                           sp ↓ i ⇒ w →
                           stack-lookup i σ τ →
                           ψ₁ , ψ₂ , [] ⊢ w of τ wval
stack-lookup-reduction (w⋆ ∷ sp⋆) here here = w⋆
stack-lookup-reduction (w⋆ ∷ sp⋆) (there l₁) (there l₂) = stack-lookup-reduction sp⋆ l₁ l₂

stack-update-reduction : ∀ {ψ₁ ψ₂ sp sp' σ σ' i w τ} →
                           ψ₁ , ψ₂ , [] ⊢ w of τ wval →
                           ψ₁ , ψ₂ ⊢ sp of σ stack →
                           stack-update i τ σ σ' →
                           sp ⟦ i ⟧← w ⇒ sp' →
                           ψ₁ , ψ₂ ⊢ sp' of σ' stack
stack-update-reduction w⋆ (w'⋆ ∷ sp⋆) here here = w⋆ ∷ sp⋆
stack-update-reduction w⋆ (w'⋆ ∷ sp⋆) (there up₁) (there up₂) = w'⋆ ∷ stack-update-reduction w⋆ sp⋆ up₁ up₂

wval-int : ∀ {ψ₁ ψ₂ H w} →
             ψ₁ ⊢ H of ψ₂ heap →
             ψ₁ , ψ₂ , [] ⊢ w of int wval →
             ∃ λ n →
               w ≡ int n
wval-int H⋆ (of-globval l int-≤ ())
wval-int (of-heap hs⋆) (of-heapval l int-≤)
  with allzip-lookup₂ l hs⋆
... | h , l' , ()
wval-int H⋆ of-int = _ , refl

wval-tuple : ∀ {ψ₁ ψ₂ H w τs⁻} →
               ψ₁ ⊢ H of ψ₂ heap →
               ψ₁ , ψ₂ , [] ⊢ w of tuple τs⁻ wval →
               ∃₂ λ lₕ h →
                 w ≡ heapval lₕ ×
                 H ↓ lₕ ⇒ h ×
                 ψ₁ , ψ₂ ⊢ h of tuple τs⁻ hval
wval-tuple H⋆ (of-globval l (tuple-≤ τs⁻₁≤τs⁻₂) ())
wval-tuple (of-heap hs⋆) (of-heapval l τ₁≤τ₂)
  with allzip-lookup₂ l hs⋆
... | h , l' , h⋆ = _ , h , refl , l' , hval-subtype h⋆ τ₁≤τ₂

run-inst-length : ∀ {Δ₁ Δ₂ i ι} →
                    Run Δ₁ ⟦ inst i / ι ⟧≡ Δ₂ →
                    length Δ₁ ≡ suc (length Δ₂)
run-inst-length (run-inst m) = refl
run-inst-length (run-suc sub-a run-Δ) = cong suc (run-inst-length run-Δ)

run-weaken-length : ∀ {Δ₁ Δ₂ Δ⁺ ι} →
                      Run Δ₁ ⟦ weaken Δ⁺ / ι ⟧≡ Δ₂ →
                      length Δ₁ + length Δ⁺ ≡ length Δ₂
run-weaken-length {Δ₁} {Δ⁺ = Δ⁺} run-weaken rewrite List-length-++ Δ⁺ {Δ₁} = +-comm (length Δ₁) (length Δ⁺)
run-weaken-length (run-suc run-a run-Δ) = cong suc (run-weaken-length run-Δ)

wctx-proof : ∀ {ψ₁ H ψ₂ Δ w Δᵢ Γ} →
               ψ₁ ⊢ H of ψ₂ heap →
               ψ₁ , ψ₂ , Δ ⊢ w of ∀[ Δᵢ ] Γ wval →
               wctx-length w ≡ length Δᵢ
wctx-proof H⋆ (of-globval l (∀-≤ Δ⋆ Γ₁≤Γ₂) eq) rewrite just-injective eq = refl
wctx-proof (of-heap hs⋆) (of-heapval l (∀-≤ Δ⋆ Γ₁≤Γ₂))
  with allzip-lookup₂ l hs⋆
... | h , l' , ()
wctx-proof H⋆ (of-inst {cᵥ = inst i} {ι} w⋆ c⋆ run-Δ sub-Γ Γ₂≤Γ₃)
  rewrite wctx-proof H⋆ w⋆
        | run-inst-length run-Δ = refl
wctx-proof H⋆ (of-inst {cᵥ = weaken Δ⁺} {ι} w⋆ c⋆ run-Δ sub-Γ Γ₂≤Γ₃)
  rewrite wctx-proof H⋆ w⋆
        | run-weaken-length run-Δ = refl

wut : ∀ {Δ Δ' cᵥ ι Δ₁ Δ₁' Δ₂ cₘ} →
        Δ ⊢ cᵥ / ι Valid →
        Run Δ ⟦ cᵥ / ι ⟧≡ Δ' →
        Δ₁ ⟦ Strong→Weak cᵥ / ι ⟧≡ Δ₁' →
        Δ₁ ++ Δ  ⊢ cₘ Valid →
        Run Δ₁ ⟦ cₘ ⟧≡ Δ₂ →
        ∃₂ λ cₘ' Δ₂' →
           cₘ ⟦ Strong→Weak cᵥ / ι ⟧≡ cₘ' ×
           Δ₁' ++ Δ' ⊢ cₘ' Valid ×
           Run Δ₁' ⟦ cₘ' ⟧≡ Δ₂'
wut = {!!}

-- can-subst-w : ∀ {ψ₁ H ψ₂ Δ Δ' cᵥ ι w τ τ'} →
--                 ψ₁ ⊢ H of ψ₂ heap →
--                 Δ ⊢ cᵥ / ι Valid →
--                 Run Δ ⟦ cᵥ / ι ⟧≡ Δ' →
--                 τ ⟦ Strong→Weak cᵥ / ι ⟧≡ τ' →
--                 ψ₁ , ψ₂ , Δ ⊢ w of τ wval →
--                 ∃ λ w' →
--                   w ⟦ Strong→Weak cᵥ / ι ⟧≡ w' ×
--                   ψ₁ , ψ₂ , Δ' ⊢ w' of τ' wval
-- can-subst-w H⋆ c⋆ run-Δ sub-τ (of-globval l lookup≤τ eq)
--   with subst-empty-ctx (proj₂ (≤-valid lookup≤τ)) sub-τ
-- ... | eq' rewrite eq' = _ , subst-globval , of-globval l lookup≤τ eq
-- can-subst-w H⋆ c⋆ run-Δ sub-τ (of-heapval l lookup≤τ)
--   with subst-empty-ctx (proj₂ (≤-valid lookup≤τ)) sub-τ
-- ... | eq' rewrite eq' = _ , subst-heapval , of-heapval l lookup≤τ
-- can-subst-w H⋆ c⋆ run-Δ subst-int of-int = _ , subst-int , of-int
-- can-subst-w H⋆ c⋆ run-Δ subst-ns of-ns = _ , subst-ns , of-ns
-- can-subst-w {ψ₁} {H} {ψ₂} {Δ} {Δ'} {cᵥ} {ι} {w ⟦ cₘ ⟧} {∀[ Δ₂ ] Γ₃} {∀[ Δ₂' ] Γ₃'} H⋆ c⋆ run-Δ (subst-∀ sub-Δ₂ sub-Γ₃) (of-inst .{ψ₁} .{ψ₂} .{Δ} {Δ₁} .{Δ₂} {Γ₁} {Γ₂} .{Γ₃} w⋆ cₘ⋆ run-Δ₁ sub-Γ₁ Γ₂≤Γ₃)
--   with wval-valid-type w⋆
-- ... | valid-∀ Δ₁⋆ Γ₁⋆
--   with can-subst c⋆ run-Δ Δ₁⋆
-- ... | Δ₁' , sub-Δ₁ , Δ₁'⋆
--   with can-subst (c-valid-add-left Δ₁ c⋆) (run-combine sub-Δ₁ run-Δ) Γ₁⋆
-- ... | Γ₁' , sub-Γ₁' , Γ₁'⋆
--   with
--     begin
--       wctx-length w + ι
--     ≡⟨ wctx-proof H⋆ w⋆ ∥ (λ v → v + ι)  ⟩
--       length Δ₁ + ι
--     ∎ where open Eq-Reasoning
-- ... | eq
--   with can-subst-w {ψ₁} {H} {ψ₂} {Δ} {Δ'} {cᵥ / ι} {w} {∀[ Δ₁ ] Γ₁} {∀[ Δ₁' ] Γ₁'} H⋆ c⋆ run-Δ (subst-∀ sub-Δ₁ sub-Γ₁') w⋆
-- ... | w' , sub-w , w'⋆
--   with wut c⋆ run-Δ sub-Δ₁ cₘ⋆ run-Δ₁
-- ... | cₘ' , Δ₂'' , sub-cₘ , cₘ'⋆ , run-Δ₁'
--   = w' ⟦ cₘ' ⟧ , subst-⟦⟧ sub-w {!!} , of-inst w'⋆ {!!} {!!} {!!} {!!}

-- can-subst-v : ∀ {ψ₁ Δ Δ' Γ Γ' c v τ τ'} →
--                 Δ ⊢ c Valid →
--                 Run Δ ⟦ c ⟧≡ Δ' →
--                 Γ ⟦ c ⟧≡ Γ' →
--                 τ ⟦ c ⟧≡ τ' →
--                 ψ₁ , Δ , Γ ⊢ v of τ vval →
--                 ∃ λ v' →
--                   v ⟦ c ⟧≡ v' ×
--                   ψ₁ , Δ' , Γ' ⊢ v' of τ' vval
-- can-subst-v {v = reg ♯r} c⋆ run-Δ (subst-registerₐ sub-sp sub-regs) sub-τ (of-reg lookup≤τ)
--   with allzipᵥ-lookup ♯r sub-regs
-- ... | sub-lookup =
--   reg ♯r , subst-reg , of-reg (valid-subtype {{r = Type-Subtype⁺}} c⋆ run-Δ lookup≤τ sub-lookup sub-τ)
-- can-subst-v c⋆ run-Δ sub-Γ sub-τ (of-word w⋆)
--   with can-subst-w (of-heap []) c⋆ run-Δ sub-τ w⋆
-- ... | w' , sub-w , w'⋆ = word w' , subst-word sub-w , of-word w'⋆
-- can-subst-v c⋆ run-Δ sub-Γ sub-τ (of-inst v⋆ c'⋆ run-Δ' sub-Γ' Γ₂≤Γ₃) = {!!}

-- subst-int-≡ : ∀ {c : WeakCast} {τ : Type} →
--                 int ⟦ c ⟧≡ τ →
--                 τ ≡ int
-- subst-int-≡ subst-int = refl

-- subst-∀-≡ : ∀ {cᵥ : WeakCastValue} {ι} {τ : Type} {Δ Γ} →
--                 ∀[ Δ ] Γ ⟦ cᵥ / ι ⟧≡ τ →
--                 ∃₂ λ Δ' Γ' →
--                   Δ ⟦ cᵥ / ι ⟧≡ Δ' ×
--                   Γ ⟦ cᵥ / length Δ + ι ⟧≡ Γ' ×
--                   τ ≡ (∀[ Δ' ] Γ')
-- subst-∀-≡ (subst-∀ sub-Δ sub-Γ) = _ , _ , sub-Δ , sub-Γ , refl


-- can-subst-ι : ∀ {ψ₁ Δ Δ' Γ₁ Γ₁' Γ₂ c ι} →
--                 Δ ⊢ c Valid →
--                 Run Δ ⟦ c ⟧≡ Δ' →
--                 Γ₁ ⟦ c ⟧≡ Γ₁' →
--                 ψ₁ , Δ , Γ₁ ⊢ ι ⇒ Γ₂ instruction →
--                 ∃₂ λ ι' Γ₂' →
--                   ι ⟦ c ⟧≡ ι' ×
--                   Γ₂ ⟦ c ⟧≡ Γ₂' ×
--                   ψ₁ , Δ' , Γ₁' ⊢ ι' ⇒ Γ₂' instruction
-- can-subst-ι {Γ₁ = registerₐ regs₁ sp₁} {registerₐ regs₁' sp₁'}
--             {ι = add ♯rd ♯rs v}
--             c⋆ run-Δ (subst-registerₐ sub-sp sub-regs) (of-add eq v⋆)
--   with can-subst-v c⋆ run-Δ (subst-registerₐ sub-sp sub-regs) v⋆
-- ... | v' , int , sub-v , subst-int , v'⋆
--   with allzipᵥ-lookup ♯rs sub-regs
-- ... | sub-♯rs rewrite eq =
--   add ♯rd ♯rs v' , registerₐ regs₁' (update ♯rd int sp₁') , subst-add sub-v , subst-registerₐ sub-sp (allzipᵥ-update ♯rd subst-int sub-regs) , of-add (subst-int-≡ sub-♯rs) v'⋆
-- can-subst-ι {Γ₁ = registerₐ regs₁ sp₁} {registerₐ regs₁' sp₁'}
--             {ι = sub ♯rd ♯rs v}
--             c⋆ run-Δ (subst-registerₐ sub-sp sub-regs) (of-sub eq v⋆)
--   with can-subst-v c⋆ run-Δ (subst-registerₐ sub-sp sub-regs) v⋆
-- ... | v' , int , sub-v , subst-int , v'⋆
--   with allzipᵥ-lookup ♯rs sub-regs
-- ... | sub-♯rs rewrite eq =
--   sub ♯rd ♯rs v' , registerₐ regs₁' (update ♯rd int sp₁') , subst-sub sub-v , subst-registerₐ sub-sp (allzipᵥ-update ♯rd subst-int sub-regs) , of-sub (subst-int-≡ sub-♯rs) v'⋆
-- can-subst-ι {Γ₁ = registerₐ regs₁ sp₁} {registerₐ regs₁' sp₁'}
--             {ι = push v}
--             c⋆ run-Δ (subst-registerₐ sub-sp sub-regs) (of-push v⋆)
--   with can-subst-v c⋆ run-Δ (subst-registerₐ sub-sp sub-regs) v⋆
-- ... | v' , τ' , sub-v , sub-τ , v'⋆
--   = push v' , registerₐ (τ' ∷ regs₁') sp₁' , subst-push sub-v , subst-registerₐ (sub-τ ∷ sub-sp) sub-regs , of-push v'⋆
-- can-subst-ι c⋆ run-Δ (subst-registerₐ (sub-τ ∷ sub-sp) sub-regs) of-pop = _ , _ , subst-pop , subst-registerₐ sub-sp sub-regs , of-pop
-- can-subst-ι c⋆ run-Δ sub-Γ (of-sld l) = {!!}
-- can-subst-ι c⋆ run-Δ sub-Γ (of-sst x) = {!!}
-- can-subst-ι c⋆ run-Δ sub-Γ (of-ld x x₁) = {!!}
-- can-subst-ι c⋆ run-Δ sub-Γ (of-st x x₁ x₂ x₃) = {!!}
-- can-subst-ι c⋆ run-Δ sub-Γ (of-malloc x) = {!!}
-- can-subst-ι c⋆ run-Δ sub-Γ (of-mov x) = {!!}
-- can-subst-ι c⋆ run-Δ sub-Γ (of-beq x x₁ x₂) = {!!}

-- can-subst-I : ∀ {ψ₁ Δ Δ' Γ Γ' c I} →
--                 Δ ⊢ c Valid →
--                 Run Δ ⟦ c ⟧≡ Δ' →
--                 Γ ⟦ c ⟧≡ Γ' →
--                 ψ₁ , Δ , Γ ⊢ I instructionsequence →
--                 ∃ λ I' →
--                   I ⟦ c ⟧≡ I' ×
--                   ψ₁ , Δ' , Γ' ⊢ I' instructionsequence
-- can-subst-I c⋆ run-Δ sub-Γ (of-~> ι⋆ I⋆)
--   with can-subst-ι c⋆ run-Δ sub-Γ ι⋆
-- ... | ι' , Γ₂' , sub-ι , sub-Γ₂ , ι'⋆
--   with can-subst-I c⋆ run-Δ sub-Γ₂ I⋆
-- ... | I' , sub-I , I'⋆
--   = ι' ~> I' , subst-~> sub-ι sub-I , of-~> ι'⋆ I'⋆
-- can-subst-I {c = cᵥ / ι} c⋆ run-Δ sub-Γ (of-jmp Γ₁≤Γ₂ v⋆)
--   with can-subst-v c⋆ run-Δ sub-Γ v⋆
-- ... | v' , τ' , sub-v , sub-τ , v'⋆
--   with subst-∀-≡ sub-τ
-- ... | [] , Γ₁' , [] , sub-Γ' , eq rewrite eq
--   with valid-subtype {{r = RegisterAssignment-Subtype⁺}} c⋆ run-Δ Γ₁≤Γ₂ sub-Γ sub-Γ'
-- ... | Γ₁'≤Γ₂' = jmp v' , subst-jmp sub-v , of-jmp Γ₁'≤Γ₂' v'⋆

-- wval-∀ : ∀ {ψ₁ ψ₂ G H w Δ Γ₁} →
--            ⊢ G of ψ₁ globals →
--            ψ₁ ⊢ H of ψ₂ heap →
--            ψ₁ , ψ₂ , [] ⊢ w of ∀[ Δ ] Γ₁ wval →
--            ∃₂ λ I Γ₂ →
--                Δ ⊢ Γ₂ ≤ Γ₁ ×
--                EvalGlobal G w (code[ Δ ] Γ₂ ∙ I) ×
--                ψ₁ ⊢ code[ Δ ] Γ₂ ∙ I of ∀[ Δ ] Γ₂ gval
-- wval-∀ {Δ = Δ} {Γ₁} (of-globals gs⋆) H⋆ (of-globval l (∀-≤ Δ⋆ Γ₂≤Γ₁) eq)
--   with allzip-lookup₂ l gs⋆
-- ... | code[ .Δ ] Γ₂ ∙ I , l' , of-gval Δ⋆' Γ₂⋆ I⋆
--   = I , Γ₂ , ≤-change₁ Γ₂≤Γ₁ Γ₂⋆ , instantiate-globval l' (just-injective eq) , of-gval Δ⋆ Γ₂⋆ I⋆
-- wval-∀ G⋆ (of-heap hs⋆) (of-heapval l (∀-≤ Δ⋆ Γ₂≤Γ₁))
--   with allzip-lookup₂ l hs⋆
-- ... | h , l' , ()
-- wval-∀ {w = w ⟦ c ⟧} G⋆ H⋆ (of-inst {Δ₁ = Δ₁} {Δ₂} {Γ₁} {Γ₂} {Γ₃} .{w} .{c} w⋆ c⋆ run-Δ sub-Γ Γ₂≤Γ₃)
--   with wval-∀ G⋆ H⋆ w⋆
-- ... | I , Γ₁' , Γ₁'≤Γ₁ , eval , (of-gval Δ⋆ Γ⋆ I⋆)
--   rewrite List-++-right-identity Δ₁
--   with can-subst c⋆ run-Δ (proj₁ (≤-valid Γ₁'≤Γ₁))
-- ... | Γ₂' , sub-Γ' , Γ₂'⋆
--   with valid-subtype {{r = RegisterAssignment-Subtype⁺}} c⋆ run-Δ Γ₁'≤Γ₁ sub-Γ' sub-Γ
-- ... | Γ₂'≤Γ₂
--   with can-subst-I c⋆ run-Δ sub-Γ' I⋆
-- ... | I' , sub-I , I'⋆
--   = I' , Γ₂' , ≤-trans Γ₂'≤Γ₂ (≤-change₁ Γ₂≤Γ₃ (proj₂ (≤-valid Γ₂'≤Γ₂))) , instantiate-⟦⟧ eval run-Δ sub-Γ' sub-I , of-gval (run-valid (subst₂ _⊢_Valid (sym (List-++-right-identity Δ₁)) refl c⋆) Δ⋆ run-Δ) Γ₂'⋆ I'⋆
-- --   -- = {!!} , Γ₂' , Γ₂'≤Γ₁' , instantiate-⟦⟧ eval run-Δ sub-Γ₂ {!!}

-- stack-lookup-progress : ∀ {ψ₁ ψ₂ S σ i τ} →
--                           ψ₁ , ψ₂ ⊢ S of σ stack →
--                           stack-lookup i σ τ →
--                           ∃ λ w →
--                             ψ₁ , ψ₂ , [] ⊢ w of τ wval ×
--                             S ↓ i ⇒ w
-- stack-lookup-progress (w⋆ ∷ S⋆) here = _ , w⋆ , here
-- stack-lookup-progress (w⋆ ∷ S⋆) (there l) with stack-lookup-progress S⋆ l
-- ... | w' , w'⋆ , l' = w' , w'⋆ , there l'

-- stack-update-progress : ∀ {ψ₁ ψ₂ S₁ σ₁ σ₂ i w τ} →
--                           ψ₁ , ψ₂ , [] ⊢ w of τ wval →
--                           ψ₁ , ψ₂ ⊢ S₁ of σ₁ stack →
--                           stack-update i τ σ₁ σ₂ →
--                           ∃ λ S₂ →
--                             ψ₁ , ψ₂ ⊢ S₂ of σ₂ stack ×
--                             S₁ ⟦ i ⟧← w ⇒ S₂
-- stack-update-progress w'⋆ (w⋆ ∷ S⋆) here = _ , w'⋆ ∷ S⋆ , here
-- stack-update-progress w'⋆ (w⋆ ∷ S₁⋆) (there up)
--   with stack-update-progress w'⋆ S₁⋆ up
-- ... | S₂ , S₂⋆ , up' = _ , w⋆ ∷ S₂⋆ , there up'

-- exec-progress : ∀ {G} {P : ProgramState} →
--                    G ⊢ P program →
--                    ∃ λ P' → G ⊢ P ⇒ P'
-- exec-progress (of-program {I = add ♯rd ♯rs v ~> I} G⋆ H⋆
--                           (of-register sp⋆ regs⋆)
--                           (of-~> (of-add eq v⋆) I⋆))
--   with eval-reduction regs⋆ v⋆
-- ... | int , int-≤ , eval
--   with wval-int H⋆ eval | allzipᵥ-lookup ♯rs regs⋆
-- ... | n₁ , eq₁ | rs⋆
--   rewrite eq with wval-int H⋆ rs⋆
-- ... | n₂ , eq₂ = _ , exec-add eq₁ eq₂
-- exec-progress (of-program {I = sub ♯rd ♯rs v ~> I} G⋆ H⋆
--                           (of-register sp⋆ regs⋆)
--                           (of-~> (of-sub eq v⋆) I⋆))
--   with eval-reduction regs⋆ v⋆
-- ... | int , int-≤ , eval
--   with wval-int H⋆ eval | allzipᵥ-lookup ♯rs regs⋆
-- ... | n₁ , eq₁ | rs⋆
--   rewrite eq with wval-int H⋆ rs⋆
-- ... | n₂ , eq₂ = _ , exec-sub eq₁ eq₂
-- exec-progress (of-program G⋆ H⋆ R⋆ (of-~> (of-push v⋆) I⋆)) = _ , exec-push
-- exec-progress (of-program {I = pop ~> I} G⋆ H⋆
--                           (of-register (τ⋆ ∷ sp⋆) regs⋆)
--                           (of-~> of-pop I⋆)) = _ , exec-pop
-- exec-progress (of-program {I = sld ♯rd i ~> I} G⋆ H⋆
--                           (of-register sp⋆ regs⋆)
--                           (of-~> (of-sld l) I⋆))
--   with stack-lookup-progress sp⋆ l
-- ... | w , w⋆ , l' = _ , exec-sld l'
-- exec-progress (of-program {I = sst i ♯rs ~> I} G⋆ H⋆
--                           (of-register sp⋆ regs⋆)
--                           (of-~> (of-sst up) I⋆))
--   with allzipᵥ-lookup ♯rs regs⋆
-- ... | rs⋆
--   with stack-update-progress rs⋆ sp⋆ up
-- ... | sp' , sp'⋆ , up' = _ , exec-sst up'
-- exec-progress (of-program {I = ld ♯rd ♯rs i ~> I} G⋆ H⋆
--                           (of-register sp⋆ regs⋆)
--                           (of-~> (of-ld eq l) I⋆))
--   with allzipᵥ-lookup ♯rs regs⋆
-- ... | rs⋆
--   rewrite eq with wval-tuple H⋆ rs⋆
-- ... | lₕ , tuple ws , eq' , l' , (of-tuple ws⋆)
--   with allzip-lookup₂ l ws⋆
-- ... | w' , l'' , of-init w'⋆ = _ , exec-ld eq' l' l''
-- exec-progress (of-program {H = H} {I = st ♯rd i ♯rs ~> I} G⋆ H⋆
--                           (of-register {regs = regs} sp⋆ regs⋆)
--                           (of-~> (of-st eq₁ lookup≤τ l up) I⋆))
--   with allzipᵥ-lookup ♯rd regs⋆ | allzipᵥ-lookup ♯rs regs⋆
-- ... | rd⋆ | rs⋆
--   rewrite eq₁ with wval-tuple H⋆ rd⋆
-- ... | lₕ , tuple ws , eq₂ , l' , (of-tuple ws⋆)
--   with allzip-lookup₂ l ws⋆
-- ... | w' , l'' , w'⋆
--   with <-to-← ws (lookup ♯rs regs) {i} (↓-to-< l'')
-- ... | ws' , up'
--   with <-to-← H (tuple ws') {lₕ} (↓-to-< l')
-- ... | H' , up''
--   = _ , exec-st eq₂ l' up' up''
-- exec-progress (of-program G⋆ H⋆ R⋆ (of-~> (of-malloc τs⋆) I⋆)) = _ , exec-malloc
-- exec-progress (of-program G⋆ H⋆ R⋆ (of-~> (of-mov v⋆) I⋆)) = _ , exec-mov
-- exec-progress (of-program {I = beq ♯r v ~> I} G⋆ H⋆
--                           (of-register sp⋆ regs⋆)
--                           (of-~> (of-beq {Γ = Γ} {Γ'} eq₁ Γ≤Γ' v⋆) I⋆))
--   with allzipᵥ-lookup ♯r regs⋆
-- ... | rs⋆ rewrite eq₁ with wval-int H⋆ rs⋆
-- ... | n , eq₂ with n ≟ 0
-- ... | no n≢0 = _ , exec-beq₁ eq₂ n≢0
-- ... | yes eq₃
--   rewrite eq₃
--   with eval-reduction regs⋆ v⋆
-- ... | ∀[ [] ] Γ'' , ∀-≤ [] Γ''≤Γ' , eval
--   with wval-∀ G⋆ H⋆ eval
-- ... | I' , Γ₂ , Γ₂≤Γ₁ , eval' , I⋆' = _ , exec-beq₀ eq₂ eval'
-- exec-progress (of-program {I = jmp v} G⋆ H⋆
--                           (of-register sp⋆ regs⋆)
--                           (of-jmp Γ≤Γ' v⋆))
--   with eval-reduction regs⋆ v⋆
-- ... | ∀[ [] ] Γ'' , ∀-≤ [] Γ''≤Γ' , eval
--   with wval-∀ G⋆ H⋆ eval
-- ... | I' , Γ₂ , Γ₂≤Γ₁ , eval' , I⋆' = _ , exec-jmp eval'
