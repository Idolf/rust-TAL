module Lemmas.Embed where

open import Util
open import Judgments
open import Data.List using (drop)

private
  module S where
    open SimpleGrammar public
    open SimpleSemantics public

  module H where
    open HighGrammar public
    open HighSemantics public

private
  embed-↓ : ∀ {A B : Set} {{E : Embed A B}}
                 {xs : List A} {i x} →
                 xs ↓ i ⇒ x →
                 embed {{ListEmbed E}} xs ↓ i ⇒ embed x
  embed-↓ here = here
  embed-↓ (there l) = there (embed-↓ l)

  embed-← : ∀ {A B : Set} {{E : Embed A B}}
                 {xs xs' : List A} {i x} →
                 xs ⟦ i ⟧← x ⇒ xs' →
                 embed {{ListEmbed E}} xs ⟦ i ⟧← embed x ⇒ embed {{ListEmbed E}} xs'
  embed-← here = here
  embed-← (there l) = there (embed-← l)

  embed-lookup : ∀ {A B : Set} {{E : Embed A B}}
                {n} i (xs : Vec A n) →
                embed (lookup i xs) ≡ lookup i (embed {{VecEmbed E}} xs)
  embed-lookup zero (x ∷ xs) = refl
  embed-lookup (suc i) (x ∷ xs) = embed-lookup i xs

  embed-update : ∀ {A B : Set} {{E : Embed A B}}
                   {n} i x (xs : Vec A n) →
                   embed {{VecEmbed E}} (update i x xs) ≡ update i (embed x) (embed {{VecEmbed E}} xs)
  embed-update zero w (w' ∷ ws) = refl
  embed-update (suc i) w (w' ∷ ws) = cong₂ _∷_ refl (embed-update i w ws)

  replicate-ns : ∀ n (sp : H.Stack) →
                   embed (replicate n ns ++ sp) ≡ replicate n ns ++ embed sp
  replicate-ns zero sp = refl
  replicate-ns (suc n) sp = cong₂ _∷_ refl (replicate-ns n sp)

  drop-helper : ∀ {n} {sp sp' : H.Stack} →
                  Drop n sp sp' →
                  embed sp' ≡ drop n (embed sp)
  drop-helper here = refl
  drop-helper (there drop) = drop-helper drop

  uninit-helper : ∀ (τs : List Type) →
                    embed {{ListEmbed embedWordValue}} (map uninit τs) ≡ replicate (length τs) uninit
  uninit-helper [] = refl
  uninit-helper (τ ∷ τs) = cong₂ _∷_ refl (uninit-helper τs)

  malloc-helper : ∀ (H : H.Heap) τs →
                    embed (H ∷ʳ tuple (map uninit τs)) ≡ embed H ∷ʳ tuple (replicate (length τs) uninit)
  malloc-helper [] τs = cong (λ w → [ tuple w ]) (uninit-helper τs)
  malloc-helper (h ∷ H) τs = cong₂ _∷_ refl (malloc-helper H τs)

  embed-length : ∀ {A B : Set} {{E : Embed A B}} xs →
                   length (embed {{ListEmbed E}} xs) ≡ length xs
  embed-length [] = refl
  embed-length (x ∷ xs) = cong suc (embed-length xs)

  embed-subst-v : ∀ {v v' : H.SmallValue} {i pos} →
                    v ⟦ i / pos ⟧≡ v' →
                    embed v ≡ embed v'
  embed-subst-v subst-reg = refl
  embed-subst-v subst-globval = refl
  embed-subst-v subst-int = refl
  embed-subst-v (subst-Λ sub-v subs-I) = embed-subst-v sub-v

  embed-subst-ι : ∀ {ι ι' : H.Instruction} {i pos} →
                    ι ⟦ i / pos ⟧≡ ι' →
                    embed ι ≡ embed ι'
  embed-subst-ι {add ♯rd ♯rs v} (subst-add sub-v) = cong (add ♯rd ♯rs) (embed-subst-v sub-v)
  embed-subst-ι {sub ♯rd ♯rs v} (subst-sub sub-v) = cong (sub ♯rd ♯rs) (embed-subst-v sub-v)
  embed-subst-ι subst-salloc = refl
  embed-subst-ι subst-sfree = refl
  embed-subst-ι subst-sld = refl
  embed-subst-ι subst-sst = refl
  embed-subst-ι subst-ld = refl
  embed-subst-ι subst-st = refl
  embed-subst-ι (subst-malloc sub-τs) = cong₂ malloc refl (help sub-τs)
    where help : ∀ {τs τs' : List Type} {i pos} →
                   τs ⟦ i / pos ⟧≡ τs' →
                   length τs ≡ length τs'
          help [] = refl
          help (sub-τ ∷ sub-τs) = cong suc (help sub-τs)

  embed-subst-ι (subst-mov sub-v) = cong₂ mov refl (embed-subst-v sub-v)
  embed-subst-ι (subst-beq sub-v) = cong₂ beq refl (embed-subst-v sub-v)

  embed-subst-I : ∀ {I I' : H.InstructionSequence} {i pos} →
                    I ⟦ i / pos ⟧≡ I' →
                    embed I ≡ embed I'
  embed-subst-I (subst-~> sub-ι sub-I) = cong₂ _~>_ (embed-subst-ι sub-ι) (embed-subst-I sub-I)
  embed-subst-I (subst-jmp sub-v) = cong jmp (embed-subst-v sub-v)
  embed-subst-I subst-halt = refl

  embed-subst-I-many : ∀ {I I' : H.InstructionSequence} {is pos} →
                         I ⟦ is / pos ⟧many≡ I' →
                         embed I ≡ embed I'
  embed-subst-I-many [] = refl
  embed-subst-I-many (sub-I ∷ subs-I)
    rewrite embed-subst-I sub-I
      = embed-subst-I-many subs-I

embed-eval : ∀ regs v →
               embed (H.evalSmallValue regs v) ≡ S.evalSmallValue (embed regs) (embed v)
embed-eval regs (reg ♯r) = embed-lookup ♯r regs
embed-eval regs (globval l) = refl
embed-eval regs (int i) = refl
embed-eval regs Λ Δ ∙ v ⟦ is ⟧ = embed-eval regs v

embed-instantiate : ∀ {G w I} →
                      InstantiateGlobal G w I →
                      ∃ λ l →
                        embed w ≡ globval l ×
                        embed G ↓ l ⇒ code (embed I)
embed-instantiate (instantiate-globval l) = _ , refl , embed-↓ l
embed-instantiate (instantiate-Λ ig subs-I)
  with embed-instantiate ig
... | lab , eq , l
  rewrite embed-subst-I-many subs-I
    = _ , eq , l

embed-step : ∀ {G P P'} →
               G H.⊢ P ⇒ P' →
               embed G S.⊢ embed P ⇒ embed P'
embed-step (step-add {regs = regs} {♯rd = ♯rd} {♯rs} {v} {n₁} {n₂} eq₁ eq₂)
  rewrite embed-update ♯rd (int (n₁ + n₂)) regs
        = step-add (trans (sym (embed-eval regs v)) (cong embed eq₁))
                      (trans (sym (embed-lookup ♯rs regs)) (cong embed eq₂))
embed-step (step-sub {regs = regs} {♯rd = ♯rd} {♯rs} {v} {n₁} {n₂} eq₁ eq₂)
  rewrite embed-update ♯rd (int (n₁ ∸ n₂)) regs
        = step-sub (trans (sym (embed-eval regs v)) (cong embed eq₁))
                      (trans (sym (embed-lookup ♯rs regs)) (cong embed eq₂))
embed-step (step-salloc {sp = sp} {n = n})
  rewrite replicate-ns n sp
    = step-salloc
embed-step (step-sfree drop)
  rewrite drop-helper drop
    = step-sfree
embed-step (step-sld {regs = regs} {♯rd = ♯rd} {w = w} l)
  rewrite embed-update ♯rd w regs
    = step-sld (embed-↓ l)
embed-step (step-sst {regs = regs} {♯rs = ♯rs} up)
  with embed-← up
... | up'
  rewrite embed-lookup ♯rs regs
    = step-sst up'
embed-step (step-ld {regs = regs} {♯rd = ♯rd} {♯rs} {w = w} eq l₁ l₂)
  rewrite embed-update ♯rd w regs
  = step-ld (trans (sym (embed-lookup ♯rs regs)) (cong embed eq)) (embed-↓ l₁) (embed-↓ l₂)
embed-step (step-st {regs = regs} {♯rd = ♯rd} {♯rs = ♯rs} eq l up₁ up₂)
  with embed-← up₁
... | up₁'
  rewrite embed-lookup ♯rs regs
  = step-st (trans (sym (embed-lookup ♯rd regs)) (cong embed eq)) (embed-↓ l) up₁' (embed-← up₂)
embed-step (step-malloc {H = H} {regs = regs} {♯rd = ♯rd} {τs = τs})
  rewrite malloc-helper H τs
        | embed-update ♯rd (heapval (length H)) regs
        | sym (embed-length H)
    = step-malloc
embed-step (step-mov {regs = regs} {♯rd = ♯rd} {v = v})
  rewrite embed-update ♯rd (H.evalSmallValue regs v) regs
        | embed-eval regs v
  = step-mov
embed-step (step-beq₀ {regs = regs} {♯r = ♯r} {v = v} eq ig)
  with embed-instantiate ig
... | lab , eq₁ , l
  rewrite embed-eval regs v
  = step-beq₀ (trans (sym (embed-lookup ♯r regs)) (cong embed eq)) eq₁ l
embed-step (step-beq₁ {regs = regs} {♯r = ♯r} eq neq)
  = step-beq₁ (trans (sym (embed-lookup ♯r regs)) (cong embed eq)) neq
embed-step (step-jmp {regs = regs} {v = v} ig)
  with embed-instantiate ig
... | lab , eq₁ , l
  rewrite embed-eval regs v
    = step-jmp eq₁ l

embed-step-prg : ∀ {P P'} →
                   H.⊢ P ⇒ P' →
                   S.⊢ embed P ⇒ embed P'
embed-step-prg (step-running step) = step-running (embed-step step)
embed-step-prg step-halting = step-halting
embed-step-prg step-halted = step-halted
