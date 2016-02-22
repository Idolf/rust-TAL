module Lemmas.Erase where

open import Util
open import Judgments
open import Lemmas.HighSemantics
open import Lemmas.SimpleSemantics

-- The purpose of this module is to prove that
-- the relation {(ℒₕ, erase ℒₕ)} is a simulation.

private
  module S where
    open SimpleGrammar public
    open SimpleSemantics public

  module H where
    open HighGrammar public
    open HighSemantics public

  erase-↓ : ∀ {A B : Set} {{E : Erase A B}}
              {xs : List A} {i x} →
              xs ↓ i ⇒ x →
              map erase xs ↓ i ⇒ erase x
  erase-↓ here = here
  erase-↓ (there l) = there (erase-↓ l)

  erase-← : ∀ {A B : Set} {{E : Erase A B}}
                 {xs xs' : List A} {i x} →
                 xs ⟦ i ⟧← x ⇒ xs' →
                 map erase xs ⟦ i ⟧← erase x ⇒ map erase xs'
  erase-← here = here
  erase-← (there l) = there (erase-← l)

  erase-lookup : ∀ {A B : Set} {{E : Erase A B}}
                {n} i (xs : Vec A n) →
                erase (lookup i xs) ≡ lookup i (Vec-map erase xs)
  erase-lookup zero (x ∷ xs) = refl
  erase-lookup (suc i) (x ∷ xs) = erase-lookup i xs

  erase-update : ∀ {A B : Set} {{E : Erase A B}}
                   {n} i x (xs : Vec A n) →
                   Vec-map erase (update i x xs) ≡ update i (erase x) (Vec-map erase xs)
  erase-update i x xs = map-[]≔ erase xs i

  drop-helper : ∀ {n} {sp sp' : H.Stack} →
                  Drop n sp sp' →
                  erase sp' ≡ drop n (erase sp)
  drop-helper here = refl
  drop-helper (there drop) = drop-helper drop

  replicate-helper : ∀ n → erase {{eraseListWordValue}} (replicate n uninit) ≡ replicate n uninit
  replicate-helper zero = refl
  replicate-helper (suc n) = cong₂ _∷_ refl (replicate-helper n)

  erase-subst-v : ∀ {v v' : H.SmallValue} {θ pos} →
                    v ⟦ θ / pos ⟧≡ v' →
                    erase v ≡ erase v'
  erase-subst-v subst-reg = refl
  erase-subst-v subst-globval = refl
  erase-subst-v subst-int = refl
  erase-subst-v (subst-Λ sub-v subs-I) = erase-subst-v sub-v

  erase-subst-ι : ∀ {ι ι' : H.Instruction} {θ pos} →
                    ι ⟦ θ / pos ⟧≡ ι' →
                    erase ι ≡ erase ι'
  erase-subst-ι {add ♯rd ♯rs v} (subst-add sub-v) = cong (add ♯rd ♯rs) (erase-subst-v sub-v)
  erase-subst-ι {sub ♯rd ♯rs v} (subst-sub sub-v) = cong (sub ♯rd ♯rs) (erase-subst-v sub-v)
  erase-subst-ι subst-salloc = refl
  erase-subst-ι subst-sfree = refl
  erase-subst-ι subst-sld = refl
  erase-subst-ι subst-sst = refl
  erase-subst-ι subst-ld = refl
  erase-subst-ι subst-st = refl
  erase-subst-ι (subst-malloc sub-τs) = cong₂ malloc refl (AllZip-length sub-τs)
  erase-subst-ι (subst-mov sub-v) = cong₂ mov refl (erase-subst-v sub-v)
  erase-subst-ι (subst-beq sub-v) = cong₂ beq refl (erase-subst-v sub-v)

  erase-subst-I : ∀ {I I' : H.InstructionSequence} {θ pos} →
                    I ⟦ θ / pos ⟧≡ I' →
                    erase I ≡ erase I'
  erase-subst-I (subst-~> sub-ι sub-I) = cong₂ _~>_ (erase-subst-ι sub-ι) (erase-subst-I sub-I)
  erase-subst-I (subst-jmp sub-v) = cong jmp (erase-subst-v sub-v)
  erase-subst-I subst-halt = refl

  erase-subst-I-many : ∀ {I I' : H.InstructionSequence} {θs pos} →
                         I ⟦ θs / pos ⟧many≡ I' →
                         erase I ≡ erase I'
  erase-subst-I-many [] = refl
  erase-subst-I-many (sub-I ∷ subs-I)
    rewrite erase-subst-I sub-I
      = erase-subst-I-many subs-I

  erase-eval : ∀ regs v →
                 erase (H.evalSmallValue regs v) ≡ S.evalSmallValue (erase regs) (erase v)
  erase-eval regs (reg ♯r) = erase-lookup ♯r regs
  erase-eval regs (globval lab) = refl
  erase-eval regs (int i) = refl
  erase-eval regs Λ Δ ∙ v ⟦ θs ⟧ = erase-eval regs v

  erase-instantiate : ∀ {G w I} →
                        H.InstantiateGlobal G w I →
                        S.InstantiateGlobal (erase G) (erase w) (erase I)
  erase-instantiate (instantiate-globval l) = instantiate-globval (erase-↓ l)
  erase-instantiate (instantiate-Λ ig subs-I)
    with erase-instantiate ig
  ... | ig'
    rewrite erase-subst-I-many subs-I
      = ig'

  erase-step : ∀ {G Pₘ Pₘ'} →
                 G H.⊢ Pₘ ⇒ Pₘ' →
                 erase G S.⊢ erase Pₘ ⇒ erase Pₘ'
  erase-step (step-add {regs = regs} {♯rd = ♯rd} {♯rs} {v} {n₁} {n₂} eq₁ eq₂)
    rewrite erase-update ♯rd (int (n₁ + n₂)) regs
          = step-add (trans (sym (erase-lookup ♯rs regs)) (cong erase eq₁))
                     (trans (sym (erase-eval regs v)) (cong erase eq₂))
  erase-step (step-sub {regs = regs} {♯rd = ♯rd} {♯rs} {v} {n₁} {n₂} eq₁ eq₂)
    rewrite erase-update ♯rd (int (n₁ ∸ n₂)) regs
          = step-sub (trans (sym (erase-lookup ♯rs regs)) (cong erase eq₁))
                     (trans (sym (erase-eval regs v)) (cong erase eq₂))
  erase-step (step-salloc {sp = sp} {n = n})
    rewrite List-map-++-commute erase (replicate n uninit) sp
          | replicate-helper n
      = step-salloc
  erase-step (step-sfree drop)
    rewrite drop-helper drop
      = step-sfree
  erase-step (step-sld {regs = regs} {♯rd = ♯rd} {w = w} l)
    rewrite erase-update ♯rd w regs
      = step-sld (erase-↓ l)
  erase-step (step-sst {regs = regs} {♯rs = ♯rs} up)
    with erase-← up
  ... | up'
    rewrite erase-lookup ♯rs regs
      = step-sst up'
  erase-step (step-ld {regs = regs} {♯rd = ♯rd} {♯rs} {w = w} eq l₁ l₂)
    rewrite erase-update ♯rd w regs
    = step-ld (trans (sym (erase-lookup ♯rs regs)) (cong erase eq)) (erase-↓ l₁) (erase-↓ l₂)
  erase-step (step-st {regs = regs} {♯rd = ♯rd} {♯rs = ♯rs} eq l up₁ up₂)
    with erase-← up₁
  ... | up₁'
    rewrite erase-lookup ♯rs regs
    = step-st (trans (sym (erase-lookup ♯rd regs)) (cong erase eq)) (erase-↓ l) up₁' (erase-← up₂)
  erase-step (step-malloc {H = H} {regs = regs} {♯rd = ♯rd} {τs = τs})
    rewrite List-map-++-commute erase H [ tuple τs (replicate (length τs) uninit) ]
          | replicate-helper (length τs)
          | erase-update ♯rd (heapval (length H)) regs
          | sym (List-length-map erase H)
      = step-malloc
  erase-step (step-mov {regs = regs} {♯rd = ♯rd} {v = v})
    rewrite erase-update ♯rd (H.evalSmallValue regs v) regs
          | erase-eval regs v
    = step-mov
  erase-step (step-beq₀ {regs = regs} {♯r = ♯r} {v = v} eq ig)
    with erase-instantiate ig
  ... | ig'
    rewrite erase-eval regs v
    = step-beq₀ (trans (sym (erase-lookup ♯r regs)) (cong erase eq)) ig'
  erase-step (step-beq₁ {regs = regs} {♯r = ♯r} eq neq)
    = step-beq₁ (trans (sym (erase-lookup ♯r regs)) (cong erase eq)) neq
  erase-step (step-jmp {regs = regs} {v = v} ig)
    with erase-instantiate ig
  ... | ig'
    rewrite erase-eval regs v
    = step-jmp ig'

erase-step-prg : ∀ {P P'} →
                   H.⊢ P ⇒ P' →
                   S.⊢ erase P ⇒ erase P'
erase-step-prg (step-inner step) = step-inner (erase-step step)

erase-lockstep : ∀ {P₁ P₂ P₂'} →
                   H.⊢ P₁ ⇒ P₂ →
                   S.⊢ erase P₁ ⇒ P₂' →
                   erase P₂ ≡ P₂'
erase-lockstep step step'
  = step-prg-uniqueₛ (erase-step-prg step) step'

erase-step-prg-backwards : ∀ {P Pₛ'} →
                             S.⊢ erase P ⇒ Pₛ' →
                             (∃ λ P' → H.⊢ P ⇒ P' × erase P' ≡ Pₛ') ∨
                             ¬ (H.GoodState P)
erase-step-prg-backwards {G , H , R , I} step
  with step-prg-decₕ (G , H , R , I) | I ≟ halt
... | yes (P' , step') | _
    = inj₁ (P' , step' , step-prg-uniqueₛ (erase-step-prg step') step)
erase-step-prg-backwards {G , H , R , .halt} (step-inner ())
    | _ | yes refl
... | no ¬step' | no I≢halt = inj₂ (help ¬step' I≢halt)
  where help : ∀ {G H R I} →
                 ¬ (∃ λ P' → H.⊢ (G , H , R , I) ⇒ P') →
                 I ≢ halt →
                 ¬ (H.GoodState (G , H , R , I))
        help ¬step I≢halt halting = I≢halt refl
        help ¬step I≢halt (transitioning step) = ¬step (_ , step)
