module Lemmas.HighSemantics where

open import Util
open import Judgments
open import Lemmas.Equality using ()
open import Lemmas.Substitution using (subst-unique-many ; _⟦_/_⟧many?)
open HighGrammar
open HighSemantics

-- The purpose of this file is to prove
-- determinism and decidibibly of evaluation
-- of smallvalue, stepping of instructions
-- and execution of instructions.

private
  int-helper : ∀ {n₁ n₂} {w : WordValue} →
                 w ≡ int n₁ →
                 w ≡ int n₂ →
                 n₁ ≡ n₂
  int-helper refl refl = refl

  heapval-helper : ∀ {labₕ₁ labₕ₂} {w : WordValue} →
                     w ≡ heapval labₕ₁ →
                     w ≡ heapval labₕ₂ →
                     labₕ₁ ≡ labₕ₂
  heapval-helper refl refl = refl

  ↓-unique-heap : ∀ {H : Heap} {labₕ τs₁ τs₂ ws₁ ws₂} →
                    H ↓ labₕ ⇒ tuple τs₁ ws₁ →
                    H ↓ labₕ ⇒ tuple τs₂ ws₂ →
                    ws₁ ≡ ws₂
  ↓-unique-heap l₁ l₂ with ↓-unique l₁ l₂
  ... | refl = refl

  ↓-unique-heap' : ∀ {H : Heap} {labₕ τs₁ τs₂ ws₁ ws₂} →
                     H ↓ labₕ ⇒ tuple τs₁ ws₁ →
                     H ↓ labₕ ⇒ tuple τs₂ ws₂ →
                     τs₁ ≡ τs₂
  ↓-unique-heap' l₁ l₂ with ↓-unique l₁ l₂
  ... | refl = refl

  is-int : ∀ (w : WordValue) → Dec (∃ λ n → w ≡ int n)
  is-int (globval lab) = no (λ { (_ , ()) })
  is-int (heapval labₕ) = no (λ { (_ , ()) })
  is-int (int n) = yes (n , refl)
  is-int uninit = no (λ { (_ , ()) })
  is-int (Λ Δ ∙ w ⟦ θs ⟧) = no (λ { (_ , ()) })

  is-heapval : ∀ (w : WordValue) → Dec (∃ λ labₕ → w ≡ heapval labₕ)
  is-heapval (globval lab) = no (λ { (_ , ()) })
  is-heapval (heapval labₕ) = yes (labₕ , refl)
  is-heapval (int n) = no (λ { (_ , ()) })
  is-heapval uninit = no (λ { (_ , ()) })
  is-heapval (Λ Δ ∙ w ⟦ θs ⟧) = no (λ { (_ , ()) })

instantiate-uniqueₕ : ∀ {G w I₁ I₂} →
                        InstantiateGlobal G w I₁ →
                        InstantiateGlobal G w I₂ →
                        I₁ ≡ I₂
instantiate-uniqueₕ (instantiate-globval l₁) (instantiate-globval l₂)
  with ↓-unique l₁ l₂
instantiate-uniqueₕ (instantiate-globval l₁) (instantiate-globval l₂)
  | refl = refl
instantiate-uniqueₕ (instantiate-Λ ig₁ x) (instantiate-Λ ig₂ x₁)
  with instantiate-uniqueₕ ig₁ ig₂
instantiate-uniqueₕ (instantiate-Λ ig₁ subs-I₁) (instantiate-Λ ig₂ subs-I₂)
  | refl with subst-unique-many subs-I₁ subs-I₂
instantiate-uniqueₕ (instantiate-Λ ig₁ subs-I₁) (instantiate-Λ ig₂ subs-I₂)
  | refl | refl = refl

instantiate-decₕ : ∀ G w → Dec (∃ λ I → InstantiateGlobal G w I)
instantiate-decₕ G (globval lab)
  with ↓-dec G lab
... | no ¬l' = no (λ { (._ , instantiate-globval l) → ¬l' (_ , l) })
... | yes (code[ Δ ] Γ ∙ I , l') = yes (I , instantiate-globval l')
instantiate-decₕ G (heapval lab) = no (λ { (_ , ()) })
instantiate-decₕ G (int n) = no (λ { (_ , ()) })
instantiate-decₕ G uninit = no (λ { (_ , ()) })
instantiate-decₕ G (Λ Δ ∙ w ⟦ θs ⟧)
  with instantiate-decₕ G w
... | no ¬ig = no (λ { (_ , instantiate-Λ ig subs-I) → ¬ig (_ , ig)})
... | yes (I , ig)
  with I ⟦ θs / 0 ⟧many?
... | yes (Iₑ , subs-I) = yes (Iₑ , instantiate-Λ ig subs-I)
... | no ¬subs-I = no help
  where help : ¬ (∃ λ I → InstantiateGlobal G (Λ Δ ∙ w ⟦ θs ⟧) I)
        help (Iₑ , instantiate-Λ {I = I'} ig' subs-I)
          with instantiate-uniqueₕ ig ig'
        help (Iₑ , instantiate-Λ {I = .I} ig' subs-I)
            | refl = ¬subs-I (Iₑ , subs-I)

step-uniqueₕ : ∀ {G P P₁ P₂} →
                 G ⊢ P ⇒ P₁ →
                 G ⊢ P ⇒ P₂ →
                 P₁ ≡ P₂
step-uniqueₕ (step-add eq₁₁ eq₁₂) (step-add eq₂₁ eq₂₂)
  rewrite int-helper eq₁₁ eq₂₁
        | int-helper eq₁₂ eq₂₂
  = refl
step-uniqueₕ (step-sub eq₁₁ eq₁₂) (step-sub eq₂₁ eq₂₂)
  rewrite int-helper eq₁₁ eq₂₁
        | int-helper eq₁₂ eq₂₂
  = refl
step-uniqueₕ step-salloc step-salloc = refl
step-uniqueₕ (step-sfree drop₁) (step-sfree drop₂)
  rewrite drop-unique drop₁ drop₂ = refl
step-uniqueₕ (step-sld l₁) (step-sld l₂)
  rewrite ↓-unique l₁ l₂ = refl
step-uniqueₕ (step-sst up₁) (step-sst up₂)
  rewrite ←-unique up₁ up₂ = refl
step-uniqueₕ (step-ld eq₁ l₁₁ l₁₂) (step-ld eq₂ l₂₁ l₂₂)
  rewrite heapval-helper eq₁ eq₂
        | ↓-unique-heap l₁₁ l₂₁
        | ↓-unique l₁₂ l₂₂
  = refl
step-uniqueₕ (step-st eq₁ l₁ up₁₁ up₁₂) (step-st eq₂ l₂ up₂₁ up₂₂)
  rewrite heapval-helper eq₁ eq₂
        | ↓-unique-heap l₁ l₂
        | ↓-unique-heap' l₁ l₂
        | ←-unique up₁₁ up₂₁
        | ←-unique up₁₂ up₂₂
  = refl
step-uniqueₕ step-malloc step-malloc = refl
step-uniqueₕ step-mov step-mov = refl
step-uniqueₕ (step-beq₀ eq₁ ig₁) (step-beq₀ eq₂ ig₂)
  with instantiate-uniqueₕ ig₁ ig₂
... | refl = refl
step-uniqueₕ (step-beq₀ eq₁ ig₁) (step-beq₁ eq₂ neq₂)
  rewrite int-helper eq₁ eq₂
  with neq₂ refl
... | ()
step-uniqueₕ (step-beq₁ eq₁ neq₁) (step-beq₀ eq₂ ig₂)
  rewrite int-helper eq₁ eq₂
  with neq₁ refl
... | ()
step-uniqueₕ (step-beq₁ eq₁ neq₁) (step-beq₁ eq₂ neq₂) = refl
step-uniqueₕ (step-jmp ig₁) (step-jmp ig₂)
  with instantiate-uniqueₕ ig₁ ig₂
... | refl = refl

step-decₕ : ∀ G P → Dec (∃ λ P' → G ⊢ P ⇒ P')
step-decₕ G (H , register sp regs , add ♯rd ♯rs v ~> I)
  with is-int (lookup ♯rs regs) | is-int (evalSmallValue regs v)
... | yes (n₁ , eq₁) | yes (n₂ , eq₂) = yes (_ , step-add eq₁ eq₂)
... | no ¬eq₁ | _ = no (λ { (._ , step-add eq₁ eq₂) → ¬eq₁ (_ , eq₁)})
... | _ | no ¬eq₂ = no (λ { (._ , step-add eq₁ eq₂) → ¬eq₂ (_ , eq₂)})
step-decₕ G (H , register sp regs , sub ♯rd ♯rs v ~> I)
  with is-int (lookup ♯rs regs) | is-int (evalSmallValue regs v)
... | yes (n₁ , eq₁) | yes (n₂ , eq₂) = yes (_ , step-sub eq₁ eq₂)
... | no ¬eq₁ | _ = no (λ { (._ , step-sub eq₁ eq₂) → ¬eq₁ (_ , eq₁)})
... | _ | no ¬eq₂ = no (λ { (._ , step-sub eq₁ eq₂) → ¬eq₂ (_ , eq₂)})
step-decₕ G (H , register sp regs , salloc n ~> I)
  = yes (_ , step-salloc)
step-decₕ G (H , register sp regs , sfree n ~> I)
  with drop-dec n sp
... | yes (sp' , drop) = yes (_ , step-sfree drop)
... | no ¬drop = no (λ { (._ , step-sfree drop) → ¬drop (_ , drop)})
step-decₕ G (H , register sp regs , sld ♯rd i ~> I)
  with ↓-dec sp i
... | yes (w , l) = yes (_ , step-sld l)
... | no ¬l = no (λ { (._ , step-sld l) → ¬l (_ , l)})
step-decₕ G (H , register sp regs , sst i ♯rs ~> I)
  with ←-dec sp i (lookup ♯rs regs)
... | yes (sp' , up) = yes (_ , step-sst up)
... | no ¬up = no (λ { (._ , step-sst up) → ¬up (_ , up)})
step-decₕ G (H , register sp regs , ld ♯rd ♯rs i ~> I)
  with is-heapval (lookup ♯rs regs)
... | no ¬eq = no (λ { (_ , step-ld eq l₁ l₂) → ¬eq (_ , eq)})
... | yes (lₕ , eq) with ↓-dec H lₕ
... | no ¬l₁ = no help
  where help : ¬ (∃ λ P' → G ⊢ H , register sp regs , ld ♯rd ♯rs i ~> I ⇒ P')
        help (._ , step-ld eq' l₁ l₂) with heapval-helper eq eq'
        ... | refl = ¬l₁ (_ , l₁)
... | yes (tuple τs ws , l₁) with ↓-dec ws i
... | no ¬l₂ = no help
  where help : ¬ (∃ λ P' → G ⊢ H , register sp regs , ld ♯rd ♯rs i ~> I ⇒ P')
        help (._ , step-ld eq' l₁' l₂) with heapval-helper eq eq'
        ... | refl with ↓-unique-heap l₁ l₁'
        ... | refl = ¬l₂ (_ , l₂)
... | yes (w , l₂) = yes (_ , step-ld eq l₁ l₂)
step-decₕ G (H , register sp regs , st ♯rd i ♯rs ~> I)
  with is-heapval (lookup ♯rd regs)
... | no ¬eq = no (λ { (_ , step-st eq l up₁ up₂) → ¬eq (_ , eq)})
... | yes (lₕ , eq) with ↓-dec H lₕ
... | no ¬l = no help
  where help : ¬ (∃ λ P' → G ⊢ H , register sp regs , st ♯rd i ♯rs ~> I ⇒ P')
        help (._ , step-st eq' l up₁ up₂) with heapval-helper eq eq'
        ... | refl = ¬l (_ , l)
... | yes (tuple τs ws , l) with ←-dec ws i (lookup ♯rs regs)
... | no ¬up₁ = no help
  where help : ¬ (∃ λ P' → G ⊢ H , register sp regs , st ♯rd i ♯rs ~> I ⇒ P')
        help (._ , step-st eq' l' up₁ up₂) with heapval-helper eq eq'
        ... | refl with ↓-unique-heap l l'
        ... | refl = ¬up₁ (_ , up₁)
... | yes (ws' , up₁) with ←-dec H lₕ (tuple τs ws')
... | no ¬up₂ = no help
  where help : ¬ (∃ λ P' → G ⊢ H , register sp regs , st ♯rd i ♯rs ~> I ⇒ P')
        help (._ , step-st eq' l' up₁' up₂) with heapval-helper eq eq'
        ... | refl with ↓-unique-heap l l'
        ... | refl with ↓-unique-heap' l l'
        ... | refl with ←-unique up₁ up₁'
        ... | refl = ¬up₂ (_ , up₂)
... | yes (H' , up₂) = yes (_ , step-st eq l up₁ up₂)
step-decₕ G (H , register sp regs , malloc ♯rd τs ~> I)
  = yes (_ , step-malloc)
step-decₕ G (H , register sp regs , mov ♯rd v ~> I)
  = yes (_ , step-mov)
step-decₕ G (H , register sp regs , beq ♯r v ~> I)
  with is-int (lookup ♯r regs)
... | no ¬eq = no (λ { (._ , step-beq₀ eq ig) → ¬eq (_ , eq)
                     ; (._ , step-beq₁ eq neg) → ¬eq (_ , eq)})
... | yes (suc n , eq) = yes (_ , step-beq₁ eq (λ ()))
... | yes (zero , eq) with instantiate-decₕ G (evalSmallValue regs v)
... | no ¬ig = no (λ { (._ , step-beq₀ eq' ig) → ¬ig (_ , ig)
                       ; (._ , step-beq₁ eq' neq) →
                             neq (int-helper eq' eq)})
... | yes (I' , ig) = yes (_ , step-beq₀ eq ig)
step-decₕ G (H , register sp regs , jmp v)
  with instantiate-decₕ G (evalSmallValue regs v)
... | no ¬ig = no (λ { (._ , step-jmp ig) → ¬ig (_ , ig) })
... | yes (I' , ig) = yes (_ , step-jmp ig)
step-decₕ G (H , R , halt) = no (λ { (_ , ()) })

step-prg-uniqueₕ : ∀ {ℒ ℒ₁ ℒ₂} →
                    ⊢ ℒ ⇒ ℒ₁ →
                    ⊢ ℒ ⇒ ℒ₂ →
                    ℒ₁ ≡ ℒ₂
step-prg-uniqueₕ (step-running step₁) (step-running step₂)
  rewrite step-uniqueₕ step₁ step₂
    = refl
step-prg-uniqueₕ (step-running ()) step-halting
step-prg-uniqueₕ step-halting (step-running ())
step-prg-uniqueₕ step-halting step-halting = refl
step-prg-uniqueₕ step-halted step-halted = refl

step-prg-decₕ : ∀ ℒ → Dec (∃ λ ℒ' → ⊢ ℒ ⇒ ℒ')
step-prg-decₕ (running G (H , R , I))
  with I ≟ halt | step-decₕ G (H , R , I)
step-prg-decₕ (running G (H , R , .halt))
    | yes refl | _ = yes (halted , step-halting)
... | _ | yes (P' , step) = yes (running G P' , step-running step)
... | no I≢halt | no ¬step = no (help I≢halt ¬step)
  where help : ∀ {G H R I} →
                 I ≢ halt →
                 ¬ ∃ (λ P' → (G ⊢ (H , R , I) ⇒ P')) →
                 ¬ ∃ (λ ℒ' → (⊢ running G (H , R , I) ⇒ ℒ'))
        help I≢halt ¬step (_ , step-running step) = ¬step (_ , step)
        help I≢halt ¬step (_ , step-halting) = I≢halt refl
step-prg-decₕ halted = yes (halted , step-halted)

step-prg-dec-specificₕ : ∀ ℒ ℒ' → Dec (⊢ ℒ ⇒ ℒ')
step-prg-dec-specificₕ ℒ ℒ'
  with step-prg-decₕ ℒ
... | no ¬step = no (λ step → ¬step (ℒ' , step))
... | yes (ℒ'' , step)
  with ℒ' ≟ ℒ''
... | no ¬eq = no (λ step' → ¬eq (step-prg-uniqueₕ step' step))
step-prg-dec-specificₕ ℒ ℒ'
    | yes (.ℒ' , step) | yes refl = yes step

exec-uniqueₕ : ∀ {ℒ ℒ₁ ℒ₂ n} →
                 ⊢ ℒ ⇒ₙ n / ℒ₁ →
                 ⊢ ℒ ⇒ₙ n / ℒ₂ →
                 ℒ₁ ≡ ℒ₂
exec-uniqueₕ [] [] = refl
exec-uniqueₕ (step₁ ∷ exec₁) (step₂ ∷ exec₂)
  rewrite step-prg-uniqueₕ step₁ step₂
        | exec-uniqueₕ exec₁ exec₂ = refl

exec-decₕ : ∀ ℒ n → Dec (∃ λ ℒ' → ⊢ ℒ ⇒ₙ n / ℒ')
exec-decₕ ℒ zero = yes (ℒ , [])
exec-decₕ ℒ (suc n) with step-prg-decₕ ℒ
... | no ¬step = no (λ { (ℒ'' , step ∷ exec) → ¬step (_ , step)})
... | yes (ℒ' , step) with exec-decₕ ℒ' n
... | no ¬exec = no (λ
  { (ℒ'' , step' ∷ exec) → ¬exec (ℒ'' ,
    subst (λ ℒ → ⊢ ℒ ⇒ₙ n / ℒ'') (step-prg-uniqueₕ step' step) exec
  )})
... | yes (ℒ'' , exec) = yes (ℒ'' , step ∷ exec)

¬Stuck→stepₕ : ∀  {ℒ} → ¬ Stuck ℒ →
               ∃ λ ℒ' → ⊢ ℒ ⇒ ℒ' × ¬ Stuck ℒ'
¬Stuck→stepₕ {ℒ} ¬stuck
  with step-prg-decₕ ℒ
... | yes (ℒ' , step) = ℒ' , step , (λ stuck → ¬stuck (there step stuck))
... | no ¬step
  with ¬stuck (here ¬step)
... | ()
