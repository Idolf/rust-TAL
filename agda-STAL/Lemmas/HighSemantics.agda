module Lemmas.HighSemantics where

open import Util
open import Judgments
open import Lemmas.Equality
open import Lemmas.Substitution
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

  heapval-helper : ∀ {lₕ₁ lₕ₂} {w : WordValue} →
                   w ≡ heapval lₕ₁ →
                   w ≡ heapval lₕ₂ →
                   lₕ₁ ≡ lₕ₂
  heapval-helper refl refl = refl

  ↓-unique-heap : ∀ {H : Heap} {lₕ ws₁ ws₂} →
                    H ↓ lₕ ⇒ tuple ws₁ →
                    H ↓ lₕ ⇒ tuple ws₂ →
                    ws₁ ≡ ws₂
  ↓-unique-heap l₁ l₂ with ↓-unique l₁ l₂
  ... | refl = refl

eval-unique : ∀ {G w I₁ I₂} →
                InstantiateGlobal G w I₁ →
                InstantiateGlobal G w I₂ →
                I₁ ≡ I₂
eval-unique (instantiate-globval l₁) (instantiate-globval l₂)
  with ↓-unique l₁ l₂
eval-unique (instantiate-globval l₁) (instantiate-globval l₂)
  | refl = refl
eval-unique (instantiate-Λ eval₁ x) (instantiate-Λ eval₂ x₁)
  with eval-unique eval₁ eval₂
eval-unique (instantiate-Λ eval₁ subs-I₁) (instantiate-Λ eval₂ subs-I₂)
  | refl with subst-unique-many subs-I₁ subs-I₂
eval-unique (instantiate-Λ eval₁ subs-I₁) (instantiate-Λ eval₂ subs-I₂)
  | refl | refl = refl

step-uniqueₕ : ∀ {G P P₁ P₂} →
                G ⊢ P ⇒ P₁ →
                G ⊢ P ⇒ P₂ →
                P₁ ≡ P₂
step-uniqueₕ (step-add eq₁₁ eq₁₂) (step-add eq₂₁ eq₂₂)
  rewrite int-helper eq₁₁ eq₂₁
        | int-helper eq₁₂ eq₂₂ = refl
step-uniqueₕ (step-sub eq₁₁ eq₁₂) (step-sub eq₂₁ eq₂₂)
  rewrite int-helper eq₁₁ eq₂₁
        | int-helper eq₁₂ eq₂₂ = refl
step-uniqueₕ step-salloc step-salloc = refl
step-uniqueₕ (step-sfree drop₁) (step-sfree drop₂)
  rewrite drop-unique drop₁ drop₂ = refl
step-uniqueₕ (step-sld l₁) (step-sld l₂)
  rewrite ↓-unique l₁ l₂ = refl
step-uniqueₕ (step-sst u₁) (step-sst u₂)
  rewrite ←-unique u₁ u₂ = refl
step-uniqueₕ (step-ld eq₁ l₁₁ l₁₂) (step-ld eq₂ l₂₁ l₂₂)
  rewrite heapval-helper eq₁ eq₂
        | ↓-unique-heap l₁₁ l₂₁
        | ↓-unique l₁₂ l₂₂ = refl
step-uniqueₕ (step-st eq₁ l₁ u₁₁ u₁₂) (step-st eq₂ l₂ u₂₁ u₂₂)
  rewrite heapval-helper eq₁ eq₂
        | ↓-unique-heap l₁ l₂
        | ←-unique u₁₁ u₂₁
        | ←-unique u₁₂ u₂₂
  = refl
step-uniqueₕ step-mov step-mov = refl
step-uniqueₕ step-malloc step-malloc = refl
step-uniqueₕ (step-beq₀ eq₁ eval₁) (step-beq₀ eq₂ eval₂)
  with eval-unique eval₁ eval₂
... | refl = refl
step-uniqueₕ (step-beq₀ eq₁ eval₁) (step-beq₁ eq₂ neq₂)
  rewrite int-helper eq₁ eq₂ with neq₂ refl
... | ()
step-uniqueₕ (step-beq₁ eq₁ neq₁) (step-beq₀ eq₂ eval₂)
  rewrite int-helper eq₁ eq₂ with neq₁ refl
... | ()
step-uniqueₕ (step-beq₁ eq₁ neq₁) (step-beq₁ eq₂ neq₂) = refl
step-uniqueₕ (step-jmp eval₁) (step-jmp eval₂)
  with eval-unique eval₁ eval₂
... | refl = refl

step-prg-uniqueₕ : ∀ {P P₁ P₂} →
                    ⊢ P ⇒ P₁ →
                    ⊢ P ⇒ P₂ →
                    P₁ ≡ P₂
step-prg-uniqueₕ (step-going step₁) (step-going step₂)
  rewrite step-uniqueₕ step₁ step₂
    = refl
step-prg-uniqueₕ (step-going ()) step-halting
step-prg-uniqueₕ step-halting (step-going ())
step-prg-uniqueₕ step-halting step-halting = refl
step-prg-uniqueₕ step-halted step-halted = refl

exec-uniqueₕ : ∀ {P P₁ P₂ n} →
                 ⊢ P ⇒ₙ n / P₁ →
                 ⊢ P ⇒ₙ n / P₂ →
                 P₁ ≡ P₂
exec-uniqueₕ [] [] = refl
exec-uniqueₕ (step₁ ∷ exec₁) (step₂ ∷ exec₂)
  rewrite step-prg-uniqueₕ step₁ step₂
        | exec-uniqueₕ exec₁ exec₂ = refl

instantiate-dec : ∀ G w → Dec (∃ λ I → InstantiateGlobal G w I)
instantiate-dec G (globval l)
  with ↓-dec G l
... | no ¬l' = no (λ { (._ , instantiate-globval l) → ¬l' (_ , l) })
... | yes (code[ Δ ] Γ ∙ I , l') = yes (I , instantiate-globval l')
instantiate-dec G (heapval l) = no (λ { (_ , ()) })
instantiate-dec G (int n) = no (λ { (_ , ()) })
instantiate-dec G ns = no (λ { (_ , ()) })
instantiate-dec G (uninit τ) = no (λ { (_ , ()) })
instantiate-dec G (Λ Δ ∙ w ⟦ is ⟧)
  with instantiate-dec G w
... | no ¬eval = no (λ { (_ , instantiate-Λ eval subs-I) → ¬eval (_ , eval)})
... | yes (I , eval)
  with I ⟦ is / 0 ⟧many?
... | yes (Iₑ , subs-I) = yes (Iₑ , instantiate-Λ eval subs-I)
... | no ¬subs-I = no help
  where help : ¬ (∃ λ I → InstantiateGlobal G (Λ Δ ∙ w ⟦ is ⟧) I)
        help (Iₑ , instantiate-Λ {I = I'} eval' subs-I)
          with eval-unique eval eval'
        help (Iₑ , instantiate-Λ {I = .I} eval' subs-I)
            | refl = ¬subs-I (Iₑ , subs-I)

private
  is-int : ∀ (w : WordValue) → Dec (∃ λ n → w ≡ int n)
  is-int (globval l) = no (λ { (_ , ()) })
  is-int (heapval lₕ) = no (λ { (_ , ()) })
  is-int (int n) = yes (n , refl)
  is-int ns = no (λ { (_ , ()) })
  is-int (uninit τs) = no (λ { (_ , ()) })
  is-int (Λ Δ ∙ w ⟦ is ⟧) = no (λ { (_ , ()) })

  ↓-is-int : ∀ regs ♯r → Dec (∃ λ n → regs ↓ ♯r ⇒ int n)
  ↓-is-int regs ♯r with ↓-dec regs ♯r
  ... | no ¬l = no (λ { (n , l) → ¬l (_ , l)})
  ... | yes (v , l) with is-int v
  ... | yes (n , eq) rewrite eq = yes (n , l)
  ... | no ¬eq = no (λ { (n , l') → ¬eq (n , ↓-unique l l')})

  is-heapval : ∀ (w : WordValue) → Dec (∃ λ lₕ → w ≡ heapval lₕ)
  is-heapval (globval l) = no (λ { (_ , ()) })
  is-heapval (heapval lₕ) = yes (lₕ , refl)
  is-heapval (int n) = no (λ { (_ , ()) })
  is-heapval ns = no (λ { (_ , ()) })
  is-heapval (uninit τs) = no (λ { (_ , ()) })
  is-heapval (Λ Δ ∙ w ⟦ is ⟧) = no (λ { (_ , ()) })

  ↓-is-heapval : ∀ regs ♯r → Dec (∃ λ lₕ → regs ↓ ♯r ⇒ heapval lₕ)
  ↓-is-heapval regs ♯r with ↓-dec regs ♯r
  ... | no ¬l = no (λ { (lₕ , l) → ¬l (_ , l)})
  ... | yes (v , l) with is-heapval v
  ... | yes (lₕ , eq) rewrite eq = yes (lₕ , l)
  ... | no ¬eq = no (λ { (lₕ , l') → ¬eq (lₕ , ↓-unique l l')})

step-decₕ : ∀ G P → Dec (∃ λ P' → G ⊢ P ⇒ P')
step-decₕ G (H , register sp regs , add ♯rd ♯rs v ~> I)
  with is-int (evalSmallValue regs v) | is-int (lookup ♯rs regs)
... | yes (n₁ , eq₁) | yes (n₂ , eq₂) = yes (_ , step-add eq₁ eq₂)
... | no ¬eq₁ | _ = no (λ { (._ , step-add eq₁ eq₂) → ¬eq₁ (_ , eq₁)})
... | _ | no ¬eq₂ = no (λ { (._ , step-add eq₁ eq₂) → ¬eq₂ (_ , eq₂)})
step-decₕ G (H , register sp regs , sub ♯rd ♯rs v ~> I)
  with is-int (evalSmallValue regs v) | is-int (lookup ♯rs regs)
... | yes (n₁ , eq₁) | yes (n₂ , eq₂) = yes (_ , step-sub eq₁ eq₂)
... | no ¬eq₁ | _ = no (λ { (._ , step-sub eq₁ eq₂) → ¬eq₁ (_ , eq₁)})
... | _ | no ¬eq₂ = no (λ { (._ , step-sub eq₁ eq₂) → ¬eq₂ (_ , eq₂)})
step-decₕ G (H , register sp regs , salloc n ~> I) = yes (_ , step-salloc)
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
... | yes (tuple ws , l₁) with ↓-dec ws i
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
... | yes (tuple ws , l) with ←-dec ws i (lookup ♯rs regs)
... | no ¬up₁ = no help
  where help : ¬ (∃ λ P' → G ⊢ H , register sp regs , st ♯rd i ♯rs ~> I ⇒ P')
        help (._ , step-st eq' l' up₁ up₂) with heapval-helper eq eq'
        ... | refl with ↓-unique-heap l l'
        ... | refl = ¬up₁ (_ , up₁)
... | yes (ws' , up₁) with ←-dec H lₕ (tuple ws')
... | no ¬up₂ = no help
  where help : ¬ (∃ λ P' → G ⊢ H , register sp regs , st ♯rd i ♯rs ~> I ⇒ P')
        help (._ , step-st eq' l' up₁' up₂) with heapval-helper eq eq'
        ... | refl with ↓-unique-heap l l'
        ... | refl with ←-unique up₁ up₁'
        ... | refl = ¬up₂ (_ , up₂)
... | yes (H' , up₂) = yes (_ , step-st eq l up₁ up₂)
step-decₕ G (H , register sp regs , malloc ♯rd τs ~> I) = yes (_ , step-malloc)
step-decₕ G (H , register sp regs , mov ♯rd v ~> I) = yes (_ , step-mov)
step-decₕ G (H , register sp regs , beq ♯r v ~> I)
  with is-int (lookup ♯r regs)
... | no ¬eq = no (λ { (._ , step-beq₀ eq eval) → ¬eq (_ , eq)
                     ; (._ , step-beq₁ eq neg) → ¬eq (_ , eq)})
... | yes (suc n , eq) = yes (_ , step-beq₁ eq (λ ()))
... | yes (zero , eq) with instantiate-dec G (evalSmallValue regs v)
... | no ¬eval = no (λ { (._ , step-beq₀ eq' eval) → ¬eval (_ , eval)
                       ; (._ , step-beq₁ eq' neq) →
                             neq (int-helper eq' eq)})
... | yes (I' , eval) = yes (_ , step-beq₀ eq eval)
step-decₕ G (H , register sp regs , jmp v)
  with instantiate-dec G (evalSmallValue regs v)
... | no ¬eval = no (λ { (._ , step-jmp eval) → ¬eval (_ , eval) })
... | yes (I' , eval) = yes (_ , step-jmp eval)
step-decₕ G (H , R , halt) = no (λ { (_ , ()) })

step-prg-decₕ : ∀ P → Dec (∃ λ P' → ⊢ P ⇒ P')
step-prg-decₕ (going G (H , R , I))
  with I ≟ halt | step-decₕ G (H , R , I)
step-prg-decₕ (going G (H , R , .halt))
    | yes refl | _ = yes (halted , step-halting)
... | _ | yes (P' , step) = yes (going G P' , step-going step)
... | no I≢halt | no ¬step = no (help I≢halt ¬step)
  where help : ∀ {G H R I} →
                 I ≢ halt →
                 ¬ ∃ (λ P' → (G ⊢ (H , R , I) ⇒ P')) →
                 ¬ ∃ (λ P' → (⊢ going G (H , R , I) ⇒ P'))
        help I≢halt ¬step (_ , step-going step) = ¬step (_ , step)
        help I≢halt ¬step (_ , step-halting) = I≢halt refl
step-prg-decₕ halted = yes (halted , step-halted)

exec-decₕ : ∀ P n → Dec (∃ λ P' → ⊢ P ⇒ₙ n / P')
exec-decₕ P zero = yes (P , [])
exec-decₕ P (suc n) with step-prg-decₕ P
... | no ¬step = no (λ { (P'' , step ∷ exec) → ¬step (_ , step)})
... | yes (P' , step) with exec-decₕ P' n
... | no ¬exec = no (λ
  { (P'' , step' ∷ exec) → ¬exec (P'' ,
    subst (λ P → ⊢ P ⇒ₙ n / P'') (step-prg-uniqueₕ step' step) exec
  )})
... | yes (P'' , exec) = yes (P'' , step ∷ exec)
