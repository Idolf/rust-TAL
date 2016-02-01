module Simple.SemanticsLemmas where

open import Util
open import Simple.Grammar
open import Simple.Semantics
open import Simple.Equality

private
  int-helper : ∀ {n₁ n₂} {w : WordValue} →
                 w ≡ int n₁ →
                 w ≡ int n₂ →
                 n₁ ≡ n₂
  int-helper refl refl = refl

  heapval-helper : ∀ {lₕ₁ lₕ₂ w} →
                     w ≡ heapval lₕ₁ →
                     w ≡ heapval lₕ₂ →
                     lₕ₁ ≡ lₕ₂
  heapval-helper refl refl = refl

  globval-helper : ∀ {l₁ l₂} {w : WordValue} →
                     w ≡ globval l₁ →
                     w ≡ globval l₂ →
                     l₁ ≡ l₂
  globval-helper refl refl = refl

  ↓-unique-heap : ∀ {H : Heap} {lₕ ws₁ ws₂} →
                    H ↓ lₕ ⇒ tuple ws₁ →
                    H ↓ lₕ ⇒ tuple ws₂ →
                    ws₁ ≡ ws₂
  ↓-unique-heap l₁ l₂ with ↓-unique l₁ l₂
  ... | refl = refl

  ↓-unique-globals : ∀ {G : Globals} {l I₁ I₂} →
                       G ↓ l ⇒ code I₁ →
                       G ↓ l ⇒ code I₂ →
                       I₁ ≡ I₂
  ↓-unique-globals l₁ l₂ with ↓-unique l₁ l₂
  ... | refl = refl

step-unique : ∀ {G P P₁ P₂} →
                G ⊢ P ⇒ P₁ →
                G ⊢ P ⇒ P₂ →
                P₁ ≡ P₂
step-unique (step-add eq₁₁ eq₁₂) (step-add eq₂₁ eq₂₂)
  rewrite int-helper eq₁₁ eq₂₁
        | int-helper eq₁₂ eq₂₂
        = refl
step-unique (step-sub eq₁₁ eq₁₂) (step-sub eq₂₁ eq₂₂)
  rewrite int-helper eq₁₁ eq₂₁
        | int-helper eq₁₂ eq₂₂
        = refl
step-unique step-salloc step-salloc = refl
step-unique step-sfree step-sfree = refl
step-unique (step-sld l₁) (step-sld l₂)
  rewrite ↓-unique l₁ l₂ = refl
step-unique (step-sst up₁) (step-sst up₂)
  rewrite ←-unique up₁ up₂ = refl
step-unique (step-ld eq₁ l₁₁ l₁₂) (step-ld eq₂ l₂₁ l₂₂)
  rewrite heapval-helper eq₁ eq₂
        | ↓-unique-heap l₁₁ l₂₁
        | ↓-unique l₁₂ l₂₂
        = refl
step-unique (step-st eq₁ l₁ up₁₁ up₁₂) (step-st eq₂ l₂ up₂₁ up₂₂)
  rewrite heapval-helper eq₁ eq₂
        | ↓-unique-heap l₁ l₂
        | ←-unique up₁₁ up₂₁
        | ←-unique up₁₂ up₂₂
        = refl
step-unique step-malloc step-malloc = refl
step-unique step-mov step-mov = refl
step-unique (step-beq₀ eq₁₁ eq₁₂ l₁) (step-beq₀ eq₂₁ eq₂₂ l₂)
  rewrite globval-helper eq₁₂ eq₂₂
        | ↓-unique-globals l₁ l₂
        = refl
step-unique (step-beq₀ eq₁₁ eq₁₂ l₁) (step-beq₁ eq₂ neq₂)
  rewrite int-helper eq₁₁ eq₂
  with neq₂ refl
... | ()
step-unique (step-beq₁ eq₁ neq₁) (step-beq₀ eq₂₁ eq₂₂ l₂)
  rewrite int-helper eq₁ eq₂₁
  with neq₁ refl
... | ()
step-unique (step-beq₁ eq₁ neq₁) (step-beq₁ eq₂ neq₂) = refl
step-unique (step-jmp eq₁ l₁) (step-jmp eq₂ l₂)
  rewrite globval-helper eq₁ eq₂
        | ↓-unique-globals l₁ l₂
        = refl

step-prg-unique : ∀ {P P₁ P₂} →
                    ⊢ P ⇒ P₁ →
                    ⊢ P ⇒ P₂ →
                    P₁ ≡ P₂
step-prg-unique (step-going step₁) (step-going step₂)
  rewrite step-unique step₁ step₂
    = refl
step-prg-unique (step-going ()) step-halting
step-prg-unique step-halting (step-going ())
step-prg-unique step-halting step-halting = refl
step-prg-unique step-halted step-halted = refl

exec-unique : ∀ {P P₁ P₂ n} →
                 ⊢ P ⇒ₙ n / P₁ →
                 ⊢ P ⇒ₙ n / P₂ →
                 P₁ ≡ P₂
exec-unique [] [] = refl
exec-unique (step₁ ∷ exec₁) (step₂ ∷ exec₂)
  rewrite step-prg-unique step₁ step₂
        | exec-unique exec₁ exec₂ = refl

private
  is-int : ∀ (w : WordValue) → Dec (∃ λ n → w ≡ int n)
  is-int (globval l) = no (λ { (_ , ()) })
  is-int (heapval lₕ) = no (λ { (_ , ()) })
  is-int (int n) = yes (n , refl)
  is-int ns = no (λ { (_ , ()) })
  is-int uninit = no (λ { (_ , ()) })

  is-heapval : ∀ (w : WordValue) → Dec (∃ λ lₕ → w ≡ heapval lₕ)
  is-heapval (globval l) = no (λ { (_ , ()) })
  is-heapval (heapval lₕ) = yes (lₕ , refl)
  is-heapval (int n) = no (λ { (_ , ()) })
  is-heapval ns = no (λ { (_ , ()) })
  is-heapval uninit = no (λ { (_ , ()) })

  is-globval : ∀ (w : WordValue) → Dec (∃ λ lₕ → w ≡ globval lₕ)
  is-globval (globval l) = yes (l , refl)
  is-globval (heapval lₕ) = no (λ { (_ , ()) })
  is-globval (int n) = no (λ { (_ , ()) })
  is-globval ns = no (λ { (_ , ()) })
  is-globval uninit = no (λ { (_ , ()) })

step-dec : ∀ G P → Dec (∃ λ P' → G ⊢ P ⇒ P')
step-dec G (H , register sp regs , add ♯rd ♯rs v ~> I)
  with is-int (evalSmallValue regs v) | is-int (lookup ♯rs regs)
... | yes (n₁ , eq₁) | yes (n₂ , eq₂) = yes (_ , step-add eq₁ eq₂)
... | no ¬eq₁ | _ = no (λ { (._ , step-add eq₁ eq₂) → ¬eq₁ (_ , eq₁)})
... | _ | no ¬eq₂ = no (λ { (._ , step-add eq₁ eq₂) → ¬eq₂ (_ , eq₂)})
step-dec G (H , register sp regs , sub ♯rd ♯rs v ~> I)
  with is-int (evalSmallValue regs v) | is-int (lookup ♯rs regs)
... | yes (n₁ , eq₁) | yes (n₂ , eq₂) = yes (_ , step-sub eq₁ eq₂)
... | no ¬eq₁ | _ = no (λ { (._ , step-sub eq₁ eq₂) → ¬eq₁ (_ , eq₁)})
... | _ | no ¬eq₂ = no (λ { (._ , step-sub eq₁ eq₂) → ¬eq₂ (_ , eq₂)})
step-dec G (H , register sp regs , salloc n ~> I)
  = yes (_ , step-salloc)
step-dec G (H , register sp regs , sfree n ~> I)
  = yes (_ , step-sfree)
step-dec G (H , register sp regs , sld ♯rd i ~> I)
  with ↓-dec sp i
... | yes (w , l) = yes (_ , step-sld l)
... | no ¬l = no (λ { (._ , step-sld l) → ¬l (_ , l)})
step-dec G (H , register sp regs , sst i ♯rs ~> I)
  with ←-dec sp i (lookup ♯rs regs)
... | yes (sp' , up) = yes (_ , step-sst up)
... | no ¬up = no (λ { (._ , step-sst up) → ¬up (_ , up)})
step-dec G (H , register sp regs , ld ♯rd ♯rs i ~> I)
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
step-dec G (H , register sp regs , st ♯rd i ♯rs ~> I)
  with is-heapval (lookup ♯rd regs)
... | no ¬eq = no (λ { (_ , step-st eq l up₁ up₂)  → ¬eq (_ , eq)})
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
step-dec G (H , register sp regs , malloc ♯rd n ~> I)
  = yes (_ , step-malloc)
step-dec G (H , register sp regs , mov ♯rd v ~> I)
  = yes (_ , step-mov)
step-dec G (H , register sp regs , beq ♯r v ~> I)
  with is-int (lookup ♯r regs)
... | no ¬eq = no (λ { (_ , step-beq₀ eq₁ eq₂ l) → ¬eq (_ , eq₁) ; (_ , step-beq₁ eq neq) → ¬eq (_ , eq) })
... | yes (suc n , eq) = yes (_ , step-beq₁ eq (λ ()))
... | yes (zero , eq₁)
  with is-globval (evalSmallValue regs v)
... | no ¬eq = no (λ { (_ , step-beq₀ eq₁ eq₂ l) → ¬eq (_ , eq₂) ; (_ , step-beq₁ eq neq) → neq (int-helper eq eq₁) })
... | yes (lab , eq₂)
  with ↓-dec G lab
... | yes (code I₂ , l)
  = yes (_ , step-beq₀ eq₁ eq₂ l)
... | no ¬l = no help
  where help : ¬ (∃ λ P' → G ⊢ H , register sp regs , beq ♯r v ~> I ⇒ P')
        help (._ , step-beq₀ eq₃ eq₄ l)
          with globval-helper eq₂ eq₄
        ... | refl = ¬l (_ , l)
        help (._ , step-beq₁ eq neq) = neq (int-helper eq eq₁)
step-dec G (H , register sp regs , jmp v)
  with is-globval (evalSmallValue regs v)
... | no ¬eq = no (λ { (_ , step-jmp eq l) → ¬eq (_ , eq) })
... | yes (lab , eq)
  with ↓-dec G lab
... | yes (code I , l)
  = yes (_ , step-jmp eq l)
... | no ¬l = no help
  where help : ¬ (∃ λ P' → G ⊢ H , register sp regs , jmp v ⇒ P')
        help (._ , step-jmp eq' l)
          with globval-helper eq eq'
        ... | refl = ¬l (_ , l)
step-dec G (H , R , halt) = no (λ { (_ , ()) })

step-prg-dec : ∀ P → Dec (∃ λ P' → ⊢ P ⇒ P')
step-prg-dec (going G (H , R , I))
  with I ≟ halt | step-dec G (H , R , I)
step-prg-dec (going G (H , R , .halt))
    | yes refl | _ = yes (halted , step-halting)
... | _ | yes (P' , step) = yes (going G P' , step-going step)
... | no I≢halt | no ¬step = no (help I≢halt ¬step)
  where help : ∀ {G H R I} →
                 I ≢ halt →
                 ¬ ∃ (λ P' → (G ⊢ (H , R , I) ⇒ P')) →
                 ¬ ∃ (λ P' → (⊢ going G (H , R , I) ⇒ P'))
        help I≢halt ¬step (_ , step-going step) = ¬step (_ , step)
        help I≢halt ¬step (_ , step-halting) = I≢halt refl
step-prg-dec halted = yes (halted , step-halted)

exec-dec : ∀ P n → Dec (∃ λ P' → ⊢ P ⇒ₙ n / P')
exec-dec P zero = yes (P , [])
exec-dec P (suc n) with step-prg-dec P
... | no ¬step = no (λ { (P'' , step ∷ exec) → ¬step (_ , step)})
... | yes (P' , step) with exec-dec P' n
... | no ¬exec = no (λ
  { (P'' , step' ∷ exec) → ¬exec (P'' ,
    subst (λ P → ⊢ P ⇒ₙ n / P'') (step-prg-unique step' step) exec
  )})
... | yes (P'' , exec) = yes (P'' , step ∷ exec)
