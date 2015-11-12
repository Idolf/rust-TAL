module Semantics where

open import Util
open import Judgments
open import Lemmas

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

  globval-helper : ∀ {lₕ₁ lₕ₂ ♯a₁ ♯a₂ w} →
                   w ≡ globval lₕ₁ ♯a₁ →
                   w ≡ globval lₕ₂ ♯a₂ →
                   lₕ₁ ≡ lₕ₂
  globval-helper refl refl = refl

  ↓-unique-heap : ∀ {H : Heap} {lₕ ws₁ ws₂} →
                    H ↓ lₕ ⇒ tuple ws₁ →
                    H ↓ lₕ ⇒ tuple ws₂ →
                    ws₁ ≡ ws₂
  ↓-unique-heap l₁ l₂ with ↓-unique l₁ l₂
  ... | refl = refl

eval-unique : ∀ {G w I₁ I₂} →
                EvalGlobal G w I₁ →
                EvalGlobal G w I₂ →
                I₁ ≡ I₂
eval-unique (instantiate-globval l₁) (instantiate-globval l₂)
  with ↓-unique l₁ l₂
... | refl = refl
eval-unique (instantiate-⟦⟧ eval₁ sub-I₁)
            (instantiate-⟦⟧ eval₂ sub-I₂)
  with eval-unique eval₁ eval₂
... | refl = subst-unique sub-I₁ sub-I₂

exec-unique : ∀ {G P P₁ P₂} →
                G ⊢ P ⇒ P₁ →
                G ⊢ P ⇒ P₂ →
                P₁ ≡ P₂
exec-unique (exec-add eq₁₁ eq₁₂) (exec-add eq₂₁ eq₂₂)
  rewrite int-helper eq₁₁ eq₂₁
        | int-helper eq₁₂ eq₂₂ = refl
exec-unique (exec-sub eq₁₁ eq₁₂) (exec-sub eq₂₁ eq₂₂)
  rewrite int-helper eq₁₁ eq₂₁
        | int-helper eq₁₂ eq₂₂ = refl
exec-unique exec-push exec-push = refl
exec-unique exec-pop exec-pop = refl
exec-unique (exec-sld l₁) (exec-sld l₂)
  rewrite ↓-unique l₁ l₂ = refl
exec-unique (exec-sst u₁) (exec-sst u₂)
  rewrite ←-unique u₁ u₂ = refl
exec-unique (exec-ld eq₁ l₁₁ l₁₂) (exec-ld eq₂ l₂₁ l₂₂)
  rewrite heapval-helper eq₁ eq₂
        | ↓-unique-heap l₁₁ l₂₁
        | ↓-unique l₁₂ l₂₂ = refl
exec-unique (exec-st eq₁ l₁ u₁₁ u₁₂) (exec-st eq₂ l₂ u₂₁ u₂₂)
  rewrite heapval-helper eq₁ eq₂
        | ↓-unique-heap l₁ l₂
        | ←-unique u₁₁ u₂₁
        | ←-unique u₁₂ u₂₂
  = refl
exec-unique exec-mov exec-mov = refl
exec-unique exec-malloc exec-malloc = refl
exec-unique (exec-beq₀ eq₁ eval₁) (exec-beq₀ eq₂ eval₂)
  with eval-unique eval₁ eval₂
... | refl = refl
exec-unique (exec-beq₀ eq₁ eval₁) (exec-beq₁ eq₂ neq₂)
  rewrite int-helper eq₁ eq₂ with neq₂ refl
... | ()
exec-unique (exec-beq₁ eq₁ neq₁) (exec-beq₀ eq₂ eval₂)
  rewrite int-helper eq₁ eq₂ with neq₁ refl
... | ()
exec-unique (exec-beq₁ eq₁ neq₁) (exec-beq₁ eq₂ neq₂) = refl
exec-unique (exec-jmp eval₁) (exec-jmp eval₂)
  with eval-unique eval₁ eval₂
... | refl = refl

execs-unique : ∀ {G P P₁ P₂ n} →
                 G ⊢ P ⇒ₙ n / P₁ →
                 G ⊢ P ⇒ₙ n / P₂ →
                 P₁ ≡ P₂
execs-unique [] [] = refl
execs-unique (exec₁ ∷ execs₁) (exec₂ ∷ execs₂)
  rewrite exec-unique exec₁ exec₂
        | execs-unique execs₁ execs₂ = refl

eval-dec : ∀ G w → Dec (∃ λ I → EvalGlobal G w I)
eval-dec G (globval l ♯a)
  with ↓-dec G l
... | no ¬l' = no (λ { (._ , instantiate-globval l) → ¬l' (_ , l) })
... | yes (code[ Δ ] Γ ∙ I , l') = yes (I , instantiate-globval l')
eval-dec G (heapval l) = no (λ { (_ , ()) })
eval-dec G (int n) = no (λ { (_ , ()) })
eval-dec G ns = no (λ { (_ , ()) })
eval-dec G (uninit τ) = no (λ { (_ , ()) })
eval-dec G (w ⟦ cᵥ / ι ⟧)
  with eval-dec G w
... | no ¬eval = no (λ { (._ , instantiate-⟦⟧ eval sub-I) → ¬eval (_ , eval) })
... | yes (I , eval)
  with I ⟦ Strong→Weak cᵥ / ι ⟧?
... | yes (I' , sub-I) = yes (I' , instantiate-⟦⟧ eval sub-I)
... | no ¬sub-I = no (λ { (._ , instantiate-⟦⟧ eval' sub-I) → help eval eval' ¬sub-I (_ , sub-I) })
  where help : ∀ {G w c I₁ I₂} →
                 EvalGlobal G w I₁ →
                 EvalGlobal G w I₂ →
                 ¬ (∃ λ I' → I₁ ⟦ c ⟧≡ I') →
                 ¬ (∃ λ I' → I₂ ⟦ c ⟧≡ I')
        help eval₁ eval₂ ¬sub-I sub-I
          rewrite eval-unique eval₁ eval₂ = ¬sub-I sub-I

private
  is-int : ∀ v → Dec (∃ λ n → v ≡ int n)
  is-int (globval l ♯a) = no (λ { (_ , ()) })
  is-int (heapval lₕ) = no (λ { (_ , ()) })
  is-int (int n) = yes (n , refl)
  is-int ns = no (λ { (_ , ()) })
  is-int (uninit τs) = no (λ { (_ , ()) })
  is-int (v' ⟦ c ⟧) = no (λ { (_ , ()) })

  ↓-is-int : ∀ regs ♯r → Dec (∃ λ n → regs ↓ ♯r ⇒ int n)
  ↓-is-int regs ♯r with ↓-dec regs ♯r
  ... | no ¬l = no (λ { (n , l) → ¬l (_ , l)})
  ... | yes (v , l) with is-int v
  ... | yes (n , eq) rewrite eq = yes (n , l)
  ... | no ¬eq = no (λ { (n , l') → ¬eq (n , ↓-unique l l')})

  is-heapval : ∀ v → Dec (∃ λ lₕ → v ≡ heapval lₕ)
  is-heapval (globval l ♯a) = no (λ { (_ , ()) })
  is-heapval (heapval lₕ) = yes (lₕ , refl)
  is-heapval (int n) = no (λ { (_ , ()) })
  is-heapval ns = no (λ { (_ , ()) })
  is-heapval (uninit τs) = no (λ { (_ , ()) })
  is-heapval (v' ⟦ c ⟧) = no (λ { (_ , ()) })

  ↓-is-heapval : ∀ regs ♯r → Dec (∃ λ lₕ → regs ↓ ♯r ⇒ heapval lₕ)
  ↓-is-heapval regs ♯r with ↓-dec regs ♯r
  ... | no ¬l = no (λ { (lₕ , l) → ¬l (_ , l)})
  ... | yes (v , l) with is-heapval v
  ... | yes (lₕ , eq) rewrite eq = yes (lₕ , l)
  ... | no ¬eq = no (λ { (lₕ , l') → ¬eq (lₕ , ↓-unique l l')})

exec-dec : ∀ G P → Dec (∃ λ P' → G ⊢ P ⇒ P')
exec-dec G (H , register sp regs , add ♯rd ♯rs v ~> I)
  with is-int (evalSmallValue regs v) | is-int (lookup ♯rs regs)
... | yes (n₁ , eq₁) | yes (n₂ , eq₂) = yes (_ , exec-add eq₁ eq₂)
... | no ¬eq₁ | _ = no (λ { (._ , exec-add eq₁ eq₂) → ¬eq₁ (_ , eq₁)})
... | _ | no ¬eq₂ = no (λ { (._ , exec-add eq₁ eq₂) → ¬eq₂ (_ , eq₂)})
exec-dec G (H , register sp regs , sub ♯rd ♯rs v ~> I)
  with is-int (evalSmallValue regs v) | is-int (lookup ♯rs regs)
... | yes (n₁ , eq₁) | yes (n₂ , eq₂) = yes (_ , exec-sub eq₁ eq₂)
... | no ¬eq₁ | _ = no (λ { (._ , exec-sub eq₁ eq₂) → ¬eq₁ (_ , eq₁)})
... | _ | no ¬eq₂ = no (λ { (._ , exec-sub eq₁ eq₂) → ¬eq₂ (_ , eq₂)})
exec-dec G (H , register sp regs , push v ~> I) = yes (_ , exec-push)
exec-dec G (H , register [] regs , pop ~> I) = no (λ { (_ , ()) })
exec-dec G (H , register (v ∷ sp) regs , pop ~> I) = yes (_ , exec-pop)
exec-dec G (H , register sp regs , sld ♯rd i ~> I)
  with ↓-dec sp i
... | yes (w , l) = yes (_ , exec-sld l)
... | no ¬l = no (λ { (._ , exec-sld l) → ¬l (_ , l)})
exec-dec G (H , register sp regs , sst i ♯rs ~> I)
  with ←-dec sp i (lookup ♯rs regs)
... | yes (sp' , up) = yes (_ , exec-sst up)
... | no ¬up = no (λ { (._ , exec-sst up) → ¬up (_ , up)})
exec-dec G (H , register sp regs , ld ♯rd ♯rs i ~> I)
  with is-heapval (lookup ♯rs regs)
... | no ¬eq = no (λ { (_ , exec-ld eq l₁ l₂) → ¬eq (_ , eq)})
... | yes (lₕ , eq) with ↓-dec H lₕ
... | no ¬l₁ = no help
  where help : ¬ (∃ λ P' → G ⊢ H , register sp regs , ld ♯rd ♯rs i ~> I ⇒ P')
        help (._ , exec-ld eq' l₁ l₂) with heapval-helper eq eq'
        ... | refl = ¬l₁ (_ , l₁)
... | yes (tuple ws , l₁) with ↓-dec ws i
... | no ¬l₂ = no help
  where help : ¬ (∃ λ P' → G ⊢ H , register sp regs , ld ♯rd ♯rs i ~> I ⇒ P')
        help (._ , exec-ld eq' l₁' l₂) with heapval-helper eq eq'
        ... | refl with ↓-unique-heap l₁ l₁'
        ... | refl = ¬l₂ (_ , l₂)
... | yes (w , l₂) = yes (_ , exec-ld eq l₁ l₂)
exec-dec G (H , register sp regs , st ♯rd i ♯rs ~> I)
  with is-heapval (lookup ♯rd regs)
... | no ¬eq = no (λ { (_ , exec-st eq l up₁ up₂)  → ¬eq (_ , eq)})
... | yes (lₕ , eq) with ↓-dec H lₕ
... | no ¬l = no help
  where help : ¬ (∃ λ P' → G ⊢ H , register sp regs , st ♯rd i ♯rs ~> I ⇒ P')
        help (._ , exec-st eq' l up₁ up₂) with heapval-helper eq eq'
        ... | refl = ¬l (_ , l)
... | yes (tuple ws , l) with ←-dec ws i (lookup ♯rs regs)
... | no ¬up₁ = no help
  where help : ¬ (∃ λ P' → G ⊢ H , register sp regs , st ♯rd i ♯rs ~> I ⇒ P')
        help (._ , exec-st eq' l' up₁ up₂) with heapval-helper eq eq'
        ... | refl with ↓-unique-heap l l'
        ... | refl = ¬up₁ (_ , up₁)
... | yes (ws' , up₁) with ←-dec H lₕ (tuple ws')
... | no ¬up₂ = no help
  where help : ¬ (∃ λ P' → G ⊢ H , register sp regs , st ♯rd i ♯rs ~> I ⇒ P')
        help (._ , exec-st eq' l' up₁' up₂) with heapval-helper eq eq'
        ... | refl with ↓-unique-heap l l'
        ... | refl with ←-unique up₁ up₁'
        ... | refl = ¬up₂ (_ , up₂)
... | yes (H' , up₂) = yes (_ , exec-st eq l up₁ up₂)
exec-dec G (H , register sp regs , malloc ♯rd τs ~> I) = yes (_ , exec-malloc)
exec-dec G (H , register sp regs , mov ♯rd v ~> I) = yes (_ , exec-mov)
exec-dec G (H , register sp regs , beq ♯r v ~> I)
  with is-int (lookup ♯r regs)
... | no ¬eq = no (λ { (._ , exec-beq₀ eq eval) → ¬eq (_ , eq)
                     ; (._ , exec-beq₁ eq neg) → ¬eq (_ , eq)})
... | yes (suc n , eq) = yes (_ , exec-beq₁ eq (λ ()))
... | yes (zero , eq) with eval-dec G (evalSmallValue regs v)
... | no ¬eval = no (λ { (._ , exec-beq₀ eq' eval) → ¬eval (_ , eval)
                       ; (._ , exec-beq₁ eq' neq) →
                             neq (int-helper eq' eq)})
... | yes (I' , eval) = yes (_ , exec-beq₀ eq eval)
exec-dec G (H , register sp regs , jmp v)
  with eval-dec G (evalSmallValue regs v)
... | no ¬eval = no (λ { (._ , exec-jmp  eval) → ¬eval (_ , eval) })
... | yes (I' , eval) = yes (_ , exec-jmp eval)

execs-dec : ∀ G P n → Dec (∃ λ P' → G ⊢ P ⇒ₙ n / P')
execs-dec G P zero = yes (P , [])
execs-dec G P (suc n) with exec-dec G P
... | no ¬exec = no (λ { (P'' , exec ∷ execs) → ¬exec (_ , exec)})
... | yes (P' , exec) with execs-dec G P' n
... | no ¬execs = no (λ
  { (P'' , exec' ∷ execs) → ¬execs (P'' ,
    subst (λ p → G ⊢ p ⇒ₙ n / P'') (exec-unique exec' exec) execs
  )})
... | yes (P'' , execs) = yes (P'' , exec ∷ execs)
