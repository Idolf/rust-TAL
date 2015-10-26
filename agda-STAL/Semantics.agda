open import Util
open import Grammar
open import Substitution

evalSmallValue : Vec WordValue ♯regs → SmallValue → WordValue
evalSmallValue regs (reg ♯r) = lookup ♯r regs
evalSmallValue regs (word w) = w
evalSmallValue regs (v ⟦ i ⟧ᵥ) = evalSmallValue regs v ⟦ i ⟧

data EvalGlobal (G : Globals) : WordValue → GlobalValue → Set where
  instantiate-globval :
                 ∀ {l ♯a Δ Γ I} →
             G ↓ l ⇒ (∀[ Δ ] Γ ∙ I) →
                  length Δ ≡ ♯a →
    ------------------------------------------
    EvalGlobal G (globval l ♯a) (∀[ Δ ] Γ ∙ I)

  instantiate-⟦⟧ :
           ∀ {w c Δ Δ' Γ Γ' I I'} →
         EvalGlobal G w (∀[ Δ ] Γ ∙ I) →
               Run Δ ⟦ c ⟧≡ Δ' →
                 Γ ⟦ c ⟧≡ Γ' →
                 I ⟦ c ⟧≡ I' →
    -----------------------------------------
    EvalGlobal G (w ⟦ c ⟧) (∀[ Δ' ] Γ' ∙ I')

infix 3 _⊢_⇒_
data _⊢_⇒_ (G : Globals) : ProgramState → ProgramState → Set where
    exec-add :
             ∀ {H sp regs I ♯rd ♯rs v n₁ n₂} →
          evalSmallValue regs v ≡ const n₁ →
                lookup ♯rs regs ≡ const n₂ →
      ------------------------------------------------------------
      G ⊢ H , register sp regs , add ♯rd ♯rs v ~> I ⇒
          H , register sp (update ♯rd (const (n₁ + n₂)) regs) , I

    exec-sub :
             ∀ {H sp regs I ♯rd ♯rs v n₁ n₂} →
          evalSmallValue regs v ≡ const n₁ →
                lookup ♯rs regs ≡ const n₂ →
      ------------------------------------------------------------
      G ⊢ H , register sp regs , sub ♯rd ♯rs v ~> I ⇒
          H , register sp (update ♯rd (const (n₁ ∸ n₂)) regs) , I

    exec-push :
                      ∀ {H sp regs I v} →
      -------------------------------------------------------
      G ⊢ H , register sp regs , push v ~> I ⇒
          H , register (evalSmallValue regs v ∷ sp) regs , I

    exec-pop :
                  ∀ {H w sp regs I} →
      --------------------------------------------
      G ⊢ H , register (w ∷ sp) regs , pop ~> I ⇒
          H , register sp regs , I

    exec-sld :
             ∀ {H sp regs I ♯rd i w} →
                    sp ↓ i ⇒ w →
      --------------------------------------------
      G ⊢ H , register sp regs , sld ♯rd i ~> I ⇒
          H , register sp (update ♯rd w regs) , I

    exec-sst :
             ∀ {H sp sp' regs I ♯rs i} →
           sp ⟦ i ⟧← lookup ♯rs regs ⇒ sp' →
      --------------------------------------------
      G ⊢ H , register sp  regs , sst i ♯rs ~> I ⇒
          H , register sp' regs , I

    exec-ld :
          ∀ {H sp regs I ♯rd ♯rs i lₕ ws w} →
             lookup ♯rs regs ≡ heapval lₕ →
                     H ↓ lₕ ⇒ tuple ws →
                     ws ↓ i ⇒ w →
      -----------------------------------------------
      G ⊢ H , register sp regs , ld ♯rd ♯rs i ~> I ⇒
          H , register sp (update ♯rd w regs) , I

    exec-st :
          ∀ {H H' sp regs I ♯rd ♯rs i lₕ ws ws'} →
             lookup ♯rd regs ≡ heapval lₕ →
                       H ↓ lₕ ⇒ tuple ws →
              ws ⟦ i ⟧← lookup ♯rs regs ⇒ ws' →
                    H ⟦ lₕ ⟧← tuple ws' ⇒ H' →
      -----------------------------------------------
      G ⊢ H  , register sp regs , st ♯rd i ♯rs ~> I ⇒
          H' , register sp regs , I

    exec-malloc :
                    ∀ {H sp regs I ♯rd τs} →
      --------------------------------------------------------
      G ⊢ H , register sp regs , malloc ♯rd τs ~> I ⇒
          H ∷ʳ tuple (map uninit τs) ,
          register sp (update ♯rd (heapval (length H)) regs) ,
          I

    exec-mov :
                       ∀ {H sp regs I ♯rd v} →
      -----------------------------------------------------------------
      G ⊢ H , register sp regs , mov ♯rd v ~> I ⇒
          H , register sp (update ♯rd (evalSmallValue regs v) regs) , I

    exec-beq₀ :
                    ∀ {H sp regs ♯r v Γ I₁ I₂} →
                     lookup ♯r regs ≡ const 0 →
      EvalGlobal G (evalSmallValue regs v) (∀[ [] ] Γ ∙ I₂) →
      -------------------------------------------------------
             G ⊢ H , register sp regs , beq ♯r v ~> I₁ ⇒
                 H , register sp regs , I₂

    exec-beq₁ :
                ∀ {H sp regs I ♯r v n₀} →
              lookup ♯r regs ≡ const n₀ →
                        n₀ ≢ 0 →
      ------------------------------------------
      G ⊢ H , register sp regs , beq ♯r v ~> I ⇒
          H , register sp regs , I

    exec-jmp :
                    ∀ {H sp regs v Γ I} →
      EvalGlobal G (evalSmallValue regs v) (∀[ [] ] Γ ∙ I) →
      ------------------------------------------------------
               G ⊢ H , register sp regs , jmp v ⇒
                   H , register sp regs , I

infix 3 _⊢_⇒ₙ_/_
infix 5 _∷_
data _⊢_⇒ₙ_/_ (G : Globals) : ProgramState → ℕ → ProgramState → Set where
  []  :
        ∀ {P} →
    --------------
    G ⊢ P ⇒ₙ 0 / P

  _∷_ :
       ∀ {P₁ P₂ P₃ n} →
         G ⊢ P₁ ⇒ P₂ →
       G ⊢ P₂ ⇒ₙ n / P₃ →
      --------------------
      G ⊢ P₁ ⇒ₙ suc n / P₃

private
  const-helper : ∀ {n₁ n₂ w} →
                   w ≡ const n₁ →
                   w ≡ const n₂ →
                   n₁ ≡ n₂
  const-helper refl refl = refl

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

eval-unique : ∀ {G w g₁ g₂} →
                EvalGlobal G w g₁ →
                EvalGlobal G w g₂ →
                g₁ ≡ g₂
eval-unique (instantiate-globval l₁ eq₁) (instantiate-globval l₂ eq₂)
  rewrite ↓-unique l₁ l₂ = refl
eval-unique (instantiate-⟦⟧ eval₁ run-Δ₁ sub-Γ₁ sub-I₁)
            (instantiate-⟦⟧ eval₂ run-Δ₂ sub-Γ₂ sub-I₂)
  with eval-unique eval₁ eval₂
... | refl
  rewrite run-unique run-Δ₁ run-Δ₂
        | subst-unique {W = ℕ} sub-Γ₁ sub-Γ₂
        | subst-unique {W = ℕ} sub-I₁ sub-I₂ = refl

exec-unique : ∀ {G P P₁ P₂} →
                G ⊢ P ⇒ P₁ →
                G ⊢ P ⇒ P₂ →
                P₁ ≡ P₂
exec-unique (exec-add eq₁₁ eq₁₂) (exec-add eq₂₁ eq₂₂)
  rewrite const-helper eq₁₁ eq₂₁
        | const-helper eq₁₂ eq₂₂ = refl
exec-unique (exec-sub eq₁₁ eq₁₂) (exec-sub eq₂₁ eq₂₂)
  rewrite const-helper eq₁₁ eq₂₁
        | const-helper eq₁₂ eq₂₂ = refl
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
  rewrite const-helper eq₁ eq₂ with neq₂ refl
... | ()
exec-unique (exec-beq₁ eq₁ neq₁) (exec-beq₀ eq₂ eval₂)
  rewrite const-helper eq₁ eq₂ with neq₁ refl
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

eval-dec : ∀ G w → Dec (∃ λ g → EvalGlobal G w g)
eval-dec G (globval l ♯a)
  with ↓-dec G l
... | no ¬l' = no (λ { (._ , instantiate-globval l' eq) → ¬l' (_ , l') })
... | yes (∀[ Δ ] Γ ∙ I , l') with length Δ ≟ ♯a
... | yes ♯a≡len = yes (∀[ Δ ] Γ ∙ I , instantiate-globval l' ♯a≡len)
... | no ♯a≢len = no (λ { (._ , instantiate-globval l'' eq) →
                     help l' l'' ♯a≢len eq })
  where help : ∀ {G l ♯a Δ₁ Δ₂ Γ₁ Γ₂ I₁ I₂} →
                 G ↓ l ⇒ ∀[ Δ₁ ] Γ₁ ∙ I₁ →
                 G ↓ l ⇒ ∀[ Δ₂ ] Γ₂ ∙ I₂ →
                 length Δ₁ ≢ ♯a →
                 length Δ₂ ≢ ♯a
        help l₁ l₂ neq eq with ↓-unique l₁ l₂
        ... | refl = neq eq
eval-dec G (heapval l) = no (λ { (_ , ()) })
eval-dec G (const n) = no (λ { (_ , ()) })
eval-dec G ns = no (λ { (_ , ()) })
eval-dec G (uninit τ) = no (λ { (_ , ()) })
eval-dec G (w ⟦ c ⟧) with eval-dec G w
... | no ¬eval =
  no (λ { (._ , instantiate-⟦⟧ eval run-Δ sub-Γ sub-I) → ¬eval (_ , eval) })
... | yes (∀[ Δ ] Γ ∙ I , eval₁)
  with Run Δ ⟦ c ⟧? |  Γ ⟦ c ⟧? | I ⟦ c ⟧?
... | yes (Δ' , run-Δ) | yes (Γ' , sub-Γ) | yes (I' , sub-I) =
 yes (∀[ Δ' ] Γ' ∙ I' , instantiate-⟦⟧ eval₁ run-Δ sub-Γ sub-I)
... | no ¬run-Δ | _ | _ =
  no (λ { (∀[ Δ' ] Γ' ∙ I' , instantiate-⟦⟧ eval₂ run-Δ sub-Γ sub-I) →
    help eval₁ eval₂ ¬run-Δ (Δ' , run-Δ) })
  where help : ∀ {G w c Δ₁ Δ₂ Γ₁ Γ₂ I₁ I₂} →
                 EvalGlobal G w (∀[ Δ₁ ] Γ₁ ∙ I₁) →
                 EvalGlobal G w (∀[ Δ₂ ] Γ₂ ∙ I₂) →
                 ¬ (∃ λ Δ' → Run Δ₁ ⟦ c ⟧≡ Δ') →
                 ¬ (∃ λ Δ' → Run Δ₂ ⟦ c ⟧≡ Δ')
        help eval₁ eval₂ ¬run-Δ run-Δ
          with eval-unique eval₁ eval₂
        ... | refl = ¬run-Δ run-Δ
... | _ | no ¬sub-Γ | _ =
  no (λ { (∀[ Δ' ] Γ' ∙ I' , instantiate-⟦⟧ eval₂ run-Δ sub-Γ sub-I) →
    help eval₁ eval₂ ¬sub-Γ (Γ' , sub-Γ) })
  where help : ∀ {G w} {c : StrongCast} {Δ₁ Δ₂ Γ₁ Γ₂ I₁ I₂} →
                 EvalGlobal G w (∀[ Δ₁ ] Γ₁ ∙ I₁) →
                 EvalGlobal G w (∀[ Δ₂ ] Γ₂ ∙ I₂) →
                 ¬ (∃ λ Γ' → Γ₁ ⟦ c ⟧≡ Γ') →
                 ¬ (∃ λ Γ' → Γ₂ ⟦ c ⟧≡ Γ')
        help eval₁ eval₂ ¬sub-Γ sub-Γ
          with eval-unique eval₁ eval₂
        ... | refl = ¬sub-Γ sub-Γ
... | _ | _ | no ¬sub-I =
  no (λ { (∀[ Δ' ] Γ' ∙ I' , instantiate-⟦⟧ eval₂ run-Δ sub-Γ sub-I) →
    help eval₁ eval₂ ¬sub-I (I' , sub-I) })
  where help : ∀ {G w} {c : StrongCast} {Δ₁ Δ₂ Γ₁ Γ₂ I₁ I₂} →
                 EvalGlobal G w (∀[ Δ₁ ] Γ₁ ∙ I₁) →
                 EvalGlobal G w (∀[ Δ₂ ] Γ₂ ∙ I₂) →
                 ¬ (∃ λ I' → I₁ ⟦ c ⟧≡ I') →
                 ¬ (∃ λ I' → I₂ ⟦ c ⟧≡ I')
        help eval₁ eval₂ ¬sub-I sub-I
          with eval-unique eval₁ eval₂
        ... | refl = ¬sub-I sub-I

private
  is-const : ∀ v → Dec (∃ λ n → v ≡ const n)
  is-const (globval l ♯a) = no (λ { (_ , ()) })
  is-const (heapval lₕ) = no (λ { (_ , ()) })
  is-const (const n) = yes (n , refl)
  is-const ns = no (λ { (_ , ()) })
  is-const (uninit τs) = no (λ { (_ , ()) })
  is-const (v' ⟦ c ⟧) = no (λ { (_ , ()) })

  ↓-is-const : ∀ regs ♯r → Dec (∃ λ n → regs ↓ ♯r ⇒ const n)
  ↓-is-const regs ♯r with ↓-dec regs ♯r
  ... | no ¬l = no (λ { (n , l) → ¬l (_ , l)})
  ... | yes (v , l) with is-const v
  ... | yes (n , eq) rewrite eq = yes (n , l)
  ... | no ¬eq = no (λ { (n , l') → ¬eq (n , ↓-unique l l')})

  is-heapval : ∀ v → Dec (∃ λ lₕ → v ≡ heapval lₕ)
  is-heapval (globval l ♯a) = no (λ { (_ , ()) })
  is-heapval (heapval lₕ) = yes (lₕ , refl)
  is-heapval (const n) = no (λ { (_ , ()) })
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
  with is-const (evalSmallValue regs v) | is-const (lookup ♯rs regs)
... | yes (n₁ , eq₁) | yes (n₂ , eq₂) = yes (_ , exec-add eq₁ eq₂)
... | no ¬eq₁ | _ = no (λ { (._ , exec-add eq₁ eq₂) → ¬eq₁ (_ , eq₁)})
... | _ | no ¬eq₂ = no (λ { (._ , exec-add eq₁ eq₂) → ¬eq₂ (_ , eq₂)})
exec-dec G (H , register sp regs , sub ♯rd ♯rs v ~> I)
  with is-const (evalSmallValue regs v) | is-const (lookup ♯rs regs)
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
  with is-const (lookup ♯r regs)
... | no ¬eq = no (λ { (._ , exec-beq₀ eq eval) → ¬eq (_ , eq)
                     ; (._ , exec-beq₁ eq neg) → ¬eq (_ , eq)})
... | yes (suc n , eq) = yes (_ , exec-beq₁ eq (λ ()))
... | yes (zero , eq) with eval-dec G (evalSmallValue regs v)
... | no ¬eval = no (λ { (._ , exec-beq₀ eq' eval) → ¬eval (_ , eval)
                       ; (._ , exec-beq₁ eq' neq) →
                             neq (const-helper eq' eq)})
... | yes (∀[ [] ] Γ ∙ I' , eval) = yes (_ , exec-beq₀ eq eval)
... | yes (∀[ a ∷ Δ ] Γ ∙ I' , eval) = no help
  where help : ¬ (∃ λ P' → G ⊢ H , register sp regs , beq ♯r v ~> I ⇒ P')
        help (._ , exec-beq₀ eq' eval') with eval-unique eval eval'
        ... | ()
        help (._ , exec-beq₁ eq' neq) = neq (const-helper eq' eq)
exec-dec G (H , register sp regs , jmp v)
  with eval-dec G (evalSmallValue regs v)
... | no ¬eval = no (λ { (._ , exec-jmp  eval) → ¬eval (_ , eval) })
... | yes (∀[ [] ] Γ ∙ I' , eval) = yes (_ , exec-jmp eval)
... | yes (∀[ a ∷ Δ ] Γ ∙ I' , eval) = no help
  where help : ¬ (∃ λ P' → G ⊢ H , register sp regs , jmp v ⇒ P')
        help (._ , exec-jmp eval') with eval-unique eval eval'
        ... | ()

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
