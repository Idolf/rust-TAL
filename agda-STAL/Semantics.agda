open import Util
open import Grammar
open import Substitution

evalSmallValue : Vec WordValue ♯regs → SmallValue → WordValue
evalSmallValue regs (reg ♯r) = lookup ♯r regs
evalSmallValue regs (word w) = w
evalSmallValue regs (v ⟦ i ⟧ᵥ) = evalSmallValue regs v ⟦ i ⟧

infix 4 _⊢_⇒_
data _⊢_⇒_ (G : Globals) : Program → Program → Set where
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
          ∀ {H sp regs I ♯rd ♯rs i lₕ h w} →
             lookup ♯rs regs ≡ heapval lₕ →
                     H ↓ lₕ ⇒ tuple h →
                     h ↓ i ⇒ w →
      -----------------------------------------------
      G ⊢ H , register sp regs , ld ♯rd ♯rs i ~> I ⇒
          H , register sp (update ♯rd w regs) , I

    exec-st :
          ∀ {H H' sp regs I ♯rd ♯rs i lₕ} {h h'} →
             lookup ♯rd regs ≡ heapval lₕ →
                       H ↓ lₕ ⇒ tuple h →
              h ⟦ i ⟧← lookup ♯rs regs ⇒ h' →
                    H ⟦ lₕ ⟧← tuple h' ⇒ H' →
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
      ------------------------------------------------------------------
      G ⊢ H , register sp regs , mov ♯rd v ~> I ⇒
          H , register sp (update ♯rd (evalSmallValue regs v) regs) , I

    exec-beq₀ :
                ∀ {H sp regs I₁ I₂ ♯r v l Δ Γ} →
               lookup ♯r regs ≡ const 0 →
          evalSmallValue regs v ≡ globval l →
                G ↓ l ⇒ ∀[ Δ ] Γ ∙ I₁ →
      ------------------------------------------
      G ⊢ H , register sp regs , beq ♯r v ~> I₂ ⇒
          H , register sp regs , I₁

    exec-beq₁ :
                ∀ {H sp regs I ♯r v n₀} →
              lookup ♯r regs ≡ const n₀ →
                        n₀ ≢ 0 →
      ------------------------------------------
      G ⊢ H , register sp regs , beq ♯r v ~> I ⇒
          H , register sp regs , I

    exec-jmp :
         ∀ {H sp regs v l Δ Γ I} →
      evalSmallValue regs v ≡ globval l →
          G ↓ l ⇒ ∀[ Δ ] Γ ∙ I →
      ----------------------------------
      G ⊢ H , register sp regs , jmp v ⇒
          H , register sp regs , I

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

  globval-helper : ∀ {lₕ₁ lₕ₂ w} →
                   w ≡ globval lₕ₁ →
                   w ≡ globval lₕ₂ →
                   lₕ₁ ≡ lₕ₂
  globval-helper refl refl = refl

  ∀-injective₃ : ∀ {Δ₁ Δ₂ Γ₁ Γ₂ I₁ I₂} →
                   ∀[ Δ₁ ] Γ₁ ∙ I₁ ≡ ∀[ Δ₂ ] Γ₂ ∙ I₂ →
                   I₁ ≡ I₂
  ∀-injective₃ refl = refl

  ↓-unique-heap : ∀ {H : Heap} {lₕ ws₁ ws₂} →
                    H ↓ lₕ ⇒ tuple ws₁ →
                    H ↓ lₕ ⇒ tuple ws₂ →
                    ws₁ ≡ ws₂
  ↓-unique-heap l₁ l₂ with ↓-unique l₁ l₂
  ... | refl = refl

exec-unique : ∀ {H sp regs I G P₁ P₂} →
                G ⊢ H , register sp regs , I ⇒ P₁ →
                G ⊢ H , register sp regs , I ⇒ P₂ →
                P₁ ≡ P₂
exec-unique (exec-add eq₁₁ eq₁₂) (exec-add eq₂₁ eq₂₂)
  rewrite const-helper eq₁₁ eq₂₁
        | const-helper eq₁₂ eq₂₂ = refl
exec-unique (exec-sub eq₁₁ eq₁₂) (exec-sub eq₂₁ eq₂₂)
  rewrite const-helper eq₁₁ eq₂₁
        | const-helper eq₁₂ eq₂₂ = refl
exec-unique exec-push exec-push = refl
exec-unique exec-pop exec-pop = refl
exec-unique {I = sld ♯rd i ~> I} (exec-sld l₁) (exec-sld l₂)
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
exec-unique (exec-beq₀ eq₁₁ eq₁₂ l₁) (exec-beq₀ eq₂₁ eq₂₂ l₂)
  rewrite const-helper eq₁₁ eq₂₁
        | globval-helper eq₁₂ eq₂₂
        | ∀-injective₃ (↓-unique l₁ l₂) = refl
exec-unique (exec-beq₀ eq₁₁ eq₁₂ l₁) (exec-beq₁ eq₂ neq₂)
  rewrite const-helper eq₁₁ eq₂ with neq₂ refl
... | ()
exec-unique (exec-beq₁ eq₁ neq₁) (exec-beq₀ eq₂₁ eq₂₂ l₂)
  rewrite const-helper eq₁ eq₂₁ with neq₁ refl
... | ()
exec-unique (exec-beq₁ eq₁ neq₁) (exec-beq₁ eq₂ neq₂) = refl
exec-unique (exec-jmp eq₁ l₁) (exec-jmp eq₂ l₂)
  rewrite globval-helper eq₁ eq₂
        | ∀-injective₃ (↓-unique l₁ l₂)
  = refl
