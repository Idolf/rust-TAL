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
             ∀ {H sp regs Is ♯rd ♯rs v n₁ n₂} →
          evalSmallValue regs v ≡ const n₁ →
                lookup ♯rs regs ≡ const n₂ →
      ------------------------------------------------------------
      G ⊢ H , register sp regs , add ♯rd ♯rs v ~> Is ⇒
          H , register sp (update ♯rd (const (n₁ + n₂)) regs) , Is

    exec-sub :
             ∀ {H sp regs Is ♯rd ♯rs v n₁ n₂} →
          evalSmallValue regs v ≡ const n₁ →
                lookup ♯rs regs ≡ const n₂ →
      ------------------------------------------------------------
      G ⊢ H , register sp regs , sub ♯rd ♯rs v ~> Is ⇒
          H , register sp (update ♯rd (const (n₁ ∸ n₂)) regs) , Is

    exec-push :
                      ∀ {H sp regs Is v} →
      -------------------------------------------------------
      G ⊢ H , register sp regs , push v ~> Is ⇒
          H , register (evalSmallValue regs v ∷ sp) regs , Is

    exec-pop :
                  ∀ {H w sp regs Is} →
      --------------------------------------------
      G ⊢ H , register (w ∷ sp) regs , pop ~> Is ⇒
          H , register sp regs , Is

    exec-sld :
             ∀ {H sp regs Is ♯rd i w} →
                    sp ↓ i ⇒ w →
      --------------------------------------------
      G ⊢ H , register sp regs , sld ♯rd i ~> Is ⇒
          H , register sp (update ♯rd w regs) , Is

    exec-sst :
             ∀ {H sp sp' regs Is ♯rs i} →
           sp ⟦ i ⟧← lookup ♯rs regs ⇒ sp' →
      --------------------------------------------
      G ⊢ H , register sp  regs , sst i ♯rs ~> Is ⇒
          H , register sp' regs , Is

    exec-ld :
          ∀ {H sp regs Is ♯rd ♯rs i lₕ h w} →
             lookup ♯rs regs ≡ heapval lₕ →
                     H ↓ lₕ ⇒ h →
                     h ↓ i ⇒ w →
      -----------------------------------------------
      G ⊢ H , register sp regs , ld ♯rd ♯rs i ~> Is ⇒
          H , register sp (update ♯rd w regs) , Is

    exec-st :
          ∀ {H H' sp regs Is ♯rd ♯rs i lₕ h h'} →
             lookup ♯rd regs ≡ heapval lₕ →
                       H ↓ lₕ ⇒ h →
              h ⟦ i ⟧← lookup ♯rs regs ⇒ h' →
                    H ⟦ lₕ ⟧← h' ⇒ H' →
      -----------------------------------------------
      G ⊢ H  , register sp regs , st ♯rd i ♯rs ~> Is ⇒
          H' , register sp regs , Is

    exec-mov :
                       ∀ {H sp regs Is ♯rd v} →
      ------------------------------------------------------------------
      G ⊢ H , register sp regs , mov ♯rd v ~> Is ⇒
          H , register sp (update ♯rd (evalSmallValue regs v) regs) , Is

    exec-malloc :
                    ∀ {H sp regs Is ♯rd τs} →
      --------------------------------------------------------
      G ⊢ H , register sp regs , malloc ♯rd τs ~> Is ⇒
          H ∷ʳ map uninit τs ,
          register sp (update ♯rd (heapval (length H)) regs) ,
          Is

    exec-jmp :
         ∀ {H sp regs v l Δ Γ Is} →
      evalSmallValue regs v ≡ globval l →
          G ↓ l ⇒ ∀[ Δ ] Γ ∙ Is →
      ----------------------------------
      G ⊢ H , register sp regs , jmp v ⇒
          H , register sp regs , Is

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

  ∀-injective₃ : ∀ {Δ₁ Δ₂ Γ₁ Γ₂ Is₁ Is₂} →
                   ∀[ Δ₁ ] Γ₁ ∙ Is₁ ≡ ∀[ Δ₂ ] Γ₂ ∙ Is₂ →
                   Is₁ ≡ Is₂
  ∀-injective₃ refl = refl

exec-unique : ∀ {H sp regs Is G P₁ P₂} →
                G ⊢ H , register sp regs , Is ⇒ P₁ →
                G ⊢ H , register sp regs , Is ⇒ P₂ →
                P₁ ≡ P₂
exec-unique (exec-add eq₁₁ eq₁₂) (exec-add eq₂₁ eq₂₂)
  rewrite const-helper eq₁₁ eq₂₁
        | const-helper eq₁₂ eq₂₂ = refl
exec-unique (exec-sub eq₁₁ eq₁₂) (exec-sub eq₂₁ eq₂₂)
  rewrite const-helper eq₁₁ eq₂₁
        | const-helper eq₁₂ eq₂₂ = refl
exec-unique exec-push exec-push = refl
exec-unique exec-pop exec-pop = refl
exec-unique {Is = sld ♯rd i ~> Is} (exec-sld l₁) (exec-sld l₂)
  rewrite ↓-unique l₁ l₂ = refl
exec-unique (exec-sst u₁) (exec-sst u₂)
  rewrite ←-unique u₁ u₂ = refl
exec-unique (exec-ld eq₁ l₁₁ l₁₂) (exec-ld eq₂ l₂₁ l₂₂)
  rewrite heapval-helper eq₁ eq₂ |
          ↓-unique l₁₁ l₂₁ |
          ↓-unique l₁₂ l₂₂ = refl
exec-unique (exec-st eq₁ l₁ u₁₁ u₁₂) (exec-st eq₂ l₂ u₂₁ u₂₂)
  rewrite heapval-helper eq₁ eq₂
        | ↓-unique l₁ l₂
        | ←-unique u₁₁ u₂₁
        | ←-unique u₁₂ u₂₂
  = refl
exec-unique exec-mov exec-mov = refl
exec-unique exec-malloc exec-malloc = refl
exec-unique (exec-jmp eq₁ l₁) (exec-jmp eq₂ l₂)
  rewrite globval-helper eq₁ eq₂
        | ∀-injective₃ (↓-unique l₁ l₂)
  = refl
