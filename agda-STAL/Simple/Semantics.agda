module Simple.Semantics where

open import Data.List using (drop)
open import Util
open import Simple.Grammar

evalSmallValue : Vec WordValue ♯regs → SmallValue → WordValue
evalSmallValue regs (reg ♯r) = lookup ♯r regs
evalSmallValue regs (globval l) = globval l
evalSmallValue regs (int i) = int i
evalSmallValue regs ns = ns
evalSmallValue regs uninit = uninit

infix 3 _⊢_⇒_
data _⊢_⇒_ (G : Globals) : ProgramState → ProgramState → Set where
    step-add :
             ∀ {H sp regs I ♯rd ♯rs v n₁ n₂} →
          evalSmallValue regs v ≡ int n₁ →
                lookup ♯rs regs ≡ int n₂ →
      ---------------------------------------------------------
      G ⊢ H , register sp regs , add ♯rd ♯rs v ~> I ⇒
          H , register sp (update ♯rd (int (n₁ + n₂)) regs) , I

    step-sub :
             ∀ {H sp regs I ♯rd ♯rs v n₁ n₂} →
          evalSmallValue regs v ≡ int n₁ →
                lookup ♯rs regs ≡ int n₂ →
      ---------------------------------------------------------
      G ⊢ H , register sp regs , sub ♯rd ♯rs v ~> I ⇒
          H , register sp (update ♯rd (int (n₁ ∸ n₂)) regs) , I

    step-salloc :
                      ∀ {H sp regs I n} →
      ------------------------------------------------
      G ⊢ H , register sp regs , salloc n ~> I ⇒
          H , register (replicate n ns ++ sp) regs , I

    step-sfree :
                ∀ {H sp regs I n} →
      -----------------------------------------
      G ⊢ H , register sp regs , sfree n ~> I ⇒
          H , register (drop n sp) regs , I

    step-sld :
             ∀ {H sp regs I ♯rd i w} →
                    sp ↓ i ⇒ w →
      -------------------------------------------
      G ⊢ H , register sp regs , sld ♯rd i ~> I ⇒
          H , register sp (update ♯rd w regs) , I

    step-sst :
             ∀ {H sp sp' regs I ♯rs i} →
           sp ⟦ i ⟧← lookup ♯rs regs ⇒ sp' →
      --------------------------------------------
      G ⊢ H , register sp  regs , sst i ♯rs ~> I ⇒
          H , register sp' regs , I

    step-ld :
          ∀ {H sp regs I ♯rd ♯rs i lₕ ws w} →
             lookup ♯rs regs ≡ heapval lₕ →
                     H ↓ lₕ ⇒ tuple ws →
                     ws ↓ i ⇒ w →
      ----------------------------------------------
      G ⊢ H , register sp regs , ld ♯rd ♯rs i ~> I ⇒
          H , register sp (update ♯rd w regs) , I

    step-st :
          ∀ {H H' sp regs I ♯rd i ♯rs lₕ ws ws'} →
             lookup ♯rd regs ≡ heapval lₕ →
                       H ↓ lₕ ⇒ tuple ws →
              ws ⟦ i ⟧← lookup ♯rs regs ⇒ ws' →
                    H ⟦ lₕ ⟧← tuple ws' ⇒ H' →
      -----------------------------------------------
      G ⊢ H  , register sp regs , st ♯rd i ♯rs ~> I ⇒
          H' , register sp regs , I

    step-malloc :
                    ∀ {H sp regs I ♯rd n} →
      ----------------------------------------------------------
      G ⊢ H , register sp regs , malloc ♯rd n ~> I ⇒
          H ∷ʳ tuple (replicate n uninit) ,
          register sp (update ♯rd (heapval (length H)) regs) , I

    step-mov :
                       ∀ {H sp regs I ♯rd v} →
      -----------------------------------------------------------------
      G ⊢ H , register sp regs , mov ♯rd v ~> I ⇒
          H , register sp (update ♯rd (evalSmallValue regs v) regs) , I

    step-beq₀ :
            ∀ {H sp regs ♯r v l I₁ I₂} →
             lookup ♯r regs ≡ int 0 →
           evalSmallValue regs v ≡ globval l →
                    G ↓ l ⇒ code I₂ →
      -------------------------------------------
      G ⊢ H , register sp regs , beq ♯r v ~> I₁ ⇒
          H , register sp regs , I₂

    step-beq₁ :
                ∀ {H sp regs I ♯r v n₀} →
              lookup ♯r regs ≡ int n₀ →
                        n₀ ≢ 0 →
      ------------------------------------------
      G ⊢ H , register sp regs , beq ♯r v ~> I ⇒
          H , register sp regs , I

    step-jmp :
           ∀ {H sp regs v l I} →
      evalSmallValue regs v ≡ globval l →
               G ↓ l ⇒ code I →
      -----------------------------------
      G ⊢ H , register sp regs , jmp v ⇒
          H , register sp regs , I

infix 3 ⊢_⇒_
data ⊢_⇒_ : Program → Program → Set where
  step-going :
          ∀ {G P P'} →
          G ⊢ P ⇒ P' →
    ------------------------
    ⊢ going G P ⇒ going G P'

  step-halting :
               ∀ {G H R} →
    ---------------------------------
    ⊢ going G (H , R , halt) ⇒ halted

  step-halted :
    -----------------
    ⊢ halted ⇒ halted

infix 3 ⊢_⇒ₙ_/_
infixr 5 _∷_
data ⊢_⇒ₙ_/_ : Program → ℕ → Program → Set where
  []  :
       ∀ {P} →
    ------------
    ⊢ P ⇒ₙ 0 / P

  _∷_ :
       ∀ {P₁ P₂ P₃ n} →
          ⊢ P₁ ⇒ P₂ →
       ⊢ P₂ ⇒ₙ n / P₃ →
      ------------------
      ⊢ P₁ ⇒ₙ suc n / P₃
