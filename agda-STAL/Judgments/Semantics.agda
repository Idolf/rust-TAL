module Judgments.Semantics where

open import Util
open import Judgments.Grammar
open import Judgments.Substitution
open import Judgments.Run

-- The purpose of this file is to define the
-- small-step semantics for our assembler language

evalSmallValue : Vec WordValue ♯regs → SmallValue → WordValue
evalSmallValue regs (reg ♯r) = lookup ♯r regs
evalSmallValue regs (word w) = w
evalSmallValue regs (v ⟦ i ⟧) = evalSmallValue regs v ⟦ i ⟧

data EvalGlobal (G : Globals) : WordValue → GlobalValue → Set where
  instantiate-globval :
                 ∀ {l ♯a Δ Γ I} →
             G ↓ l ⇒ (code[ Δ ] Γ ∙ I) →
                  length Δ ≡ ♯a →
    ---------------------------------------------
    EvalGlobal G (globval l ♯a) (code[ Δ ] Γ ∙ I)

  instantiate-⟦⟧ :
           ∀ {w cᵥ ι Δ Δ' Γ Γ' I I'} →
         EvalGlobal G w (code[ Δ ] Γ ∙ I) →
               Run Δ ⟦ cᵥ / ι ⟧≡ Δ' →
                 Γ ⟦ Strong→Weak cᵥ / ι ⟧≡ Γ' →
                 I ⟦ Strong→Weak cᵥ / ι ⟧≡ I' →
    -----------------------------------------
    EvalGlobal G (w ⟦ cᵥ / ι ⟧) (code[ Δ' ] Γ' ∙ I')

infix 3 _⊢_⇒_
data _⊢_⇒_ (G : Globals) : ProgramState → ProgramState → Set where
    exec-add :
             ∀ {H sp regs I ♯rd ♯rs v n₁ n₂} →
          evalSmallValue regs v ≡ int n₁ →
                lookup ♯rs regs ≡ int n₂ →
      ---------------------------------------------------------
      G ⊢ H , register sp regs , add ♯rd ♯rs v ~> I ⇒
          H , register sp (update ♯rd (int (n₁ + n₂)) regs) , I

    exec-sub :
             ∀ {H sp regs I ♯rd ♯rs v n₁ n₂} →
          evalSmallValue regs v ≡ int n₁ →
                lookup ♯rs regs ≡ int n₂ →
      ---------------------------------------------------------
      G ⊢ H , register sp regs , sub ♯rd ♯rs v ~> I ⇒
          H , register sp (update ♯rd (int (n₁ ∸ n₂)) regs) , I

    exec-push :
                      ∀ {H sp regs I v} →
      ------------------------------------------------------
      G ⊢ H , register sp regs , push v ~> I ⇒
          H , register (evalSmallValue regs v ∷ sp) regs , I

    exec-pop :
                  ∀ {H w sp regs I} →
      -------------------------------------------
      G ⊢ H , register (w ∷ sp) regs , pop ~> I ⇒
          H , register sp regs , I

    exec-sld :
             ∀ {H sp regs I ♯rd i w} →
                    sp ↓ i ⇒ w →
      -------------------------------------------
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
      ----------------------------------------------
      G ⊢ H , register sp regs , ld ♯rd ♯rs i ~> I ⇒
          H , register sp (update ♯rd w regs) , I

    exec-st :
          ∀ {H H' sp regs I ♯rd i ♯rs lₕ ws ws'} →
             lookup ♯rd regs ≡ heapval lₕ →
                       H ↓ lₕ ⇒ tuple ws →
              ws ⟦ i ⟧← lookup ♯rs regs ⇒ ws' →
                    H ⟦ lₕ ⟧← tuple ws' ⇒ H' →
      -----------------------------------------------
      G ⊢ H  , register sp regs , st ♯rd i ♯rs ~> I ⇒
          H' , register sp regs , I

    exec-malloc :
                    ∀ {H sp regs I ♯rd τs} →
      ----------------------------------------------------------
      G ⊢ H , register sp regs , malloc ♯rd τs ~> I ⇒
          H ∷ʳ tuple (map uninit τs) ,
          register sp (update ♯rd (heapval (length H)) regs) , I

    exec-mov :
                       ∀ {H sp regs I ♯rd v} →
      -----------------------------------------------------------------
      G ⊢ H , register sp regs , mov ♯rd v ~> I ⇒
          H , register sp (update ♯rd (evalSmallValue regs v) regs) , I

    exec-beq₀ :
                    ∀ {H sp regs ♯r v Γ I₁ I₂} →
                     lookup ♯r regs ≡ int 0 →
      EvalGlobal G (evalSmallValue regs v) (code[ [] ] Γ ∙ I₂) →
      ----------------------------------------------------------
             G ⊢ H , register sp regs , beq ♯r v ~> I₁ ⇒
                 H , register sp regs , I₂

    exec-beq₁ :
                ∀ {H sp regs I ♯r v n₀} →
              lookup ♯r regs ≡ int n₀ →
                        n₀ ≢ 0 →
      ------------------------------------------
      G ⊢ H , register sp regs , beq ♯r v ~> I ⇒
          H , register sp regs , I

    exec-jmp :
                    ∀ {H sp regs v Γ I} →
      EvalGlobal G (evalSmallValue regs v) (code[ [] ] Γ ∙ I) →
      ---------------------------------------------------------
               G ⊢ H , register sp regs , jmp v ⇒
                   H , register sp regs , I

infix 3 _⊢_⇒ₙ_/_
infixr 5 _∷_
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
