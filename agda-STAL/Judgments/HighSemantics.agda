module Judgments.HighSemantics where

open import Util
open import Judgments.Grammar
open import Judgments.Substitution
open HighGrammar

-- The purpose of this file is to define the
-- small-step semantics for our assembler language

evalSmallValueₕ : Vec WordValue ♯regs → SmallValue → WordValue
evalSmallValueₕ regs (reg ♯r) = lookup ♯r regs
evalSmallValueₕ regs (globval lab) = globval lab
evalSmallValueₕ regs (int i) = int i
evalSmallValueₕ regs Λ Δ ∙ v ⟦ is ⟧ = Λ Δ ∙ evalSmallValueₕ regs v ⟦ is ⟧

data InstantiateGlobalₕ (G : Globals) : WordValue → InstructionSequence → Set where
  instantiate-globval :
              ∀ {lab Δ Γ I} →
        G ↓ lab ⇒ (code[ Δ ] Γ ∙ I) →
    -----------------------------------
    InstantiateGlobalₕ G (globval lab) I

  instantiate-Λ :
               ∀ {w I I' Δ is} →
            InstantiateGlobalₕ G w I →
              I ⟦ is / 0 ⟧many≡ I' →
    ---------------------------------------
    InstantiateGlobalₕ G (Λ Δ ∙ w ⟦ is ⟧) I'

infix 3 _⊢ₕ_⇒_
data _⊢ₕ_⇒_ (G : Globals) : ProgramState → ProgramState → Set where
    step-add :
             ∀ {H sp regs I ♯rd ♯rs v n₁ n₂} →
          evalSmallValueₕ regs v ≡ int n₁ →
                lookup ♯rs regs ≡ int n₂ →
      ----------------------------------------------------------
      G ⊢ₕ H , register sp regs , add ♯rd ♯rs v ~> I ⇒
           H , register sp (update ♯rd (int (n₁ + n₂)) regs) , I

    step-sub :
             ∀ {H sp regs I ♯rd ♯rs v n₁ n₂} →
          evalSmallValueₕ regs v ≡ int n₁ →
                lookup ♯rs regs ≡ int n₂ →
      ----------------------------------------------------------
      G ⊢ₕ H , register sp regs , sub ♯rd ♯rs v ~> I ⇒
           H , register sp (update ♯rd (int (n₁ ∸ n₂)) regs) , I

    step-salloc :
                      ∀ {H sp regs I n} →
      -------------------------------------------------
      G ⊢ₕ H , register sp regs , salloc n ~> I ⇒
           H , register (replicate n ns ++ sp) regs , I

    step-sfree :
                  ∀ {H sp sp' regs I n} →
                     Drop n sp sp' →
      ------------------------------------------
      G ⊢ₕ H , register sp regs , sfree n ~> I ⇒
           H , register sp' regs , I

    step-sld :
             ∀ {H sp regs I ♯rd i w} →
                    sp ↓ i ⇒ w →
      --------------------------------------------
      G ⊢ₕ H , register sp regs , sld ♯rd i ~> I ⇒
           H , register sp (update ♯rd w regs) , I

    step-sst :
             ∀ {H sp sp' regs I ♯rs i} →
           sp ⟦ i ⟧← lookup ♯rs regs ⇒ sp' →
      --------------------------------------------
      G ⊢ₕ H , register sp  regs , sst i ♯rs ~> I ⇒
           H , register sp' regs , I

    step-ld :
          ∀ {H sp regs I ♯rd ♯rs i lₕ ws w} →
             lookup ♯rs regs ≡ heapval lₕ →
                     H ↓ lₕ ⇒ tuple ws →
                     ws ↓ i ⇒ w →
      -----------------------------------------------
      G ⊢ₕ H , register sp regs , ld ♯rd ♯rs i ~> I ⇒
           H , register sp (update ♯rd w regs) , I

    step-st :
          ∀ {H H' sp regs I ♯rd i ♯rs lₕ ws ws'} →
             lookup ♯rd regs ≡ heapval lₕ →
                       H ↓ lₕ ⇒ tuple ws →
              ws ⟦ i ⟧← lookup ♯rs regs ⇒ ws' →
                    H ⟦ lₕ ⟧← tuple ws' ⇒ H' →
      ------------------------------------------------
      G ⊢ₕ H  , register sp regs , st ♯rd i ♯rs ~> I ⇒
           H' , register sp regs , I

    step-malloc :
                    ∀ {H sp regs I ♯rd τs} →
      -----------------------------------------------------------
      G ⊢ₕ H , register sp regs , malloc ♯rd τs ~> I ⇒
           H ∷ʳ tuple (map uninit τs) ,
           register sp (update ♯rd (heapval (length H)) regs) , I

    step-mov :
                       ∀ {H sp regs I ♯rd v} →
      -------------------------------------------------------------------
      G ⊢ₕ H , register sp regs , mov ♯rd v ~> I ⇒
           H , register sp (update ♯rd (evalSmallValueₕ regs v) regs) , I

    step-beq₀ :
                  ∀ {H sp regs ♯r v I₁ I₂} →
                   lookup ♯r regs ≡ int 0 →
      InstantiateGlobalₕ G (evalSmallValueₕ regs v) I₂ →
      --------------------------------------------------
         G ⊢ₕ H , register sp regs , beq ♯r v ~> I₁ ⇒
              H , register sp regs , I₂

    step-beq₁ :
                ∀ {H sp regs I ♯r v n₀} →
              lookup ♯r regs ≡ int n₀ →
                        n₀ ≢ 0 →
      -------------------------------------------
      G ⊢ₕ H , register sp regs , beq ♯r v ~> I ⇒
           H , register sp regs , I

    step-jmp :
                    ∀ {H sp regs v I} →
      InstantiateGlobalₕ G (evalSmallValueₕ regs v) I →
      -------------------------------------------------
         G ⊢ₕ H , register sp regs , jmp v ⇒
              H , register sp regs , I

infix 3 ⊢ₕ_⇒_
data ⊢ₕ_⇒_ : Program → Program → Set where
  step-running :
          ∀ {G P P'} →
          G ⊢ₕ P ⇒ P' →
    -------------------------
    ⊢ₕ running G P ⇒ running G P'

  step-halting :
               ∀ {G H R} →
    ----------------------------------
    ⊢ₕ running G (H , R , halt) ⇒ halted

  step-halted :
    ------------------
    ⊢ₕ halted ⇒ halted

infix 3 ⊢ₕ_⇒ₙ_/_
infixr 5 _∷_
data ⊢ₕ_⇒ₙ_/_ : Program → ℕ → Program → Set where
  []  :
       ∀ {P} →
    -------------
    ⊢ₕ P ⇒ₙ 0 / P

  _∷_ :
       ∀ {P₁ P₂ P₃ n} →
          ⊢ₕ P₁ ⇒ P₂ →
       ⊢ₕ P₂ ⇒ₙ n / P₃ →
      -------------------
      ⊢ₕ P₁ ⇒ₙ suc n / P₃
