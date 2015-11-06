module Judgments.Terms where

open import Util
open import Judgments.Grammar
open import Judgments.Types
open import Judgments.Subtypes
open import Judgments.Substitution
open import Judgments.Run
open import Judgments.StackLookup

-- The purpose of this file is to include
-- judgments to show if a term is valid.

type-ctx-length : Type → Maybe ℕ
type-ctx-length (α⁼ ι) = nothing
type-ctx-length int = nothing
type-ctx-length ns = nothing
type-ctx-length (∀[ Δ ] Γ) = just (length Δ)
type-ctx-length (tuple τs) = nothing

lookup-regs : Register → RegisterAssignment → Type
lookup-regs ♯r (registerₐ sp regs) = lookup ♯r regs

update-regs : Register → Type → RegisterAssignment → RegisterAssignment
update-regs ♯r τ (registerₐ sp regs) = registerₐ sp (update ♯r τ regs)

mutual
  infix 3 ⊢_of_globals
  data ⊢_of_globals (G : Globals) (ψ₁ : GlobalLabelAssignment) : Set where
    of-globals :
      AllZip (λ g τ → ψ₁ ⊢ g of τ gval) G ψ₁ →
      ----------------------------------------
               ⊢ G of ψ₁ globals

  infix 3 _⊢_of_heap
  data _⊢_of_heap (ψ₁ : GlobalLabelAssignment) (H : Heap)
                  (ψ₂ : HeapLabelAssignment) : Set where
    of-heap :
      AllZip (λ h τ → ψ₁ , ψ₂ ⊢ h of τ hval) H ψ₂ →
      ---------------------------------------------
                  ψ₁ ⊢ H of ψ₂ heap

  infix 3 _⊢_of_stack
  infixr 5 _∷_
  data _⊢_of_stack : GlobalLabelAssignment × HeapLabelAssignment →
                     Stack → StackType → Set where
    [] :
              ∀ {ψ₁ ψ₂} →
      -------------------------
      ψ₁ , ψ₂ ⊢ [] of [] stack

    _∷_ :
           ∀ {ψ₁ ψ₂ w S τ σ} →
        ψ₁ , ψ₂ , [] ⊢ w of τ wval →
          ψ₁ , ψ₂ ⊢ S of σ stack →
      ------------------------
      ψ₁ , ψ₂ ⊢ w ∷ S of τ ∷ σ stack

  infix 3 _⊢_of_register
  data _⊢_of_register : GlobalLabelAssignment ×
                        HeapLabelAssignment →
                        RegisterFile → RegisterAssignment → Set where
    of-register :
                     ∀ {ψ₁ ψ₂ sp regs σ τs} →
                     ψ₁ , ψ₂ ⊢ sp of σ stack →
      AllZipᵥ (λ w τ → ψ₁ , ψ₂ , [] ⊢ w of τ wval) regs τs →
      ------------------------------------------------------
       ψ₁ , ψ₂ ⊢ register sp regs of registerₐ σ τs register

  infix 3 _⊢_of_gval
  data _⊢_of_gval (ψ₁ : GlobalLabelAssignment) : GlobalValue →
                                                 Type → Set where
    of-gval :
                 ∀ {Δ Γ I} →
                [] ⊢ Δ Valid →
                Δ ⊢ Γ Valid →
      ψ₁ , Δ , Γ ⊢ I instructionsequence →
      -------------------------------------
      ψ₁ ⊢ code[ Δ ] Γ ∙ I of ∀[ Δ ] Γ gval

  infix 3 _⊢_of_hval
  data _⊢_of_hval : GlobalLabelAssignment × HeapLabelAssignment →
                    HeapValue → Type → Set where
    of-tuple :
                       ∀ {ψ₁ ψ₂ ws τs⁻} →
      AllZip (λ w τ⁻ → ψ₁ , ψ₂ , [] ⊢ w of τ⁻ wval⁰) ws τs⁻ →
      -------------------------------------------------------
             ψ₁ , ψ₂ ⊢ tuple ws of tuple τs⁻ hval

  infix 3 _⊢_of_wval
  data _⊢_of_wval : GlobalLabelAssignment × HeapLabelAssignment ×
                    TypeAssignment →
                    WordValue → Type → Set where
    of-globval :
          ∀ {ψ₁ ψ₂ Δ l ♯a τ₁ τ₂} →
                ψ₁ ↓ l ⇒ τ₁ →
               [] ⊢ τ₁ ≤ τ₂ →
         type-ctx-length τ₁ ≡ just ♯a →
      -------------------------------------
      ψ₁ , ψ₂ , Δ ⊢ globval l ♯a of τ₂ wval

    of-heapval :
           ∀ {ψ₁ ψ₂ Δ lₕ τ₁ τ₂} →
               ψ₂ ↓ lₕ ⇒ τ₁ →
               [] ⊢ τ₁ ≤ τ₂ →
      -----------------------------------
      ψ₁ , ψ₂ , Δ ⊢ heapval lₕ of τ₂ wval

    of-int :
              ∀ {ψ₁ ψ₂ Δ n} →
      --------------------------------
      ψ₁ , ψ₂ , Δ ⊢ int n of int wval

    of-ns :
            ∀ {ψ₁ ψ₂ Δ} →
      ---------------------------
      ψ₁ , ψ₂ , Δ ⊢ ns of ns wval

    of-inst :
          ∀ {ψ₁ ψ₂ Δ Δ₁ Δ₂ Γ₁ Γ₂ Γ₃ w cᵥ ι} →
          ψ₁ , ψ₂ , Δ ⊢ w of ∀[ Δ₁ ] Γ₁ wval →
               Δ₁ ++ Δ ⊢ cᵥ / ι Valid →
                Run Δ₁ ⟦ cᵥ / ι ⟧≡ Δ₂ →
            Γ₁ ⟦ Strong→Weak cᵥ / ι ⟧≡ Γ₂ →
                 Δ₂ ++ Δ ⊢ Γ₂ ≤ Γ₃ →
      ---------------------------------------------
      ψ₁ , ψ₂ , Δ ⊢ w ⟦ cᵥ / ι ⟧ of ∀[ Δ₂ ] Γ₃ wval

  infix 3 _⊢_of_wval⁰
  data _⊢_of_wval⁰ : GlobalLabelAssignment × HeapLabelAssignment ×
                     TypeAssignment → WordValue → InitType → Set where
    of-uninit :
                 ∀ {ψ₁ ψ₂ Δ τ} →
                 [] ⊢ τ Valid →
      ------------------------------------------
      ψ₁ , ψ₂ , Δ ⊢ uninit τ of τ , uninit wval⁰

    of-init :
          ∀ {ψ₁ ψ₂ Δ w τ φ} →
        ψ₁ , ψ₂ , Δ ⊢ w of τ wval →
      ------------------------------
      ψ₁ , ψ₂ , Δ ⊢ w of τ , φ wval⁰

  infix 3 _⊢_of_vval
  data _⊢_of_vval : GlobalLabelAssignment ×
                    TypeAssignment × RegisterAssignment →
                    SmallValue → Type → Set where
    of-reg :
             ∀ {ψ₁ Δ Γ ♯r τ} →
       Δ ⊢ lookup-regs ♯r Γ ≤ τ →
      -----------------------------
      ψ₁ , Δ , Γ ⊢ reg ♯r of τ vval

    of-word :
           ∀ {ψ₁ Δ Γ w τ} →
       ψ₁ , [] , Δ ⊢ w of τ wval →
      -----------------------------
      ψ₁ , Δ , Γ ⊢ word w of τ vval

    of-inst :
          ∀ {ψ₁ Δ Γ Δ₁ Δ₂ Γ₁ Γ₂ Γ₃ v cᵥ ι} →
         ψ₁ , Δ , Γ ⊢ v of ∀[ Δ₁ ] Γ₁ vval →
              Δ₁ ++ Δ ⊢ cᵥ / ι Valid →
               Run Δ₁ ⟦ cᵥ / ι ⟧≡ Δ₂ →
           Γ₁ ⟦ Strong→Weak cᵥ / ι ⟧≡ Γ₂ →
                Δ₂ ++ Δ ⊢ Γ₂ ≤ Γ₃ →
      --------------------------------------------
      ψ₁ , Δ , Γ ⊢ v ⟦ cᵥ / ι ⟧ of ∀[ Δ₂ ] Γ₃ vval

  infix 3 _⊢_⇒_instruction
  data _⊢_⇒_instruction : GlobalLabelAssignment × TypeAssignment ×
                          RegisterAssignment →
                          Instruction → RegisterAssignment → Set where
    of-add :
                     ∀ {ψ₁ Δ Γ ♯rd ♯rs v} →
                    lookup-regs ♯rs Γ ≡ int →
                   ψ₁ , Δ , Γ ⊢ v of int vval →
      --------------------------------------------------------------
      ψ₁ , Δ , Γ ⊢ add ♯rd ♯rs v ⇒ update-regs ♯rd int Γ instruction

    of-sub :
                       ∀ {ψ₁ Δ Γ ♯rd ♯rs v} →
                     lookup-regs ♯rs Γ  ≡ int →
                    ψ₁ , Δ , Γ ⊢ v of int vval →
      --------------------------------------------------------------
      ψ₁ , Δ , Γ ⊢ sub ♯rd ♯rs v ⇒ update-regs ♯rd int Γ instruction

    of-push :
                ∀ {ψ₁ Δ sp regs v τ} →
       ψ₁ , Δ , registerₐ sp regs ⊢ v of τ vval →
      --------------------------------------------
      ψ₁ , Δ , registerₐ sp regs ⊢ push v ⇒
               registerₐ (τ ∷ sp) regs instruction

    of-pop :
                               ∀ {ψ₁ Δ τ sp regs} →
      ----------------------------------------------------------------------
      ψ₁ , Δ , registerₐ (τ ∷ sp) regs ⊢ pop ⇒ registerₐ sp regs instruction

    of-sld :
                      ∀ {ψ₁ Δ Γ ♯rd i τ} →
                  register-stack-lookup i Γ τ →
      --------------------------------------------------------
      ψ₁ , Δ , Γ ⊢ sld ♯rd i ⇒ update-regs ♯rd τ Γ instruction

    of-sst :
                      ∀ {ψ₁ Δ sp sp' regs i ♯rs} →
                    stack-update i (lookup ♯rs regs) sp sp' →
      -----------------------------------------------------------------------
      ψ₁ , Δ , registerₐ sp regs ⊢ sst i ♯rs ⇒ registerₐ sp' regs instruction

    of-ld :
                    ∀ {ψ₁ Δ Γ ♯rd ♯rs i τs⁻ τ} →
                   lookup-regs ♯rs Γ ≡ tuple τs⁻ →
                        τs⁻ ↓ i ⇒ τ , init →
      -----------------------------------------------------------
      ψ₁ , Δ , Γ ⊢ ld ♯rd ♯rs i ⇒ update-regs ♯rd τ Γ instruction

    of-st :
                   ∀ {ψ₁ Δ Γ ♯rd i ♯rs τs⁻ τs⁻' τ φ} →
                     lookup-regs ♯rd Γ ≡ tuple τs⁻ →
                       Δ ⊢ lookup-regs ♯rs Γ ≤ τ →
                            τs⁻ ↓ i ⇒ τ , φ →
                        τs⁻ ⟦ i ⟧← τ , init ⇒ τs⁻' →
      ----------------------------------------------------------------------
      ψ₁ , Δ , Γ ⊢ st ♯rd i ♯rs ⇒ update-regs ♯rd (tuple τs⁻') Γ instruction

    of-malloc :
                      ∀ {ψ₁ Δ Γ ♯rd τs} →
                        Δ ⊢ τs Valid →
      -------------------------------------------------------------------
      ψ₁ , Δ , Γ ⊢ malloc ♯rd τs ⇒
        update-regs ♯rd (tuple (map (λ τ → τ , uninit) τs)) Γ instruction

    of-mov :
                      ∀ {ψ₁ Δ Γ ♯rd v τ} →
                    ψ₁ , Δ , Γ ⊢ v of τ vval →
      --------------------------------------------------------
      ψ₁ , Δ , Γ ⊢ mov ♯rd v ⇒ update-regs ♯rd τ Γ instruction

    of-beq :
             ∀ {ψ₁ Δ ♯r v Γ Γ'} →
           lookup-regs ♯r Γ ≡ int →
                 Δ ⊢ Γ ≤ Γ' →
      ψ₁ , Δ , Γ ⊢ v of ∀[ [] ] Γ' vval →
      -------------------------------------
      ψ₁ , Δ , Γ ⊢ beq ♯r v ⇒ Γ instruction

  infix 3 _⊢_instructionsequence
  data _⊢_instructionsequence : GlobalLabelAssignment ×
                                TypeAssignment ×
                                RegisterAssignment →
                                InstructionSequence → Set where
    of-~> :
            ∀ {ψ₁ Δ Γ Γ' ι I} →
      ψ₁ , Δ , Γ  ⊢ ι ⇒ Γ' instruction →
      ψ₁ , Δ , Γ' ⊢ I instructionsequence →
      ---------------------------------------
      ψ₁ , Δ , Γ ⊢ ι ~> I instructionsequence

    of-jmp :
              ∀ {ψ₁ Δ Γ Γ' v} →
                 Δ ⊢ Γ ≤ Γ' →
       ψ₁ , Δ , Γ ⊢ v of ∀[ [] ] Γ' vval →
      --------------------------------------
      ψ₁ , Δ , Γ ⊢ jmp v instructionsequence

  infix 3 _⊢_program
  data _⊢_program : Globals → ProgramState → Set where
    of-program :
              ∀ {ψ₁ ψ₂ Γ G H R I} →
               ⊢ G of ψ₁ globals →
               ψ₁ ⊢ H of ψ₂ heap →
           ψ₁ , ψ₂ ⊢ R of Γ register →
      ψ₁ , [] , Γ ⊢ I instructionsequence →
      -------------------------------------
             G ⊢ H , R , I program
