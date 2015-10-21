open import Util
open import Grammar
open import Substitution
open import TypeJudgments
open import Subtyping

type-ctx-length : Type → Maybe ℕ
type-ctx-length (α⁼ ι) = nothing
type-ctx-length int = nothing
type-ctx-length ns = nothing
type-ctx-length (∀[ Δ ] Γ) = just (length Δ)
type-ctx-length (tuple τs) = nothing

mutual
  infix 4 ⊢_of_globals
  data ⊢_of_globals (G : Globals) (ψ₁ : GlobalLabelAssignment) : Set where
    of-globals :
      AllZip (λ g τ → ψ₁ ⊢ g of τ gval) G ψ₁ →
      ----------------------------------------
               ⊢ G of ψ₁ globals

  infix 4 _⊢_of_heap
  data _⊢_of_heap (ψ₁ : GlobalLabelAssignment) (H : Heap)
                  (ψ₂ : HeapLabelAssignment) : Set where
    of-heap :
      AllZip (λ h τ → (ψ₁ , ψ₂) ⊢ h of τ hval) H ψ₂ →
      -----------------------------------------------
                   ψ₁ ⊢ H of ψ₂ heap

  infix 4 _⊢_of_stack
  data _⊢_of_stack (ψ : LabelAssignment) : Stack → StackType → Set where
    of-[] : ψ ⊢ [] of nil stack

    of-∷ :
           ∀ {w S τ σ} →
        (ψ , []) ⊢ w of τ wval →
          ψ ⊢ S of σ stack →
      ------------------------
      ψ ⊢ w ∷ S of τ ∷ σ stack

  infix 4 _⊢_of_register
  data _⊢_of_register (ψ : LabelAssignment) : RegisterFile →
                                              RegisterAssignment → Set where
    of-register :
                     ∀ {sp regs σ τs} →
                     ψ ⊢ sp of σ stack →
      AllZipᵥ (λ w τ → (ψ , []) ⊢ w of τ wval) regs τs →
      --------------------------------------------------
       ψ ⊢ register sp regs of registerₐ σ τs register

  infix 4 _⊢_of_gval
  data _⊢_of_gval (ψ₁ : GlobalLabelAssignment) : GlobalValue →
                                                 Type → Set where
    of-gval :
                  ∀ {Δ Γ I} →
                 Δ ⊢ Γ Valid →
      (ψ₁ , Δ , Γ) ⊢ I instructionsequence →
      --------------------------------------
        ψ₁ ⊢ ∀[ Δ ] Γ ∙ I of ∀[ Δ ] Γ gval

  infix 4 _⊢_of_hval
  data _⊢_of_hval (ψ : LabelAssignment) : HeapValue → Type → Set where
    of-tuple :
                       ∀ {ws τs⁻} →
      AllZip (λ w τ⁻ → (ψ , []) ⊢ w of τ⁻ wval⁰) ws τs⁻ →
      ---------------------------------------------------
              ψ ⊢ tuple ws of tuple τs⁻ hval

  infix 4 _⊢_of_wval
  data _⊢_of_wval : LabelAssignment × TypeAssignment →
                    WordValue → Type → Set where
    of-globval :
              ∀ {ψ₁ ψ₂ Δ l ♯a τ₁ τ₂} →
                  ψ₁ ↓ l ⇒ τ₁ →
                 [] ⊢ τ₁ ≤ τ₂ →
           type-ctx-length τ₁ ≡ just ♯a →
      --------------------------------------
      ((ψ₁ , ψ₂) , Δ) ⊢ globval l ♯a of τ₂ wval

    of-heapval :
              ∀ {ψ₁ ψ₂ Δ lₕ τ₁ τ₂} →
                  ψ₂ ↓ lₕ ⇒ τ₁ →
                 Δ ⊢ τ₁ ≤ τ₂ →
      --------------------------------------
      ((ψ₁ , ψ₂) , Δ) ⊢ heapval lₕ of τ₂ wval

    of-const :
               ∀ {ψ Δ n} →
      -----------------------------
      (ψ , Δ) ⊢ const n of int wval

    of-ns :
             ∀ {ψ Δ} →
      -----------------------
      (ψ , Δ) ⊢ ns of ns wval

    of-inst :
           ∀ {ψ Δ Δ₁ Δ₂ Γ₁ Γ₂ w c} →
        (ψ , Δ₁) ⊢ w of ∀[ Δ₁ ] Γ₁ wval →
              Δ₁ ++ Δ ⊢ c Valid →
               Run Δ₁ ⟦ c ⟧≡ Δ₂ →
                Γ₁ ⟦ c ⟧≡ Γ₂ →
      ------------------------------------
      (ψ , Δ) ⊢ w ⟦ c ⟧ of ∀[ Δ₂ ] Γ₂ wval

  infix 4 _⊢_of_wval⁰
  data _⊢_of_wval⁰ (ψ : LabelAssignment × TypeAssignment) :
                     WordValue → InitType → Set where
    of-uninit :
                  ∀ {τ} →
      -------------------------------
      ψ ⊢ uninit τ of τ , false wval⁰

    of-init :
           ∀ {w τ φ} →
        ψ ⊢ w of τ wval →
      --------------------
      ψ ⊢ w of τ , φ wval⁰

  infix 4 _⊢_of_vval
  data _⊢_of_vval : LabelAssignment × TypeAssignment × RegisterAssignment →
                    SmallValue → Type → Set where
    of-reg :
                         ∀ {ψ Δ sp regs ♯r} →
      -----------------------------------------------------------
      (ψ , Δ , registerₐ sp regs) ⊢ reg ♯r of lookup ♯r regs vval

    of-word :
             ∀ {ψ Δ Γ w τ} →
          (ψ , Δ) ⊢ w of τ wval →
      ------------------------------
      (ψ , Δ , Γ) ⊢ word w of τ vval

    of-inst :
           ∀ {ψ Δ Γ Δ₁ Δ₂ Γ₁ Γ₂ v c} →
        (ψ , Δ₁ , Γ) ⊢ v of ∀[ Δ₁ ] Γ₁ vval →
              Δ₁ ++ Δ ⊢ c Valid →
               Run Δ₁ ⟦ c ⟧≡ Δ₂ →
                Γ₁ ⟦ c ⟧≡ Γ₂ →
      -----------------------------------------
      (ψ , Δ , Γ) ⊢ v ⟦ c ⟧ᵥ of ∀[ Δ₂ ] Γ₂ vval

  infix 4 _⊢_⇒_
  data _⊢_⇒_ : GlobalLabelAssignment × TypeAssignment × RegisterAssignment →
               Instruction → TypeAssignment × RegisterAssignment → Set where

  infix 4 _⊢_instructionsequence
  data _⊢_instructionsequence :
              GlobalLabelAssignment × TypeAssignment × RegisterAssignment →
              InstructionSequence → Set where

  infix 4 ⊢_program
  data ⊢_program : Program → Set where
