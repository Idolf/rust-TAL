module TermJudgments where

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

lookup-regs : Register → RegisterAssignment → Type
lookup-regs ♯r (registerₐ sp regs) = lookup ♯r regs

update-regs : Register → Type → RegisterAssignment → RegisterAssignment
update-regs ♯r τ (registerₐ sp regs) = registerₐ sp (update ♯r τ regs)

data stack-lookup : ℕ → StackType → Type → Set where
  here :
            ∀ {τ σ} →
    ---------------------------
    stack-lookup zero (τ ∷ σ) τ

  there :
            ∀ {i σ τ₁ τ₂} →
          stack-lookup i σ τ₁ →
    --------------------------------
    stack-lookup (suc i) (τ₂ ∷ σ) τ₁

data stack-update : ℕ → Type → StackType → StackType → Set where
  here :
                ∀ {τ₁ τ₂ σ} →
    --------------------------------------
    stack-update zero τ₁ (τ₂ ∷ σ) (τ₁ ∷ σ)

  there :
               ∀ {i τ₁ τ₂ σ₁ σ₂} →
            stack-update i τ₁ σ₁ σ₂ →
    -------------------------------------------
    stack-update (suc i) τ₁ (τ₂ ∷ σ₁) (τ₂ ∷ σ₂)

register-stack-lookup : ℕ → RegisterAssignment → Type → Set
register-stack-lookup n (registerₐ sp regs) τ = stack-lookup n sp τ

register-stack-update : ℕ → Type → RegisterAssignment →
                        RegisterAssignment → Set
register-stack-update n τ (registerₐ sp regs) (registerₐ sp' regs')
  = stack-update n τ sp sp' × regs ≡ regs'

stack-lookup-dec : ∀ i σ → Dec (∃ λ τ → stack-lookup i σ τ)
stack-lookup-dec i (ρ⁼ ι) = no (λ { (_ , ()) })
stack-lookup-dec i nil = no (λ { (_ , ()) })
stack-lookup-dec zero (τ ∷ σ) = yes (τ , here)
stack-lookup-dec (suc i) (τ ∷ σ) with stack-lookup-dec i σ
... | yes (τ' , l) = yes (τ' , there l)
... | no ¬l = no (λ { (τ' , there l) → ¬l (τ' , l)})

stack-lookup-unique : ∀ {i σ τ₁ τ₂} →
                        stack-lookup i σ τ₁ →
                        stack-lookup i σ τ₂ →
                        τ₁ ≡ τ₂
stack-lookup-unique here here = refl
stack-lookup-unique (there l₁) (there l₂) = stack-lookup-unique l₁ l₂

stack-update-dec : ∀ i τ σ → Dec (∃ λ σ' → stack-update i τ σ σ')
stack-update-dec i τ (ρ⁼ ι) = no (λ { (_ , ()) })
stack-update-dec i τ nil = no (λ { (_ , ()) })
stack-update-dec zero τ (τ' ∷ σ) = yes (τ ∷ σ , here)
stack-update-dec (suc i) τ (τ' ∷ σ) with stack-update-dec i τ σ
... | yes (σ' , up) = yes (τ' ∷ σ' , there up)
... | no ¬up = no (λ { (.τ' ∷ σ' , there up) → ¬up (σ' , up)})

stack-update-unique : ∀ {i τ σ σ₁ σ₂} →
                        stack-update i τ σ σ₁ →
                        stack-update i τ σ σ₂ →
                        σ₁ ≡ σ₂
stack-update-unique here here = refl
stack-update-unique (there up₁) (there up₂)
  rewrite stack-update-unique up₁ up₂ = refl

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
  data _⊢_of_stack : GlobalLabelAssignment × HeapLabelAssignment →
                     Stack → StackType → Set where
    of-[] :
              ∀ {ψ₁ ψ₂} →
      -------------------------
      ψ₁ , ψ₂ ⊢ [] of nil stack

    of-∷ :
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
      ------------------------------------------------
       ψ₁ , ψ₂ ⊢ register sp regs of registerₐ σ τs register

  infix 3 _⊢_of_gval
  data _⊢_of_gval (ψ₁ : GlobalLabelAssignment) : GlobalValue →
                                                 Type → Set where
    of-gval :
                 ∀ {Δ Γ I} →
                Δ ⊢ Γ Valid →
      ψ₁ , Δ , Γ ⊢ I instructionsequence →
      ------------------------------------
       ψ₁ ⊢ ∀[ Δ ] Γ ∙ I of ∀[ Δ ] Γ gval

  infix 3 _⊢_of_hval
  data _⊢_of_hval : GlobalLabelAssignment × HeapLabelAssignment →
                    HeapValue → Type → Set where
    of-tuple :
                       ∀ {ψ₁ ψ₂ ws τs⁻} →
      AllZip (λ w τ⁻ → ψ₁ , ψ₂ , [] ⊢ w of τ⁻ wval⁰) ws τs⁻ →
      -------------------------------------------------
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
               Δ ⊢ τ₁ ≤ τ₂ →
      -----------------------------------
      ψ₁ , ψ₂ , Δ ⊢ heapval lₕ of τ₂ wval

    of-const :
              ∀ {ψ₁ ψ₂ Δ n} →
      --------------------------------
      ψ₁ , ψ₂ , Δ ⊢ const n of int wval

    of-ns :
            ∀ {ψ₁ ψ₂ Δ} →
      ---------------------------
      ψ₁ , ψ₂ , Δ ⊢ ns of ns wval

    of-inst :
        ∀ {ψ₁ ψ₂ Δ Δ₁ Δ₂ Γ₁ Γ₂ w c} →
       ψ₁ , ψ₂ , Δ ⊢ w of ∀[ Δ₁ ] Γ₁ wval →
            Δ₁ ++ Δ ⊢ c Valid →
             Run Δ₁ ⟦ c ⟧≡ Δ₂ →
              Γ₁ ⟦ c ⟧≡ Γ₂ →
      ----------------------------------------
      ψ₁ , ψ₂ , Δ ⊢ w ⟦ c ⟧ of ∀[ Δ₂ ] Γ₂ wval

  infix 3 _⊢_of_wval⁰
  data _⊢_of_wval⁰ : GlobalLabelAssignment × HeapLabelAssignment ×
                     TypeAssignment → WordValue → InitType → Set where
    of-uninit :
                 ∀ {ψ₁ ψ₂ Γ τ} →
      -----------------------------------
      ψ₁ , ψ₂ , Γ ⊢ uninit τ of τ , false wval⁰

    of-init :
          ∀ {ψ₁ ψ₂ Γ w τ φ} →
        ψ₁ , ψ₂ , Γ ⊢ w of τ wval →
      ------------------------
      ψ₁ , ψ₂ , Γ ⊢ w of τ , φ wval⁰

  infix 3 _⊢_of_vval
  data _⊢_of_vval : GlobalLabelAssignment × HeapLabelAssignment ×
                    TypeAssignment × RegisterAssignment →
                    SmallValue → Type → Set where
    of-reg :
                    ∀ {ψ₁ ψ₂ Δ Γ ♯r} →
      -------------------------------------------
      ψ₁ , ψ₂ , Δ , Γ ⊢ reg ♯r of lookup-regs ♯r Γ vval

    of-word :
             ∀ {ψ₁ ψ₂ Δ Γ w τ} →
          ψ₁ , ψ₂ , Δ ⊢ w of τ wval →
      ----------------------------
      ψ₁ , ψ₂ , Δ , Γ ⊢ word w of τ vval

    of-inst :
          ∀ {ψ₁ ψ₂ Δ Γ Δ₁ Δ₂ Γ₁ Γ₂ v c} →
       ψ₁ , ψ₂ , Δ , Γ ⊢ v of ∀[ Δ₁ ] Γ₁ vval →
              Δ₁ ++ Δ ⊢ c Valid →
               Run Δ₁ ⟦ c ⟧≡ Δ₂ →
                Γ₁ ⟦ c ⟧≡ Γ₂ →
      ---------------------------------------
      ψ₁ , ψ₂ , Δ , Γ ⊢ v ⟦ c ⟧ᵥ of ∀[ Δ₂ ] Γ₂ vval

  infix 3 _⊢_⇒_
  data _⊢_⇒_ : GlobalLabelAssignment × TypeAssignment ×
               RegisterAssignment →
               Instruction → RegisterAssignment → Set where
    of-add :
                    ∀ {ψ₁ Δ Γ ♯rd ♯rs v} →
                  lookup-regs ♯rs Γ  ≡ int →
             ψ₁ , [] , Δ , Γ ⊢ v of int vval →
      --------------------------------------------------
      ψ₁ , Δ , Γ ⊢ add ♯rd ♯rs v ⇒ update-regs ♯rd int Γ

    of-sub :
                      ∀ {ψ₁ Δ Γ ♯rd ♯rs v} →
                    lookup-regs ♯rs Γ  ≡ int →
               ψ₁ , [] , Δ , Γ ⊢ v of int vval →
      --------------------------------------------------
      ψ₁ , Δ , Γ ⊢ sub ♯rd ♯rs v ⇒ update-regs ♯rd int Γ

    of-sld :
                 ∀ {ψ₁ Δ Γ ♯rd i τ} →
             register-stack-lookup i Γ τ →
      --------------------------------------------
      ψ₁ , Δ , Γ ⊢ sld ♯rd i ⇒ update-regs ♯rd τ Γ

    of-sst :
           ∀ {ψ₁ Δ Γ i ♯rs τ Γ'} →
         lookup-regs ♯rs Γ ≡ τ →
      register-stack-update i τ Γ Γ' →
      --------------------------------
        ψ₁ , Δ , Γ ⊢ sst i ♯rs ⇒ Γ'

    of-ld :
               ∀ {ψ₁ Δ Γ ♯rd ♯rs i τs⁻ τ} →
              lookup-regs ♯rs Γ ≡ tuple τs⁻ →
                    τs⁻ ↓ i ⇒ τ , true →
      -----------------------------------------------
      ψ₁ , Δ , Γ ⊢ ld ♯rd ♯rs i ⇒ update-regs ♯rd τ Γ

    of-st :
                 ∀ {ψ₁ Δ Γ ♯rd i ♯rs τ τs⁻ τs⁻'} →
                      lookup-regs ♯rs Γ ≡ τ →
                  lookup-regs ♯rd Γ ≡ tuple τs⁻ →
                    τs⁻ ⟦ i ⟧← τ , true ⇒ τs⁻' →
      ----------------------------------------------------------
      ψ₁ , Δ , Γ ⊢ st ♯rd i ♯rs ⇒ update-regs ♯rd (tuple τs⁻') Γ

    of-malloc :
                      ∀ {ψ₁ Δ Γ ♯rd τs} →
      ------------------------------------------------------
      ψ₁ , Δ , Γ ⊢ malloc ♯rd τs ⇒
        update-regs ♯rd (tuple (map (λ τ → τ , false) τs)) Γ

    of-mov :
               ∀ {ψ₁ Δ Γ ♯rd v τ} →
          ψ₁ , [] , Δ , Γ ⊢ v of τ vval →
      --------------------------------------------
      ψ₁ , Δ , Γ ⊢ mov ♯rd v ⇒ update-regs ♯rd τ Γ

    of-beq :
                 ∀ {ψ₁ Δ Γ ♯r v Γ'} →
               lookup-regs ♯r Γ ≡ int →
                     Δ ⊢ Γ ≤ Γ' →
        ψ₁ , [] , Δ , Γ ⊢ v of ∀[ [] ] Γ' vval →
        ------------------------------------------
              ψ₁ , Δ , Γ ⊢ beq ♯r v ⇒ Γ

  infix 3 _⊢_instructionsequence
  data _⊢_instructionsequence : GlobalLabelAssignment ×
                                TypeAssignment ×
                                RegisterAssignment →
                                InstructionSequence → Set where
    of-~> :
               ∀ {ψ₁ Δ Γ Γ' ι I} →
             ψ₁ , Δ , Γ ⊢ ι ⇒ Γ' →
      ψ₁ , Δ , Γ' ⊢ I instructionsequence →
      ---------------------------------------
      ψ₁ , Δ , Γ ⊢ ι ~> I instructionsequence

    of-jmp :
                 ∀ {ψ₁ Δ Γ Γ' v} →
                    Δ ⊢ Γ ≤ Γ' →
      ψ₁ , [] , Δ , Γ ⊢ v of ∀[ [] ] Γ' vval →
      -------------------------------------------
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
