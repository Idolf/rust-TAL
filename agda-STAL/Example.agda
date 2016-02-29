open import Util
open import Judgments
open import Lemmas
open HighSyntax
open HighSemantics

infloop : GlobalValue
infloop =
  code[ α ∷ α ∷ α ∷ α ∷ ρ ∷ [] ]
  registerₐ (ρ⁼ 4) (α⁼ 0 ∷ α⁼ 1 ∷ α⁼ 2 ∷ α⁼ 3 ∷ []) ∙
    jmp Λ [] ∙ globval 0 ⟦ α (α⁼ 4) ∷ α (α⁼ 4) ∷ α (α⁼ 4) ∷ α (α⁼ 4) ∷ ρ (ρ⁼ 4) ∷ [] ⟧

addloop =
  code[ α ∷ α ∷ α ∷ ρ ∷ [] ]
  registerₐ (ρ⁼ 3) (int ∷ α⁼ 0 ∷ α⁼ 1 ∷ α⁼ 2 ∷ []) ∙
    add (# 0) (# 0) (int 1) ~>
    jmp Λ [] ∙ globval 1 ⟦ α (α⁼ 3) ∷ α (α⁼ 3) ∷ α (α⁼ 3) ∷ ρ (ρ⁼ 3) ∷ [] ⟧

fiboloop =
  code[ α ∷ α ∷ ρ ∷ [] ]
  registerₐ (ρ⁼ 2) (int ∷ int ∷ α⁼ 0 ∷ α⁼ 1 ∷ []) ∙
     salloc 1 ~>
     sst 0 (# 0) ~>
     add (# 0) (# 0) (reg (# 1)) ~>
     sld (# 1) 0 ~>
     sfree 1 ~>
     jmp Λ [] ∙ globval 2 ⟦ α (α⁼ 2) ∷ α (α⁼ 2) ∷ ρ (ρ⁼ 2) ∷ [] ⟧

badloop =
  code[ α ∷ [] ]
  registerₐ [] (int ∷ int ∷ int ∷ int ∷ []) ∙
    jmp Λ [] ∙ globval 3 ⟦ α (tuple ((α⁼ 0 , uninit) ∷ (α⁼ 0 , uninit) ∷ [])) ∷ [] ⟧

condjmp =
  code[ α ∷ ρ ∷ [] ]
  registerₐ (ρ⁼ 1) (int ∷
                    (∀[ α ∷ [] ] (registerₐ (ρ⁼ 2) (int ∷ α⁼ 0 ∷ α⁼ 0 ∷ α⁼ 1 ∷ []))) ∷
                    (∀[ α ∷ [] ] (registerₐ (ρ⁼ 2) (int ∷ α⁼ 0 ∷ α⁼ 0 ∷ α⁼ 1 ∷ []))) ∷
                    α⁼ 0 ∷ []) ∙
    beq (# 0) (Λ [] ∙ reg (# 1) ⟦ α (∀[ α ∷ [] ] (registerₐ (ρ⁼ 2) (int ∷ α⁼ 0 ∷ α⁼ 0 ∷ α⁼ 1 ∷ []))) ∷ [] ⟧) ~>
    jmp       (Λ [] ∙ reg (# 2) ⟦ α (∀[ α ∷ [] ] (registerₐ (ρ⁼ 2) (int ∷ α⁼ 0 ∷ α⁼ 0 ∷ α⁼ 1 ∷ []))) ∷ [] ⟧)

myglobals : Globals
myglobals = infloop ∷ addloop ∷ fiboloop ∷ badloop ∷ condjmp ∷ []

myheap : Heap
myheap = []

myregister : ℕ → ℕ → RegisterFile
myregister a b = register [] (int a ∷ int b ∷ int 2 ∷ int 3 ∷ [])

-- Use the infloop function
mystart : InstructionSequence
mystart =
  jmp Λ [] ∙ globval 0 ⟦ α int ∷ α int ∷ α int ∷ α int ∷ ρ [] ∷ [] ⟧

myprogram : ProgramState
myprogram = myglobals , myheap , myregister 0 0 , mystart

myprogram-valid : ⊢ myprogram programstate
myprogram-valid = dec-force (programstate-dec _)

myprogram-step : ⊢ myprogram ⇒ myprogram
myprogram-step = dec-force (step-prg-dec-specificₕ _ _)

-- Use the addloop function
mystart2 : InstructionSequence
mystart2 =
  jmp Λ [] ∙ globval 1 ⟦ α int ∷ α int ∷ α int ∷ ρ [] ∷ [] ⟧

myprogram2 : ℕ → ProgramState
myprogram2 n = myglobals , myheap , myregister n 0 , mystart2

myprogram2-valid : ⊢ myprogram2 0 programstate
myprogram2-valid = dec-force (programstate-dec _)

myprogram2-step : ⊢ myprogram2 0 ⇒ₙ 10 / myprogram2 5
myprogram2-step = dec-force (exec-dec-specificₕ _ _ _)

-- Use the fibo function
mystart3 : InstructionSequence
mystart3 =
  jmp Λ [] ∙ globval 2 ⟦ α int ∷ α int ∷ ρ [] ∷ [] ⟧

myprogram3 : ℕ → ℕ → ProgramState
myprogram3 a b = myglobals , myheap , myregister a b , mystart3

myprogram3-valid : ⊢ myprogram3 1 1 programstate
myprogram3-valid = dec-force (programstate-dec _)

-- Define an independent fibonacci function
private
  fibo : ℕ → ℕ
  fibo n = go 1 1 n
    where go : ℕ → ℕ → ℕ → ℕ
          go a b 0 = b
          go a b (suc n) = go (a + b) a n

  fibo-valid : fibo 20 ≡ 10946
  fibo-valid = refl

-- At what step-count do we want to verify?
steps : ℕ
steps = 20

myprogram3-step : ⊢ myprogram3 1 1 ⇒ₙ (6 * steps) /
                    myprogram3 (fibo (suc steps)) (fibo steps)
myprogram3-step = dec-force (exec-dec-specificₕ _ _ _)

-- The bad program that cases exponential type blowup
mytupletype : ℕ → Type
mytupletype 0 = int
mytupletype (suc n)
  with mytupletype n
... | τ = tuple ((τ , uninit) ∷ (τ , uninit) ∷ [])

myprogram4 : ℕ → ProgramState
myprogram4 n = myglobals , [] , register [] (int 0 ∷ int 1 ∷ int 2 ∷ int 3 ∷ []) , jmp Λ [] ∙ globval 3 ⟦ α (mytupletype n) ∷ [] ⟧

myprogram4' : ProgramStateₛ
myprogram4' = erase myglobals , [] , register [] (int 0 ∷ int 1 ∷ int 2 ∷ int 3 ∷ []) , jmp (globval 3)

myprogram5-valid : ⊢ myprogram4 0 programstate
myprogram5-valid = dec-force (programstate-dec _)

-- Exponential blowup, do not put this too high!
step-count : ℕ
step-count = 5

myprogram4-step : ⊢ myprogram4 0 ⇒ₙ step-count / myprogram4 step-count
myprogram4-step = dec-force (exec-dec-specificₕ _ _ _)

erasure-proof1 : erase (myprogram4 0) ≡ myprogram4'
erasure-proof1 = dec-force (_ ≟ _)

erasure-proof2 : erase (myprogram4 10) ≡ myprogram4'
erasure-proof2 = dec-force (_ ≟ _)

-- As long as we stay in the untyped semantics, there is no blowup in program
-- size and only a linear blowup in proof size and time to calculate it.
step-count' : ℕ
step-count' = 2000

myprogram4-step'' : ⊢ₛ erase (myprogram4 0) ⇒ₙ step-count' / myprogram4'
myprogram4-step'' = dec-force (exec-dec-specificₛ _ _ _)
