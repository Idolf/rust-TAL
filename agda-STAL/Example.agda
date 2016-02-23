open import Util
open import Judgments
open import Lemmas
open HighGrammar
open HighSemantics

infloop : GlobalValue
infloop =
  code[ α ∷ α ∷ α ∷ α ∷ ρ ∷ [] ]
    registerₐ (ρ⁼ 4) (α⁼ 0 ∷ α⁼ 1 ∷ α⁼ 2 ∷ α⁼ 3 ∷ []) ∙
    (jmp Λ [] ∙ globval 0 ⟦ α (α⁼ 4) ∷ α (α⁼ 4) ∷ α (α⁼ 4) ∷ α (α⁼ 4) ∷ ρ (ρ⁼ 4) ∷ [] ⟧)

addloop =
  code[ α ∷ α ∷ α ∷ ρ ∷ [] ]
    registerₐ (ρ⁼ 3) (int ∷ α⁼ 0 ∷ α⁼ 1 ∷ α⁼ 2 ∷ []) ∙
    (add (# 0) (# 0) (int 1) ~> jmp Λ [] ∙ globval 1 ⟦ α (α⁼ 3) ∷ α (α⁼ 3) ∷ α (α⁼ 3) ∷ ρ (ρ⁼ 3) ∷ [] ⟧)

myglobals : Globals
myglobals = infloop ∷ addloop ∷ []

myheap : Heap
myheap = []

myregister : ℕ → RegisterFile
myregister n = register [] (int n ∷ int 1 ∷ int 2 ∷ int 3 ∷ [])

-- Use the first function
mystart : InstructionSequence
mystart =
  jmp Λ [] ∙ globval 0 ⟦ α int ∷ α int ∷ α int ∷ α int ∷ ρ [] ∷ [] ⟧

myprogram : ProgramState
myprogram = myglobals , myheap , myregister 0 , mystart

myprogram-valid : ⊢ myprogram programstate
myprogram-valid = dec-force (programstate-dec _)

myprogram-step : ⊢ myprogram ⇒ myprogram
myprogram-step = dec-force (step-prg-dec-specificₕ _ _)

-- Use the second function
mystart2 : InstructionSequence
mystart2 =
  jmp Λ [] ∙ globval 1 ⟦ α int ∷ α int ∷ α int ∷ ρ [] ∷ [] ⟧

myprogram2 : ℕ → ProgramState
myprogram2 n = myglobals , myheap , myregister n , mystart2

myprogram2-valid : ⊢ myprogram programstate
myprogram2-valid = dec-force (programstate-dec _)

myprogram2-step : ⊢ myprogram2 0 ⇒ₙ 10 / myprogram2 5
myprogram2-step = dec-force (exec-dec-specificₕ _ _ _)
