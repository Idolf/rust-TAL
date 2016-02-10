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

myglobals : Globals
myglobals = [ infloop ]

myheap : Heap
myheap = []

myregister : RegisterFile
myregister = register [] (int 0 ∷ int 1 ∷ int 2 ∷ int 3 ∷ [])

mystart : InstructionSequence
mystart =
  jmp Λ [] ∙ globval 0 ⟦ α int ∷ α int ∷ α int ∷ α int ∷ ρ [] ∷ [] ⟧

mystate : ProgramState
mystate = myheap , myregister , mystart

myprogram : Program
myprogram = running myglobals mystate

myprogram-valid : ⊢ myprogram program
myprogram-valid = dec-force (program-dec _)

myprogram-step : ⊢ myprogram ⇒ myprogram
myprogram-step = dec-force (step-prg-dec-specificₕ _ _)
