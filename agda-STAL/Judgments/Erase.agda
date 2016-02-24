module Judgments.Erase where

open import Util
open import Judgments.Syntax
private module S = SimpleSyntax
private module H = HighSyntax

-- The purpose of this file is
-- to include instances of this record.
-- It includes just a single function, erase, which
-- will translate from high syntax to simple syntax.

-- The second element of the record can safely be
-- ignored -- it only exists because of a bug in Agda.

record Erase (H : Set) (S : Set) : Set where
  constructor mkErase'
  field
    erase : H → S
    bogus : ⊤
open Erase {{...}} public

private
  mkErase : ∀ {H S} → (H → S) → Erase H S
  mkErase f = mkErase' f tt

instance
  eraseWordValue : Erase H.WordValue S.WordValue
  eraseWordValue = mkErase f
    where f : H.WordValue → S.WordValue
          f (globval lab) = globval lab
          f (heapval labₕ) = heapval labₕ
          f (int n) = int n
          f uninit = uninit
          f (Λ Δ ∙ w ⟦ θs ⟧) = f w

  eraseListWordValue : Erase (List H.WordValue) (List S.WordValue)
  eraseListWordValue = mkErase (map erase)

  eraseVecWordValues : ∀ {n} → Erase (Vec H.WordValue n) (Vec S.WordValue n)
  eraseVecWordValues = mkErase (Vec-map erase)

  eraseSmallValue : Erase H.SmallValue S.SmallValue
  eraseSmallValue = mkErase f
    where f : H.SmallValue → S.SmallValue
          f (reg ♯r) = reg ♯r
          f (globval lab) = globval lab
          f (int n) = int n
          f (Λ Δ ∙ v ⟦ θs ⟧) = f v

  eraseInstruction : Erase H.Instruction S.Instruction
  eraseInstruction = mkErase f
    where f : H.Instruction → S.Instruction
          f (add ♯rd ♯rs v) = add ♯rd ♯rs (erase v)
          f (sub ♯rd ♯rs v) = sub ♯rd ♯rs (erase v)
          f (salloc n) = salloc n
          f (sfree n) = sfree n
          f (sld ♯rd i) = sld ♯rd i
          f (sst i ♯rs) = sst i ♯rs
          f (ld ♯rd ♯rs i) = ld ♯rd ♯rs i
          f (st ♯rd i ♯rs) = st ♯rd i ♯rs
          f (malloc ♯rd τs) = malloc ♯rd (length τs)
          f (mov ♯rd v) = mov ♯rd (erase v)
          f (beq ♯r v) = beq ♯r (erase v)

  eraseInstructionSequence : Erase H.InstructionSequence S.InstructionSequence
  eraseInstructionSequence = mkErase f
    where f : H.InstructionSequence → S.InstructionSequence
          f (ι ~> I) = erase ι ~> f I
          f (jmp v) = jmp (erase v)
          f halt = halt

  eraseGlobalValue : Erase H.GlobalValue S.GlobalValue
  eraseGlobalValue = mkErase f
    where f : H.GlobalValue → S.GlobalValue
          f (code[ Δ ] Γ ∙ I) = code (erase I)

  eraseGlobals : Erase H.Globals S.Globals
  eraseGlobals = mkErase (map erase)

  eraseHeapValue : Erase H.HeapValue S.HeapValue
  eraseHeapValue = mkErase f
    where f : H.HeapValue → S.HeapValue
          f (tuple τs ws) = tuple (erase ws)

  eraseHeap : Erase H.Heap S.Heap
  eraseHeap = mkErase (map erase)

  -- This is already covered earlier, since Stack == List WordValue.
  -- It is only included for completeness.
  -- eraseStack : Erase H.Stack S.Stack
  -- eraseStack = mkErase (map erase)

  eraseRegisterFile : Erase H.RegisterFile S.RegisterFile
  eraseRegisterFile = mkErase f
    where f : H.RegisterFile → S.RegisterFile
          f (register sp regs) = register (erase sp) (erase regs)

  eraseMutProgramState : Erase H.MutProgramState S.MutProgramState
  eraseMutProgramState = mkErase f
    where f : H.MutProgramState → S.MutProgramState
          f (H , R , I) = erase H , erase R , erase I

  eraseProgramState : Erase H.ProgramState S.ProgramState
  eraseProgramState = mkErase f
    where f : H.ProgramState → S.ProgramState
          f (G , H , R , I) = erase G , erase H , erase R , erase I
