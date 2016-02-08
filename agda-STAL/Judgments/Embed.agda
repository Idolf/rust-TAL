module Judgments.Embed where

open import Util
open import Judgments.Grammar
private module S = SimpleGrammar
private module H = HighGrammar

-- The purpose of this file is
-- to include instances of this record.
-- It includes just a single function, embed, which
-- will translate from high grammar to simple grammar.

-- The second element of the record can safely be
-- ignored -- it only exists because of a bug in Agda.

record Embed (H : Set) (S : Set) : Set where
  constructor mkEmbed'
  field
    embed : H → S
    bogus : ⊤
open Embed {{...}} public

private
  mkEmbed : ∀ {H S} → (H → S) → Embed H S
  mkEmbed f = mkEmbed' f tt

instance
  embedWordValue : Embed H.WordValue S.WordValue
  embedWordValue = mkEmbed f
    where f : H.WordValue → S.WordValue
          f (globval lab) = globval lab
          f (heapval labₕ) = heapval labₕ
          f (int n) = int n
          f uninit = uninit
          f (Λ Δ ∙ w ⟦ θs ⟧) = f w

  embedListWordValue : Embed (List H.WordValue) (List S.WordValue)
  embedListWordValue = mkEmbed (map embed)

  embedVecWordValues : ∀ {n} → Embed (Vec H.WordValue n) (Vec S.WordValue n)
  embedVecWordValues = mkEmbed (Vec-map embed)

  embedSmallValue : Embed H.SmallValue S.SmallValue
  embedSmallValue = mkEmbed f
    where f : H.SmallValue → S.SmallValue
          f (reg ♯r) = reg ♯r
          f (globval lab) = globval lab
          f (int n) = int n
          f (Λ Δ ∙ v ⟦ θs ⟧) = f v

  embedInstruction : Embed H.Instruction S.Instruction
  embedInstruction = mkEmbed f
    where f : H.Instruction → S.Instruction
          f (add ♯rd ♯rs v) = add ♯rd ♯rs (embed v)
          f (sub ♯rd ♯rs v) = sub ♯rd ♯rs (embed v)
          f (salloc n) = salloc n
          f (sfree n) = sfree n
          f (sld ♯rd i) = sld ♯rd i
          f (sst i ♯rs) = sst i ♯rs
          f (ld ♯rd ♯rs i) = ld ♯rd ♯rs i
          f (st ♯rd i ♯rs) = st ♯rd i ♯rs
          f (malloc ♯rd τs) = malloc ♯rd (length τs)
          f (mov ♯rd v) = mov ♯rd (embed v)
          f (beq ♯r v) = beq ♯r (embed v)

  embedInstructionSequence : Embed H.InstructionSequence S.InstructionSequence
  embedInstructionSequence = mkEmbed f
    where f : H.InstructionSequence → S.InstructionSequence
          f (ι ~> I) = embed ι ~> f I
          f (jmp v) = jmp (embed v)
          f halt = halt

  embedGlobalValue : Embed H.GlobalValue S.GlobalValue
  embedGlobalValue = mkEmbed f
    where f : H.GlobalValue → S.GlobalValue
          f (code[ Δ ] Γ ∙ I) = code (embed I)

  embedGlobals : Embed H.Globals S.Globals
  embedGlobals = mkEmbed (map embed)

  embedHeapValue : Embed H.HeapValue S.HeapValue
  embedHeapValue = mkEmbed f
    where f : H.HeapValue → S.HeapValue
          f (tuple ws) = tuple (embed ws)

  embedHeap : Embed H.Heap S.Heap
  embedHeap = mkEmbed (map embed)

  -- This is already covered earlier, since Stack == List WordValue.
  -- It is only included for completeness.
  -- embedStack : Embed H.Stack S.Stack
  -- embedStack = mkEmbed (map embed)

  embedRegisterFile : Embed H.RegisterFile S.RegisterFile
  embedRegisterFile = mkEmbed f
    where f : H.RegisterFile → S.RegisterFile
          f (register sp regs) = register (embed sp) (embed regs)

  embedProgramState : Embed H.ProgramState S.ProgramState
  embedProgramState = mkEmbed f
    where f : H.ProgramState → S.ProgramState
          f (H , R , I) = embed H , embed R , embed I

  embedProgram : Embed H.Program S.Program
  embedProgram = mkEmbed f
    where f : H.Program → S.Program
          f (running G P) = running (embed G) (embed P)
          f halted = halted
