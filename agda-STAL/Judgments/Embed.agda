module Judgments.Embed where

open import Util
open import Judgments.Grammar
private module S = SimpleGrammar
private module H = HighGrammar

record Embed (H : Set) (S : Set) : Set where
  constructor mkEmbed'
  field
    embed : H → S
    bogus : ⊤
open Embed {{...}} public

mkEmbed : ∀ {H S} → (H → S) → Embed H S
mkEmbed f = mkEmbed' f tt

VecEmbed : ∀ {H S n} → Embed H S → Embed (Vec H n) (Vec S n)
VecEmbed {H} {S} (mkEmbed' f _) = mkEmbed f'
  where f' : ∀ {n} → Vec H n → Vec S n
        f' [] = []
        f' (x ∷ xs) = f x ∷ f' xs

ListEmbed : ∀ {H S} → Embed H S → Embed (List H) (List S)
ListEmbed {H} {S} (mkEmbed' f _) = mkEmbed f'
  where f' : List H → List S
        f' [] = []
        f' (x ∷ xs) = f x ∷ f' xs

instance
  embedWordValue : Embed H.WordValue S.WordValue
  embedWordValue = mkEmbed f
    where f : H.WordValue → S.WordValue
          f (globval lab) = globval lab
          f (heapval labₕ) = heapval labₕ
          f (int n) = int n
          f ns = ns
          f (uninit τ) = ns
          f (Λ Δ ∙ w ⟦ is ⟧) = f w

  embedListWordValue : Embed (List H.WordValue) (List S.WordValue)
  embedListWordValue = ListEmbed embedWordValue

  embedVecWordValues : ∀ {n} → Embed (Vec H.WordValue n) (Vec S.WordValue n)
  embedVecWordValues = VecEmbed embedWordValue

  embedSmallValue : Embed H.SmallValue S.SmallValue
  embedSmallValue = mkEmbed f
    where f : H.SmallValue → S.SmallValue
          f (reg ♯r) = reg ♯r
          f (globval lab) = globval lab
          f (int n) = int n
          f (Λ Δ ∙ v ⟦ is ⟧) = f v

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
  embedGlobals = ListEmbed embedGlobalValue

  embedHeapValue : Embed H.HeapValue S.HeapValue
  embedHeapValue = mkEmbed f
    where f : H.HeapValue → S.HeapValue
          f (tuple ws) = tuple (embed ws)

  embedHeap : Embed H.Heap S.Heap
  embedHeap = ListEmbed embedHeapValue

  -- This is already covered earlier and only included for completeness
  -- embedStack : Embed H.Stack S.Stack
  -- embedStack = ListEmbed embedWordValue

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
