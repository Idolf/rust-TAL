module Simple.Embed where

open import Util
import Simple.Grammar as S
import Judgments.Grammar as H

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
          f (H.globval l) = S.globval l
          f (H.heapval l) = S.heapval l
          f (H.int n) = S.int n
          f H.ns = S.ns
          f (H.uninit τ) = S.uninit
          f H.Λ Δ ∙ w ⟦ is ⟧ = f w

  embedListWordValue : Embed (List H.WordValue) (List S.WordValue)
  embedListWordValue = ListEmbed embedWordValue

  embedVecWordValues : ∀ {n} → Embed (Vec H.WordValue n) (Vec S.WordValue n)
  embedVecWordValues = VecEmbed embedWordValue

  embedSmallValue : Embed H.SmallValue S.SmallValue
  embedSmallValue = mkEmbed f
    where f : H.SmallValue → S.SmallValue
          f (H.reg ♯r) = S.reg ♯r
          f (H.globval l) = S.globval l
          f (H.int n) = S.int n
          f H.ns = S.ns
          f (H.uninit τ) = S.uninit
          f H.Λ Δ ∙ v ⟦ is ⟧ = f v

  embedInstruction : Embed H.Instruction S.Instruction
  embedInstruction = mkEmbed f
    where f : H.Instruction → S.Instruction
          f (H.add ♯rd ♯rs v) = S.add ♯rd ♯rs (embed v)
          f (H.sub ♯rd ♯rs v) = S.sub ♯rd ♯rs (embed v)
          f (H.salloc n) = S.salloc n
          f (H.sfree n) = S.sfree n
          f (H.sld ♯rd i) = S.sld ♯rd i
          f (H.sst i ♯rs) = S.sst i ♯rs
          f (H.ld ♯rd ♯rs i) = S.ld ♯rd ♯rs i
          f (H.st ♯rd i ♯rs) = S.st ♯rd i ♯rs
          f (H.malloc ♯rd τs) = S.malloc ♯rd (length τs)
          f (H.mov ♯rd v) = S.mov ♯rd (embed v)
          f (H.beq ♯r v) = S.beq ♯r (embed v)

  embedInstructionSequence : Embed H.InstructionSequence S.InstructionSequence
  embedInstructionSequence = mkEmbed f
    where f : H.InstructionSequence → S.InstructionSequence
          f (ι H.~> I) = embed ι S.~> f I
          f (H.jmp v) = S.jmp (embed v)

  embedGlobalValue : Embed H.GlobalValue S.GlobalValue
  embedGlobalValue = mkEmbed f
    where f : H.GlobalValue → S.GlobalValue
          f (H.code[ Δ ] Γ ∙ I) = S.code (embed I)

  embedGlobals : Embed H.Globals S.Globals
  embedGlobals = ListEmbed embedGlobalValue

  embedHeapValue : Embed H.HeapValue S.HeapValue
  embedHeapValue = mkEmbed f
    where f : H.HeapValue → S.HeapValue
          f (H.tuple ws) = S.tuple (embed ws)

  embedHeap : Embed H.Heap S.Heap
  embedHeap = ListEmbed embedHeapValue

  -- This is already covered earlier
  -- embedStack : Embed H.Stack S.Stack
  -- embedStack = ListEmbed embedWordValue

  embedRegisterFile : Embed H.RegisterFile S.RegisterFile
  embedRegisterFile = mkEmbed f
    where f : H.RegisterFile → S.RegisterFile
          f (H.register sp regs) = S.register (embed sp) (embed regs)

  embedProgramState : Embed H.ProgramState S.ProgramState
  embedProgramState = mkEmbed f
    where f : H.ProgramState → S.ProgramState
          f (H , R , I) = embed H , embed R , embed I

  embedProgram : Embed H.Program S.Program
  embedProgram = mkEmbed f
    where f : H.Program → S.Program
          f (G , P) = embed G , embed P
