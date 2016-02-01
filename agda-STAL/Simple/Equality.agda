module Simple.Equality where

open import Util
open import Simple.Grammar

instance
  WordValue-Tree : ToTree WordValue
  WordValue-Tree = tree⋆ from sur
    where from : Tree → Maybe WordValue
          from (node 0 (l ∷ _)) = globval <$> fromTree l
          from (node 1 (lₕ ∷ _)) = heapval <$> fromTree lₕ
          from (node 2 (n ∷ _)) = int <$> fromTree n
          from (node 3 _) = just ns
          from (node 4 _) = just uninit
          from _ = nothing
          sur : IsSurjective from
          sur (globval l) = T₁ 0 l , globval <$=> invTree l
          sur (heapval lₕ) = T₁ 1 lₕ , heapval <$=> invTree lₕ
          sur (int n) = T₁ 2 n , int <$=> invTree n
          sur ns = T₀ 3 , refl
          sur uninit = T₀ 4 , refl

  SmallValue-Tree : ToTree SmallValue
  SmallValue-Tree = tree⋆ from sur
    where from : Tree → Maybe SmallValue
          from (node 0 (♯r ∷ _)) = reg <$> fromTree ♯r
          from (node 1 (l ∷ _)) = globval <$> fromTree l
          from (node 2 (n ∷ _)) = int <$> fromTree n
          from (node 3 _) = just ns
          from (node 4 _) = just uninit
          from _ = nothing
          sur : IsSurjective from
          sur (reg ♯r) = T₁ 0 ♯r , reg <$=> invTree ♯r
          sur (globval l) = T₁ 1 l , globval <$=> invTree l
          sur (int n) = T₁ 2 n , int <$=> invTree n
          sur ns = T₀ 3 , refl
          sur uninit = T₀ 4 , refl

  Instruction-Tree : ToTree Instruction
  Instruction-Tree = tree⋆ from sur
    where from : Tree → Maybe Instruction
          from (node 0 (♯r₁ ∷ ♯r₂ ∷ v ∷ _)) =
            add <$> fromTree ♯r₁ <*> fromTree ♯r₂ <*> fromTree v
          from (node 1 (♯r₁ ∷ ♯r₂ ∷ v ∷ _)) =
            sub <$> fromTree ♯r₁ <*> fromTree ♯r₂ <*> fromTree v
          from (node 2 (n ∷ _)) = salloc <$> fromTree n
          from (node 3 (n ∷ _)) = sfree <$> fromTree n
          from (node 4 (♯r ∷ i ∷ _)) = sld <$> fromTree ♯r <*> fromTree i
          from (node 5 (i ∷ ♯r ∷ _)) = sst <$> fromTree i <*> fromTree ♯r
          from (node 6 (♯r₁ ∷ ♯r₂ ∷ i ∷ _)) =
            ld <$> fromTree ♯r₁ <*> fromTree ♯r₂ <*> fromTree i
          from (node 7 (♯r₁ ∷ i ∷ ♯r₂ ∷ _)) =
            st <$> fromTree ♯r₁ <*> fromTree i <*> fromTree ♯r₂
          from (node 8 (♯rd ∷ τs ∷ _)) =
            malloc <$> fromTree ♯rd <*> fromTree τs
          from (node 9 (♯rd ∷ v ∷ _)) =
            mov <$> fromTree ♯rd <*> fromTree v
          from (node 10 (♯r ∷ v ∷ _)) =
            beq <$> fromTree ♯r <*> fromTree v
          from _ = nothing
          sur : IsSurjective from
          sur (add ♯r₁ ♯r₂ v) = T₃ 0 ♯r₁ ♯r₂ v ,
            add <$=> invTree ♯r₁ <*=> invTree ♯r₂ <*=> invTree v
          sur (sub ♯r₁ ♯r₂ v) = T₃ 1 ♯r₁ ♯r₂ v ,
            sub <$=> invTree ♯r₁ <*=> invTree ♯r₂ <*=> invTree v
          sur (salloc n) = T₁ 2 n , salloc <$=> invTree n
          sur (sfree n) = T₁ 3 n , sfree <$=> invTree n
          sur (sld ♯r i) = T₂ 4 ♯r i , sld <$=> invTree ♯r <*=> invTree i
          sur (sst i ♯r) = T₂ 5 i ♯r , sst <$=> invTree i <*=> invTree ♯r
          sur (ld ♯r₁ ♯r₂ i) = T₃ 6 ♯r₁ ♯r₂ i ,
            ld <$=> invTree ♯r₁ <*=> invTree ♯r₂ <*=> invTree i
          sur (st ♯r₁ i ♯r₂) = T₃ 7 ♯r₁ i ♯r₂ ,
            st <$=> invTree ♯r₁ <*=> invTree i <*=> invTree ♯r₂
          sur (malloc ♯rd τs) = T₂ 8 ♯rd τs ,
            malloc <$=> invTree ♯rd <*=> invTree τs
          sur (mov ♯rd v) = T₂ 9 ♯rd v ,
            mov <$=> invTree ♯rd <*=> invTree v
          sur (beq ♯r v) = T₂ 10 ♯r v ,
            beq <$=> invTree ♯r <*=> invTree v

  InstructionSequence-Tree : ToTree InstructionSequence
  InstructionSequence-Tree = tree⋆ from sur
    where from : Tree → Maybe InstructionSequence
          from (node 0 (ι ∷ I ∷ _)) = _~>_ <$> fromTree ι <*> from I
          from (node 1 (v ∷ _)) = jmp <$> fromTree v
          from (node 2 _) = just halt
          from _ = nothing
          sur : IsSurjective from
          sur (ι ~> I) = T₂ 0 ι (proj₁ (sur I)) ,
            _~>_ <$=> invTree ι <*=> proj₂ (sur I)
          sur (jmp v) = T₁ 1 v , jmp <$=> invTree v
          sur halt = T₀ 2 , refl

  HeapValue-Tree : ToTree HeapValue
  HeapValue-Tree = tree⋆ from sur
    where from' : List Tree → Maybe (List WordValue)
          from' [] = just []
          from' (t ∷ ts) = _∷_ <$> fromTree t <*> from' ts
          sur' : IsSurjective from'
          sur' [] = [] , refl
          sur' (w ∷ ws) = toTree w ∷ proj₁ (sur' ws) ,
            _∷_ <$=> invTree w <*=> proj₂ (sur' ws)
          from : Tree → Maybe HeapValue
          from (node _ ws) = tuple <$> from' ws
          sur : IsSurjective from
          sur (tuple ws) =
            node 0 (proj₁ (sur' ws)) ,
            tuple <$=> proj₂ (sur' ws)

  GlobalValue-Tree : ToTree GlobalValue
  GlobalValue-Tree = tree⋆
    (λ { (node _ (I ∷ _)) → code <$> fromTree I ; _ → nothing })
    (λ { (code I) → T₁ 0 I , code <$=> invTree I })

  RegisterFile-Tree : ToTree RegisterFile
  RegisterFile-Tree = tree⋆
    (λ { (node _ (stack ∷ regs ∷ [])) →
           register <$> fromTree stack <*> fromTree regs ; _ → nothing })
    (λ { (register stack regs) → T₂ 0 stack regs ,
           register <$=> invTree stack <*=> invTree regs })

  Program-Tree : ToTree Program
  Program-Tree = tree⋆ from sur
    where from : Tree → Maybe Program
          from (node 0 (G ∷ P ∷ _)) = going <$> fromTree G <*> fromTree P
          from (node 1 _) = just halted
          from _ = nothing
          sur : IsSurjective from
          sur (going G P) = T₂ 0 G P ,
            going <$=> invTree G <*=> invTree P
          sur halted = T₀ 1 , refl
