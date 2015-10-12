open import Grammar
open import Util

private
  mutual
    τ-from : Tree → ¿ Type
    τ-from (node 0 (ι ∷ _)) = α⁼ <$> fromTree ι
    τ-from (node 1 _) = Just int
    τ-from (node 2 _) = Just ns
    τ-from (node 3 (Δ ∷ Γ ∷ _)) = ∀[_]_ <$> Δ-from Δ <*> Γ-from Γ
    τ-from (node 4 τs) = (tuple ∘ proj₂) <$> τs-from τs
    τ-from _ = Nothing

    τ-sur : IsSurjective τ-from
    τ-sur (α⁼ ι) = T₁ 0 ι , refl
    τ-sur int = T₀ 1 , refl
    τ-sur ns = T₀ 2 , refl
    τ-sur (∀[ Δ ] Γ) = T₂ 3 (proj₁ (Δ-sur Δ)) (proj₁ (Γ-sur Γ)) ,
      ∀[_]_ <$=> proj₂ (Δ-sur Δ) <*=> proj₂ (Γ-sur Γ)
    τ-sur (tuple τs) = node 4 (proj₁ (τs-sur (_ , τs))) ,
      (tuple ∘ proj₂) <$=> proj₂ (τs-sur (_ , τs))

    τs-from : List Tree → ¿ (∃ λ m → Vec InitType m)
    τs-from [] = Just (0 , [])
    τs-from (node _ (τ ∷ φ ∷ _) ∷ τs) =
      (λ τ φ → λ { (l , τs) → suc l , (τ , φ) ∷ τs })
        <$> τ-from τ <*> fromTree φ <*> τs-from τs
    τs-from _ = Nothing

    τs-sur : IsSurjective τs-from
    τs-sur (zero , []) = [] , refl
    τs-sur (suc l , (τ , φ) ∷ τs) =
      T₂ 0 (proj₁ (τ-sur τ)) φ ∷ proj₁ (τs-sur (l , τs)) ,
      (λ τ φ → λ { (l , τs) → suc l , (τ , φ) ∷ τs })
        <$=> proj₂ (τ-sur τ) <*=> invTree φ <*=> proj₂ (τs-sur (l , τs))

    σ-from : Tree → ¿ StackType
    σ-from (node 0 (ι ∷ _)) = ρ⁼ <$> fromTree ι
    σ-from (node 1 _) = Just nil
    σ-from (node 2 (τ ∷ σ ∷ _)) = _∷_ <$> τ-from τ <*> σ-from σ
    σ-from _ = Nothing

    σ-sur : IsSurjective σ-from
    σ-sur (ρ⁼ ι) = T₁ 0 ι , refl
    σ-sur nil = T₀ 1 , refl
    σ-sur (τ ∷ σ) = T₂ 2 (proj₁ (τ-sur τ)) (proj₁ (σ-sur σ)) ,
      _∷_ <$=> proj₂ (τ-sur τ) <*=> proj₂ (σ-sur σ)

    Δ-from : Tree → ¿ TypeAssignment
    Δ-from (node 0 _) = Just []
    Δ-from (node 1 (a ∷ Δ ∷ _)) = _∷_ <$> a-from a <*> Δ-from Δ
    Δ-from _ = Nothing

    Δ-sur : IsSurjective Δ-from
    Δ-sur [] = T₀ 0 , refl
    Δ-sur (a ∷ Δ) = T₂ 1 (proj₁ (a-sur a)) (proj₁ (Δ-sur Δ)) ,
      _∷_ <$=> proj₂ (a-sur a) <*=> proj₂ (Δ-sur Δ)

    a-from : Tree → ¿ TypeAssignmentValue
    a-from (node 0 _) = Just α
    a-from (node 1 _) = Just ρ
    a-from _ = Nothing

    a-sur : IsSurjective a-from
    a-sur α = T₀ 0 , refl
    a-sur ρ = T₀ 1 , refl

    Γ-from : Tree → ¿ RegisterAssignment
    Γ-from (node _ (sp ∷ regs)) =
      registerₐ <$> σ-from sp <*> regs-from regs
    Γ-from _ = Nothing

    Γ-sur : IsSurjective Γ-from
    Γ-sur (registerₐ sp regs) =
      node 0 (proj₁ (σ-sur sp) ∷ proj₁ (regs-sur regs)) ,
      registerₐ <$=> proj₂ (σ-sur sp) <*=> proj₂ (regs-sur regs)

    regs-from : ∀ {m} → List Tree → ¿ Vec Type m
    regs-from {zero}  []       = Just []
    regs-from {zero}  (τ ∷ τs) = Nothing
    regs-from {suc m} []       = Nothing
    regs-from {suc m} (τ ∷ τs) = _∷_ <$> τ-from τ <*> regs-from τs

    regs-sur : ∀ {m} → IsSurjective (regs-from {m})
    regs-sur [] = [] , refl
    regs-sur (τ ∷ τs) = (proj₁ (τ-sur τ) ∷ proj₁ (regs-sur τs)) ,
      _∷_ <$=> proj₂ (τ-sur τ) <*=> proj₂ (regs-sur τs)

instance
  Type-Tree : ToTree Type
  Type-Tree = tree⋆ τ-from τ-sur

  StackType-Tree : ToTree StackType
  StackType-Tree = tree⋆ σ-from σ-sur

  TypeAssignmentValue-Tree : ToTree TypeAssignmentValue
  TypeAssignmentValue-Tree = tree⋆ a-from a-sur

  RegisterAssignment-Tree : ToTree RegisterAssignment
  RegisterAssignment-Tree = tree⋆ Γ-from Γ-sur

  Instantiation-Tree : ToTree Instantiation
  Instantiation-Tree = tree⋆ from sur
    where from : Tree → ¿ Instantiation
          from (node 0 (τ ∷ _)) = α <$> fromTree τ
          from (node 1 (σ ∷ _)) = ρ <$> fromTree σ
          from _ = Nothing
          sur : IsSurjective from
          sur (α τ) = T₁ 0 τ , α <$=> invTree τ
          sur (ρ σ) = T₁ 1 σ , ρ <$=> invTree σ

  CastValue-Tree : ∀ {A} {{_ : ToTree A}} → ToTree (CastValue A)
  CastValue-Tree = tree⋆ from sur
    where from : ∀ {A} {{_ : ToTree A}} → Tree → ¿ (CastValue A)
          from (node 0 (i ∷ _)) = inst <$> fromTree i
          from (node 1 (n ∷ _)) = weaken <$> fromTree n
          from _ = Nothing
          sur : IsSurjective from
          sur (inst i) = T₁ 0 i , inst <$=> invTree i
          sur (weaken n) = T₁ 1 n , weaken <$=> invTree n

  Cast-Tree : ∀ {A} {{_ : ToTree A}} → ToTree (Cast A)
  Cast-Tree = tree⋆ from sur
    where from : ∀ {A} {{_ : ToTree A}} → Tree → ¿ (Cast A)
          from (node _ (cᵥ ∷ ι ∷ _)) = _/_ <$> fromTree cᵥ <*> fromTree ι
          from _ = Nothing
          sur : IsSurjective from
          sur (cᵥ / ι) = T₂ 0 cᵥ ι , _/_ <$=> invTree cᵥ <*=> invTree ι

  WordValue-Tree : ToTree WordValue
  WordValue-Tree = tree⋆ from sur
    where from : Tree → ¿ WordValue
          from (node 0 (l ∷ _)) = globval <$> fromTree l
          from (node 1 (lₕ ∷ _)) = heapval <$> fromTree lₕ
          from (node 2 (n ∷ _)) = const <$> fromTree n
          from (node 3 _) = Just ns
          from (node 4 (τ ∷ _)) = uninit <$> fromTree τ
          from (node 5 (w ∷ i ∷ _)) = _⟦_⟧ <$> from w <*> fromTree i
          from _ = Nothing
          sur : IsSurjective from
          sur (globval l) = T₁ 0 l , globval <$=> invTree l
          sur (heapval lₕ) = T₁ 1 lₕ , heapval <$=> invTree lₕ
          sur (const n) = T₁ 2 n , const <$=> invTree n
          sur ns = T₀ 3 , refl
          sur (uninit τ) = T₁ 4 τ , uninit <$=> invTree τ
          sur (w ⟦ i ⟧) = T₂ 5 (proj₁ (sur w)) i ,
            _⟦_⟧ <$=> proj₂ (sur w) <*=> invTree i

  SmallValue-Tree : ToTree SmallValue
  SmallValue-Tree = tree⋆ from sur
    where from : Tree → ¿ SmallValue
          from (node 0 (♯r ∷ _)) = reg <$> fromTree ♯r
          from (node 1 (w ∷ _)) = word <$> fromTree w
          from (node 2 (v ∷ i ∷ _)) = _⟦_⟧ᵥ <$> from v <*> fromTree i
          from _ = Nothing
          sur : IsSurjective from
          sur (reg ♯r) = T₁ 0 ♯r , reg <$=> invTree ♯r
          sur (word w) = T₁ 1 w , word <$=> invTree w
          sur (v ⟦ i ⟧ᵥ) = T₂ 2 (proj₁ (sur v)) i ,
            _⟦_⟧ᵥ <$=> proj₂ (sur v) <*=> invTree i

  Instruction-Tree : ToTree Instruction
  Instruction-Tree = tree⋆ from sur
    where from : Tree → ¿ Instruction
          from (node 0 (♯r₁ ∷ ♯r₂ ∷ v ∷ _)) =
            add <$> fromTree ♯r₁ <*> fromTree ♯r₂ <*> fromTree v
          from (node 1 (♯r₁ ∷ ♯r₂ ∷ v ∷ _)) =
            sub <$> fromTree ♯r₁ <*> fromTree ♯r₂ <*> fromTree v
          from (node 2 (v ∷ _)) = push <$> fromTree v
          from (node 3 _) = Just pop
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
          from _ = Nothing
          sur : IsSurjective from
          sur (add ♯r₁ ♯r₂ v) = T₃ 0 ♯r₁ ♯r₂ v ,
            add <$=> invTree ♯r₁ <*=> invTree ♯r₂ <*=> invTree v
          sur (sub ♯r₁ ♯r₂ v) = T₃ 1 ♯r₁ ♯r₂ v ,
            sub <$=> invTree ♯r₁ <*=> invTree ♯r₂ <*=> invTree v
          sur (push v) = T₁ 2 v , push <$=> invTree v
          sur pop = T₀ 3 , refl
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

  InstructionSequence-Tree : ToTree InstructionSequence
  InstructionSequence-Tree = tree⋆ from sur
    where from : Tree → ¿ InstructionSequence
          from (node 0 (I ∷ Is ∷ _)) = _~>_ <$> fromTree I <*> from Is
          from (node 1 (v ∷ _)) = jmp <$> fromTree v
          from _ = Nothing
          sur : IsSurjective from
          sur (I ~> Is) = T₂ 0 I (proj₁ (sur Is)) ,
            _~>_ <$=> invTree I <*=> proj₂ (sur Is)
          sur (jmp v) = T₁ 1 v , jmp <$=> invTree v

  GlobalValue-Tree : ToTree GlobalValue
  GlobalValue-Tree = tree⋆
    (λ { (node _ (Δ ∷ Γ ∷ Is ∷ _)) →
           ∀[_]_∙_ <$> fromTree Δ <*> fromTree Γ <*> fromTree Is
       ; _ → Nothing })
    (λ { (∀[ Δ ] Γ ∙ Is) → T₃ 0 Δ Γ Is ,
           ∀[_]_∙_ <$=> invTree Δ <*=> invTree Γ <*=> invTree Is })

  RegisterFile-Tree : ToTree RegisterFile
  RegisterFile-Tree = tree⋆
    (λ { (node _ (stack ∷ regs ∷ [])) →
           register <$> fromTree stack <*> fromTree regs ; _ → Nothing })
    (λ { (register stack regs) → T₂ 0 stack regs ,
           register <$=> invTree stack <*=> invTree regs })
