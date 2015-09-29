open import Grammar
open import Util

private
  mutual
    τ↓ : Type → Tree
    τ↓ (α⁼ ι) = T₁ 0 ι
    τ↓ int = T₀ 1
    τ↓ ns = T₀ 2
    τ↓ (∀[ Δ ] Γ) = T₂ 3 (Δ↓ Δ) (Γ↓ Γ)
    τ↓ (tuple τs) = T₁ 4 (τs↓ τs)

    τs↓ : List (Type × InitializationFlag) → Tree
    τs↓ [] = T₀ 0
    τs↓ ((τ , φ) ∷ τs) = T₃ 1 (τ↓ τ) φ (τs↓ τs)

    σ↓ : StackType → Tree
    σ↓ (ρ⁼ ι) = T₁ 0 ι
    σ↓ nil = T₀ 1
    σ↓ (τ ∷ σ) = T₂ 2 (τ↓ τ) (σ↓ σ)

    Δ↓ : TypeAssignment → Tree
    Δ↓ ∙ = T₀ 0
    Δ↓ (a , Δ) = T₂ 1 (a↓ a) (Δ↓ Δ)

    a↓ : TypeAssignmentValue → Tree
    a↓ α = T₀ 0
    a↓ ρ = T₀ 1

    Γ↓ : RegisterAssignment → Tree
    Γ↓ (registerₐ regs sp) =  T₂ 0 (regs↓ regs) (σ↓ sp)

    regs↓ : ∀ {m} → Vec Type m → Tree
    regs↓ [] = T₀ 0
    regs↓ (τ ∷ τs) = T₂ 1 (τ↓ τ) (regs↓ τs)

  mutual
    τ↑ : Tree → Type
    τ↑ (node 0 (ι ∷ _)) = α⁼ (fromTree ι)
    τ↑ (node 1 _) = int
    τ↑ (node 2 _) = ns
    τ↑ (node 3 (Δ ∷ Γ ∷ _)) = ∀[ Δ↑ Δ ] Γ↑ Γ
    τ↑ (node 4 (τs ∷ _)) = tuple (τs↑ τs)
    τ↑ _ = ns

    τs↑ : Tree → List (Type × InitializationFlag)
    τs↑ (node 0 _) = []
    τs↑ (node 1 (τ ∷ φ ∷ τs ∷ _)) = (τ↑ τ , fromTree φ) ∷ τs↑ τs
    τs↑ _ = []

    σ↑ : Tree → StackType
    σ↑ (node 0 (ι ∷ _)) = ρ⁼ (fromTree ι)
    σ↑ (node 1 _) = nil
    σ↑ (node 2 (τ ∷ σ ∷ _)) = τ↑ τ ∷ σ↑ σ
    σ↑ _ = nil

    Δ↑ : Tree → TypeAssignment
    Δ↑ (node 0 _) = ∙
    Δ↑ (node 1 (a ∷ Δ ∷ _)) = a↑ a , Δ↑ Δ
    Δ↑ _ = ∙

    a↑ : Tree → TypeAssignmentValue
    a↑ (node 0 _) = α
    a↑ (node 1 _) = ρ
    a↑ _ = ρ

    Γ↑ : Tree → RegisterAssignment
    Γ↑ (node _ (regs ∷ sp ∷ _)) = registerₐ (regs↑ regs) (σ↑ sp)
    Γ↑ _ = registerₐ (repeat ns) nil

    regs↑ : ∀ {m} → Tree → Vec Type m
    regs↑ {zero} (node 0 _) = []
    regs↑ {suc i} (node 1 (τ ∷ τs ∷ _)) = τ↑ τ ∷ regs↑ τs
    regs↑ _ = repeat ns

  mutual
    τ≡ : IsInverse τ↓ τ↑
    τ≡ (α⁼ ι) = refl
    τ≡ int = refl
    τ≡ ns = refl
    τ≡ (∀[ Δ ] Γ) = cong₂ ∀[_]_ (Δ≡ Δ) (Γ≡ Γ)
    τ≡ (tuple τs) = cong tuple (τs≡ τs)

    τs≡ : IsInverse τs↓ τs↑
    τs≡ [] = refl
    τs≡ ((τ , φ) ∷ τs) = cong₃ (λ τ φ τs → (τ , φ) ∷ τs) (τ≡ τ) (invTree φ) (τs≡ τs)

    σ≡ : IsInverse σ↓ σ↑
    σ≡ (ρ⁼ ι) = refl
    σ≡ nil = refl
    σ≡ (τ ∷ σ) = cong₂ _∷_ (τ≡ τ) (σ≡ σ)

    Δ≡ : IsInverse Δ↓ Δ↑
    Δ≡ ∙ = refl
    Δ≡ (a , Δ) = cong₂ _,_ (a≡ a) (Δ≡ Δ)

    a≡ : IsInverse a↓ a↑
    a≡ α = refl
    a≡ ρ = refl

    Γ≡ : IsInverse Γ↓ Γ↑
    Γ≡ (registerₐ regs sp) = cong₂ registerₐ (regs≡ regs) (σ≡ sp)

    regs≡ : ∀ {m} → IsInverse (regs↓ {m}) regs↑
    regs≡ [] = refl
    regs≡ (τ ∷ τs) = cong₂ _∷_ (τ≡ τ) (regs≡ τs)

instance
  Type-Tree : ToTree Type
  Type-Tree = tree τ↓ τ↑ τ≡

  StackType-Tree : ToTree StackType
  StackType-Tree = tree σ↓ σ↑ σ≡

  TypeAssignment-Tree : ToTree TypeAssignment
  TypeAssignment-Tree = tree Δ↓ Δ↑ Δ≡

  TypeAssignmentValue-Tree : ToTree TypeAssignmentValue
  TypeAssignmentValue-Tree = tree a↓ a↑ a≡

  RegisterAssignment-Tree : ToTree RegisterAssignment
  RegisterAssignment-Tree = tree Γ↓ Γ↑ Γ≡

  InstantiationValue-Tree : ToTree InstantiationValue
  InstantiationValue-Tree = tree to from eq
    where to : InstantiationValue → Tree
          to (inst-ρ σ) = T₁ 0 σ
          to (inst-α τ) = T₁ 1 τ
          from : Tree → InstantiationValue
          from (node 0 (σ ∷ _)) = inst-ρ (fromTree σ)
          from (node 1 (τ ∷ _)) = inst-α (fromTree τ)
          from _ = inst-ρ default
          eq : IsInverse to from
          eq (inst-ρ σ) = cong inst-ρ (invTree σ)
          eq (inst-α τ) = cong inst-α (invTree τ)

  WordValue-Tree : ToTree WordValue
  WordValue-Tree = tree to from eq
    where to : WordValue → Tree
          to (globval l) = T₁ 0 l
          to (heapval lₕ) = T₁ 1 lₕ
          to (const n) = T₁ 2 n
          to ns = T₀ 3
          to (uninit τ) = T₁ 4 τ
          to (w ⟦ i ⟧) = T₂ 5 (to w) i
          from : Tree → WordValue
          from (node 0 (l ∷ _)) = globval (fromTree l)
          from (node 1 (lₕ ∷ _)) = heapval (fromTree lₕ)
          from (node 2 (n ∷ _)) = const (fromTree n)
          from (node 3 _) = ns
          from (node 4 (τ ∷ _)) = uninit (fromTree τ)
          from (node 5 (w ∷ i ∷ _)) = from w ⟦ fromTree i ⟧
          from _ = ns
          eq : IsInverse to from
          eq (globval l) = refl
          eq (heapval lₕ) = refl
          eq (const n) = refl
          eq ns = refl
          eq (uninit τ) = cong uninit (invTree τ)
          eq (w ⟦ i ⟧) = cong₂ _⟦_⟧ (eq w) (invTree i)

  SmallValue-Tree : ToTree SmallValue
  SmallValue-Tree = tree to from eq
    where to : SmallValue → Tree
          to (reg ♯r) = T₁ 0 ♯r
          to (word w) = T₁ 1 w
          to (v ⟦ i ⟧ᵥ) = T₂ 2 (to v) i
          from : Tree → SmallValue
          from (node 0 (♯r ∷ _)) = reg (fromTree ♯r)
          from (node 1 (w ∷ _)) = word (fromTree w)
          from (node 2 (v ∷ i ∷ _)) = from v ⟦ fromTree i ⟧ᵥ
          from _ = reg default
          eq : IsInverse to from
          eq (reg ♯r) = cong reg (invTree ♯r)
          eq (word w) = cong word (invTree w)
          eq (v ⟦ i ⟧ᵥ) = cong₂ _⟦_⟧ᵥ (eq v) (invTree i)

  Instruction-Tree : ToTree Instruction
  Instruction-Tree = tree to from eq
    where to : Instruction → Tree
          to (add ♯r₁ ♯r₂ v) = T₃ 0 ♯r₁ ♯r₂ v
          to (sub ♯r₁ ♯r₂ v) = T₃ 1 ♯r₁ ♯r₂ v
          to (mul ♯r₁ ♯r₂ v) = T₃ 2 ♯r₁ ♯r₂ v
          to (push v) = T₁ 3 v
          to pop = T₀ 4
          to (sld ♯r i) = T₂ 5 ♯r i
          to (sst i ♯r) = T₂ 6 i ♯r
          to (ld ♯r₁ ♯r₂ i) = T₃ 7 ♯r₁ ♯r₂ i
          to (st ♯r₁ i ♯r₂) = T₃ 8 ♯r₁ i ♯r₂
          from : Tree → Instruction
          from (node 0 (♯r₁ ∷ ♯r₂ ∷ v ∷ _)) = add (fromTree ♯r₁) (fromTree ♯r₂) (fromTree v)
          from (node 1 (♯r₁ ∷ ♯r₂ ∷ v ∷ _)) = sub (fromTree ♯r₁) (fromTree ♯r₂) (fromTree v)
          from (node 2 (♯r₁ ∷ ♯r₂ ∷ v ∷ _)) = mul (fromTree ♯r₁) (fromTree ♯r₂) (fromTree v)
          from (node 3 (v ∷ _)) = push (fromTree v)
          from (node 4 _) = pop
          from (node 5 (♯r ∷ i ∷ _)) = sld (fromTree ♯r) (fromTree i)
          from (node 6 (i ∷ ♯r ∷ _)) = sst (fromTree i) (fromTree ♯r)
          from (node 7 (♯r₁ ∷ ♯r₂ ∷ i ∷ _)) = ld (fromTree ♯r₁) (fromTree ♯r₂) (fromTree i)
          from (node 8 (♯r₁ ∷ i ∷ ♯r₂ ∷ _)) = st (fromTree ♯r₁) (fromTree i) (fromTree ♯r₂)
          from _ = pop
          eq : IsInverse to from
          eq (add ♯r₁ ♯r₂ v) = cong₃ add (invTree ♯r₁) (invTree ♯r₂) (invTree v)
          eq (sub ♯r₁ ♯r₂ v) = cong₃ sub (invTree ♯r₁) (invTree ♯r₂) (invTree v)
          eq (mul ♯r₁ ♯r₂ v) = cong₃ mul (invTree ♯r₁) (invTree ♯r₂) (invTree v)
          eq (push v) = cong push (invTree v)
          eq pop = refl
          eq (sld ♯r i) = cong₂ sld (invTree ♯r) (invTree i)
          eq (sst i ♯r) = cong₂ sst (invTree i) (invTree ♯r)
          eq (ld ♯r₁ ♯r₂ i) = cong₃ ld (invTree ♯r₁) (invTree ♯r₂) (invTree i)
          eq (st ♯r₁ i ♯r₂) = cong₃ st (invTree ♯r₁) (invTree i) (invTree ♯r₂)

  InstructionSequence-Tree : ToTree InstructionSequence
  InstructionSequence-Tree = tree to from eq
    where to : InstructionSequence → Tree
          to (I ~> Is) = T₂ 0 I (to Is)
          to (jmp v) = T₁ 1 v
          from : Tree → InstructionSequence
          from (node 0 (I ∷ Is ∷ _)) = fromTree I ~> from Is
          from (node 1 (v ∷ _)) = jmp (fromTree v)
          from _ = jmp default
          eq : IsInverse to from
          eq (I ~> Is) = cong₂ _~>_ (invTree I) (eq Is)
          eq (jmp v) = cong jmp (invTree v)

  GlobalValue-Tree : ToTree GlobalValue
  GlobalValue-Tree = tree
    (λ { (∀ᵢ[ Δ ] Γ ∙ Is) → T₃ 0 Δ Γ Is })
    (λ { (node _ (Δ ∷ Γ ∷ Is ∷ _)) → ∀ᵢ[ fromTree Δ ] fromTree Γ ∙ fromTree Is
       ; _ → ∀ᵢ[ default ] default ∙ default })
    (λ { (∀ᵢ[ Δ ] Γ ∙ Is) → cong₃ ∀ᵢ[_]_∙_ (invTree Δ) (invTree Γ) (invTree Is) })

  RegisterFile-Tree : ToTree RegisterFile
  RegisterFile-Tree = tree
    (λ { (register regs stack) → T₂ 0 regs stack })
    (λ { (node _ (regs ∷ stack ∷ [])) → register (fromTree regs) (fromTree stack) ; _ → register default default })
    (λ { (register regs stack) → cong₂ register (invTree regs) (invTree stack) })

  Program-Tree : ToTree Program
  Program-Tree = tree
    (λ { (program globals heap registers instructions) → T₄ 0 globals heap registers instructions })
    (λ { (node _ (globals ∷ heap ∷ registers ∷ instructions ∷ _)) →
               program (fromTree globals) (fromTree heap) (fromTree registers) (fromTree instructions)
       ; _ → program default default default default })
    (λ { (program globals heap registers instructions) →
               cong₄ program (invTree globals) (invTree heap) (invTree registers) (invTree instructions)
    })
