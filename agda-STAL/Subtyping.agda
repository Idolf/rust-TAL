open import Grammar
open import TypeJudgments
open import Util

open import Data.Nat.Properties using (cancel-+-left)

mutual
  infix 4 _⊢_≤τ_
  data _⊢_≤τ_ (Δ : TypeAssignment) : Type → Type → Set where
    α⁼-≤ :
          ∀ {ι} →
       Δ ⊢ α⁼ ι Type →
      ----------------
      Δ ⊢ α⁼ ι ≤τ α⁼ ι

    int-≤ :
      --------------
      Δ ⊢ int ≤τ int

    ns-≤ :
      ------------
      Δ ⊢ ns ≤τ ns

    ∀-≤ :
            ∀ {Δ' Γ₁ Γ₂} →
         ⊢ Δ' TypeAssignment →
         Δ' ++ Δ ⊢ Γ₁ ≤Γ Γ₂ →
      ----------------------------
      Δ ⊢ ∀[ Δ' ] Γ₁ ≤τ ∀[ Δ' ] Γ₂

    tuple-≤ :
                    ∀ {m} {τs₁ τs₂ : Vec InitType m} →
      Allᵥ (λ {(τ⁻₁ , τ⁻₂) → Δ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂ }) (Vec-zip τs₁ τs₂) →
      -------------------------------------------------------------
                       Δ ⊢ tuple τs₁ ≤τ tuple τs₂

  infix 4 _⊢_≤τ⁻_
  data _⊢_≤τ⁻_ (Δ : TypeAssignment) : InitType → InitType → Set where
    τ⁻-≤ :
          ∀ {τ₁ τ₂ φ} →
          Δ ⊢ τ₁ ≤τ τ₂ →
      ---------------------
      Δ ⊢ τ₁ , φ ≤τ⁻ τ₂ , φ

  infix 4 _⊢_≤Γ_
  data _⊢_≤Γ_ (Δ : TypeAssignment) : (Γ₁ Γ₂ : RegisterAssignment) → Set where
    Γ-≤ :
               ∀ {sp regs₁ regs₂} →
                Δ ⊢ sp StackType →
       Allᵥ (λ { (τ₁ , τ₂) → Δ ⊢ τ₁ ≤τ τ₂ })
              (Vec-zip regs₁ regs₂) →
      --------------------------------------------
      Δ ⊢ registerₐ sp regs₁ ≤Γ registerₐ sp regs₂

private
  mutual
    τ-refl : ∀ {Δ τ} → Δ ⊢ τ Type → Δ ⊢ τ ≤τ τ
    τ-refl (valid-α⁼ l) = α⁼-≤ (valid-α⁼ l)
    τ-refl valid-int = int-≤
    τ-refl valid-ns = ns-≤
    τ-refl (valid-∀ Δ⋆ Γ⋆) = ∀-≤ Δ⋆ (Γ-refl Γ⋆)
    τ-refl (valid-tuple τs⋆) = tuple-≤ (Allᵥ-zip (τs⁻-refl τs⋆))

    τ⁻-refl : ∀ {Δ τ⁻} → Δ ⊢ τ⁻ InitType → Δ ⊢ τ⁻ ≤τ⁻ τ⁻
    τ⁻-refl (valid-τ⁻ τ⋆) = τ⁻-≤ (τ-refl τ⋆)

    τs⁻-refl : ∀ {Δ m} {τs : Vec InitType m} →
                 Allᵥ (λ τ⁻ → Δ  ⊢ τ⁻ InitType) τs →
                 Allᵥ (λ τ⁻ → Δ  ⊢ τ⁻ ≤τ⁻ τ⁻) τs
    τs⁻-refl [] = []
    τs⁻-refl (τ⁻⋆ ∷ ps) = τ⁻-refl τ⁻⋆ ∷ τs⁻-refl ps

    Γ-refl : ∀ {Δ Γ} → Δ ⊢ Γ RegisterAssignment → Δ ⊢ Γ ≤Γ Γ
    Γ-refl (valid-Γ sp⋆ regs⋆) = Γ-≤ sp⋆ (Allᵥ-zip (regs-refl regs⋆))

    regs-refl : ∀ {Δ m} {regs : Vec Type m} →
                  Allᵥ (λ τ → Δ ⊢ τ Type) regs →
                  Allᵥ (λ τ → Δ ⊢ τ ≤τ τ) regs
    regs-refl {regs = []} [] = []
    regs-refl {regs = _ ∷ _} (τ⋆ ∷ regs⋆) = τ-refl τ⋆ ∷ regs-refl regs⋆

  mutual
    τ-valid : ∀ {Δ τ₁ τ₂} → Δ ⊢ τ₁ ≤τ τ₂ → Δ ⊢ τ₁ Type × Δ ⊢ τ₂ Type
    τ-valid (α⁼-≤ (valid-α⁼ l)) = valid-α⁼ l , valid-α⁼ l
    τ-valid int-≤ = valid-int , valid-int
    τ-valid ns-≤ = valid-ns , valid-ns
    τ-valid (∀-≤ Δ⋆ Γ≤) with Γ-valid Γ≤
    ... | Γ₁⋆ , Γ₂⋆ = valid-∀ Δ⋆ Γ₁⋆ , valid-∀ Δ⋆ Γ₂⋆
    τ-valid (tuple-≤ τs) with τs⁻-valid τs
    ... | τs₁⋆ , τs₂⋆ = (valid-tuple τs₁⋆) , valid-tuple τs₂⋆

    τ⁻-valid : ∀ {Δ τ⁻₁ τ⁻₂} → Δ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂ →
                               Δ ⊢ τ⁻₁ InitType × Δ ⊢ τ⁻₂ InitType
    τ⁻-valid (τ⁻-≤ τ≤) with τ-valid τ≤
    ... | τ⁻₁⋆ , τ⁻₂⋆ = valid-τ⁻ τ⁻₁⋆ , valid-τ⁻ τ⁻₂⋆

    τs⁻-valid :
      ∀ {Δ m} {τs₁ τs₂ : Vec InitType m} →
        Allᵥ (λ { (τ⁻₁ , τ⁻₂)  → Δ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂ }) (Vec-zip τs₁ τs₂) →
        Allᵥ (λ τ⁻ → Δ ⊢ τ⁻ InitType) τs₁ ×
        Allᵥ (λ τ⁻ → Δ ⊢ τ⁻ InitType) τs₂
    τs⁻-valid {τs₁ = []} {[]} [] = [] , []
    τs⁻-valid {τs₁ = τ⁻₁ ∷ τs₁} {τ⁻₂ ∷ τs₂} (τ⁻≤ ∷ ps)
      with τ⁻-valid τ⁻≤ | τs⁻-valid ps
    ...   | τ⁻₁⋆ , τ⁻₂⋆ | τs₁⋆ , τs₂⋆ = τ⁻₁⋆ ∷ τs₁⋆ , τ⁻₂⋆ ∷ τs₂⋆

    Γ-valid : ∀ {Δ Γ₁ Γ₂} → Δ ⊢ Γ₁ ≤Γ Γ₂ →
                            Δ ⊢ Γ₁ RegisterAssignment ×
                            Δ ⊢ Γ₂ RegisterAssignment
    Γ-valid  (Γ-≤ σ⋆ regs≤) with regs-valid regs≤
    ... | regs₁⋆ , regs₂⋆ = valid-Γ σ⋆ regs₁⋆ , valid-Γ σ⋆ regs₂⋆

    regs-valid :
      ∀ {Δ m} {τs₁ τs₂ : Vec Type m} →
        Allᵥ (λ { (τ₁ , τ₂)  → Δ ⊢ τ₁ ≤τ τ₂ }) (Vec-zip τs₁ τs₂) →
        Allᵥ (λ τ → Δ ⊢ τ Type) τs₁ ×
        Allᵥ (λ τ → Δ ⊢ τ Type) τs₂
    regs-valid {τs₁ = []} {[]} [] = [] , []
    regs-valid {τs₁ = τ₁ ∷ τs₁} {τ₂ ∷ τs₂} (τ≤ ∷ τs≤)
      with τ-valid τ≤ | regs-valid τs≤
    ...   | τ₁⋆ , τ₂⋆ | τs₁⋆ , τs₂⋆ = τ₁⋆ ∷ τs₁⋆ , τ₂⋆ ∷ τs₂⋆

  mutual
    τ-trans : ∀ {Δ τ₁ τ₂ τ₃} → Δ ⊢ τ₁ ≤τ τ₂ → Δ ⊢ τ₂ ≤τ τ₃ → Δ ⊢ τ₁ ≤τ τ₃
    τ-trans (α⁼-≤ τ⋆) (α⁼-≤ _) = α⁼-≤ τ⋆
    τ-trans int-≤ int-≤ = int-≤
    τ-trans ns-≤ ns-≤ = ns-≤
    τ-trans (∀-≤ Δ'⋆ Γ₁₂≤) (∀-≤ _ Γ₂₃≤) = ∀-≤ Δ'⋆ (Γ-trans Γ₁₂≤ Γ₂₃≤)
    τ-trans (tuple-≤ τs₁₂≤) (tuple-≤ τs₂₃≤) = tuple-≤ (τs⁻-trans τs₁₂≤ τs₂₃≤)

    τ⁻-trans : ∀ {Δ τ⁻₁ τ⁻₂ τ⁻₃} → Δ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂ →
                                   Δ ⊢ τ⁻₂ ≤τ⁻ τ⁻₃ →
                                   Δ ⊢ τ⁻₁ ≤τ⁻ τ⁻₃
    τ⁻-trans (τ⁻-≤ τ₁₂≤) (τ⁻-≤ τ₂₃≤) = τ⁻-≤ (τ-trans τ₁₂≤ τ₂₃≤)

    τs⁻-trans :
      ∀ {Δ m} {τs₁ τs₂ τs₃ : Vec InitType m} →
        Allᵥ (λ { (τ⁻₁ , τ⁻₂) → Δ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂ }) (Vec-zip τs₁ τs₂) →
        Allᵥ (λ { (τ⁻₂ , τ⁻₃) → Δ ⊢ τ⁻₂ ≤τ⁻ τ⁻₃ }) (Vec-zip τs₂ τs₃) →
        Allᵥ (λ { (τ⁻₁ , τ⁻₃) → Δ ⊢ τ⁻₁ ≤τ⁻ τ⁻₃ }) (Vec-zip τs₁ τs₃)
    τs⁻-trans {τs₁ = []} {[]} {[]} [] [] = []
    τs⁻-trans {τs₁ = τ₁ ∷ τs₁} {τ₂ ∷ τs₂} {τ₃ ∷ τs₃}
      (τ₁₂≤ ∷ τs₁₂≤) (τ₂₃≤ ∷ τs₂₃≤) =
        τ⁻-trans τ₁₂≤ τ₂₃≤ ∷ τs⁻-trans τs₁₂≤ τs₂₃≤

    Γ-trans : ∀ {Δ Γ₁ Γ₂ Γ₃} → Δ ⊢ Γ₁ ≤Γ Γ₂ → Δ ⊢ Γ₂ ≤Γ Γ₃ → Δ ⊢ Γ₁ ≤Γ Γ₃
    Γ-trans (Γ-≤ sp⋆ regs₁₂≤) (Γ-≤ _ regs₂₃≤) =
      Γ-≤ sp⋆ (regs-trans regs₁₂≤ regs₂₃≤)

    regs-trans : ∀ {Δ m} {τs₁ τs₂ τs₃ : Vec Type m} →
                   Allᵥ (λ { (τ₁ , τ₂) → Δ ⊢ τ₁ ≤τ τ₂ }) (Vec-zip τs₁ τs₂) →
                   Allᵥ (λ { (τ₂ , τ₃) → Δ ⊢ τ₂ ≤τ τ₃ }) (Vec-zip τs₂ τs₃) →
                   Allᵥ (λ { (τ₁ , τ₃) → Δ ⊢ τ₁ ≤τ τ₃ }) (Vec-zip τs₁ τs₃)
    regs-trans {τs₁ = []} {[]} {[]} [] [] = []
    regs-trans {τs₁ = τ₁ ∷ τs₁} {τ₂ ∷ τs₂} {τ₃ ∷ τs₃} (τ₁₂≤ ∷ τs₁₂≤)
      (τ₂₃≤ ∷ τs₂₃≤) = τ-trans τ₁₂≤ τ₂₃≤ ∷ regs-trans τs₁₂≤ τs₂₃≤


record TypeRel (A Ctx : Set) : Set1 where
  constructor typeRel
  field
    _⊢_Valid : Ctx → A → Set
    _⊢_≤_ : Ctx → A → A → Set
    ≤-refl : ∀ {C v} → C ⊢ v Valid → C ⊢ v ≤ v
    ≤-trans : ∀ {C v₁ v₂ v₃} → C ⊢ v₁ ≤ v₂ → C ⊢ v₂ ≤ v₃ → C ⊢ v₁ ≤ v₃
    ≤-valid : ∀ {C v₁ v₂} → C ⊢ v₁ ≤ v₂ → C ⊢ v₁ Valid × C ⊢ v₂ Valid

-- These two should do the same, but they do not
-- open TypeRel {{...}} public
infix 4 _⊢_Valid _⊢_≤_
_⊢_Valid : ∀ {A Ctx : Set} {{_ : TypeRel A Ctx}} →
             Ctx → A → Set
_⊢_Valid {{r}} = TypeRel._⊢_Valid r
_⊢_≤_ : ∀ {A Ctx : Set} {{_ : TypeRel A Ctx}} →
          Ctx → A → A → Set
_⊢_≤_ {{r}} = TypeRel._⊢_≤_ r
≤-refl : ∀ {A Ctx : Set} {{_ : TypeRel A Ctx}} →
           ∀ {C v} → C ⊢ v Valid → C ⊢ v ≤ v
≤-refl {{r}} = TypeRel.≤-refl r
≤-trans : ∀ {A Ctx : Set} {{_ : TypeRel A Ctx}} →
            ∀ {C v₁ v₂ v₃} → C ⊢ v₁ ≤ v₂ → C ⊢ v₂ ≤ v₃ → C ⊢ v₁ ≤ v₃
≤-trans {{r}} = TypeRel.≤-trans r
≤-valid : ∀ {A Ctx : Set} {{_ : TypeRel A Ctx}} →
            ∀ {C v₁ v₂} → C ⊢ v₁ ≤ v₂ → C ⊢ v₁ Valid × C ⊢ v₂ Valid
≤-valid {{r}} = TypeRel.≤-valid r

instance
  Type-rel : TypeRel Type TypeAssignment
  Type-rel = typeRel _⊢_Type _⊢_≤τ_ τ-refl τ-trans τ-valid

  InitType-rel : TypeRel InitType TypeAssignment
  InitType-rel = typeRel _⊢_InitType _⊢_≤τ⁻_ τ⁻-refl τ⁻-trans τ⁻-valid

  StackType-rel : TypeRel StackType TypeAssignment
  StackType-rel = typeRel _⊢_StackType
    (λ Δ σ₁ σ₂ → σ₁ ≡ σ₂ × Δ ⊢ σ₁ StackType)
    (λ σ⋆ → refl , σ⋆)
    (λ { (eq₁₂ , σ₁⋆) (eq₂₃ , σ₂⋆) → trans eq₁₂ eq₂₃ , σ₁⋆ })
    (λ {Δ σ₁ σ₂} →
      λ { (eq , σ₁⋆) → σ₁⋆ , subst (λ σ → Δ ⊢ σ StackType) eq σ₁⋆ })

  LabelAssignment-rel : TypeRel LabelAssignment ⊤
  LabelAssignment-rel = typeRel
    (λ _ ψ → ⊢ ψ LabelAssignment)
    (λ _ ψ₁ ψ₂ → ψ₁ ≡ ψ₂ × ⊢ ψ₁ LabelAssignment)
    (λ ψ⋆ → refl , ψ⋆)
    (λ { (eq₁₂ , ψ₁⋆) (eq₂₃ , ψ₂⋆) → trans eq₁₂ eq₂₃ , ψ₁⋆ })
    (λ {ψ₁ ψ₂} → λ { (eq , ψ₁⋆) → ψ₁⋆ , subst ⊢_LabelAssignment eq ψ₁⋆ })

  TypeAssignment-rel : TypeRel TypeAssignment ⊤
  TypeAssignment-rel = typeRel
    (λ _ Δ → ⊢ Δ TypeAssignment)
    (λ _ Δ₁ Δ₂ → Δ₁ ≡ Δ₂ × ⊢ Δ₁ TypeAssignment)
    (λ Δ⋆ → refl , Δ⋆)
    (λ { (eq₁₂ , Δ₁⋆) (eq₂₃ , Δ₂⋆) → trans eq₁₂ eq₂₃ , Δ₁⋆ })
    (λ {Δ₁ Δ₂} → λ { (eq , Δ₁⋆) → Δ₁⋆ , subst ⊢_TypeAssignment eq Δ₁⋆ })

  RegisterAssignment-rel : TypeRel RegisterAssignment TypeAssignment
  RegisterAssignment-rel =
    typeRel _⊢_RegisterAssignment _⊢_≤Γ_ Γ-refl Γ-trans Γ-valid

  Vec-rel : ∀ {A Ctx : Set} {{_ : TypeRel A Ctx}} {m} → TypeRel (Vec A m) Ctx
  Vec-rel {{r}} = typeRel
      (λ C xs → Allᵥ (λ x → C ⊢ x Valid) xs)
      (λ C xs₁ xs₂ → Allᵥ (λ {(x₁ , x₂) → C ⊢ x₁ ≤ x₂ }) (Vec-zip xs₁ xs₂))
      (λ ps → Allᵥ-zip (Allᵥ-map (≤-refl {{r}}) ps))
      trans'
      valid
    where trans' : ∀ {A Ctx : Set} {{_ : TypeRel A Ctx}} {m} →
                     {C : Ctx} {xs₁ xs₂ xs₃ : Vec A m} →
                     Allᵥ (λ { (x₁ , x₂) → C ⊢ x₁ ≤ x₂ }) (Vec-zip xs₁ xs₂) →
                     Allᵥ (λ { (x₂ , x₃) → C ⊢ x₂ ≤ x₃ }) (Vec-zip xs₂ xs₃) →
                     Allᵥ (λ { (x₁ , x₃) → C ⊢ x₁ ≤ x₃ }) (Vec-zip xs₁ xs₃)
          trans' {xs₁ = []} {[]} {[]} [] [] = []
          trans' {{r}} {xs₁ = x₁ ∷ xs₁} {x₂ ∷ xs₂} {x₃ ∷ xs₃} (x₁₂≤ ∷ xs₁₂≤)
            (x₂₃≤ ∷ xs₂₃≤) = (≤-trans {{r}} x₁₂≤ x₂₃≤) ∷ trans' xs₁₂≤ xs₂₃≤
          valid : ∀ {A Ctx : Set} {{_ : TypeRel A Ctx}} {m} →
                    {C : Ctx} {xs₁ xs₂ : Vec A m} →
                    Allᵥ (λ { (x₁ , x₂) → C ⊢ x₁ ≤ x₂ }) (Vec-zip xs₁ xs₂) →
                    Allᵥ (λ { x₁ → C ⊢ x₁ Valid }) xs₁ ×
                    Allᵥ (λ { x₁ → C ⊢ x₁ Valid }) xs₂
          valid {xs₁ = []} {[]} [] = [] , []
          valid {{r}} {xs₁ = x₁ ∷ xs₁} {x₂ ∷ xs₂} (x≤ ∷ xs≤)
            with ≤-valid {{r}} x≤ | valid xs≤
          ... | x₁⋆ , x₂⋆ | xs₁⋆ , xs₂⋆ = x₁⋆ ∷ xs₁⋆ , x₂⋆ ∷ xs₂⋆


  List-rel : ∀ {A Ctx : Set} {{_ : TypeRel A Ctx}} → TypeRel (List A) Ctx
  List-rel {{r}} = typeRel
      (λ C xs → All (λ x → C ⊢ x Valid) xs)
      (λ C xs₁ xs₂ → length xs₁ ≡ length xs₂ ×
                     All (λ {(x₁ , x₂) → C ⊢ x₁ ≤ x₂ }) (zip xs₁ xs₂))
      (λ ps → refl , All-zip (All-map (≤-refl {{r}}) ps))
      trans'
      valid
    where trans' : ∀ {A Ctx : Set} {{_ : TypeRel A Ctx}} →
                     {C : Ctx} {xs₁ xs₂ xs₃ : List A} →
                     length xs₁ ≡ length xs₂ ×
                       All (λ { (x₁ , x₂) → C ⊢ x₁ ≤ x₂ }) (zip xs₁ xs₂) →
                     length xs₂ ≡ length xs₃ ×
                       All (λ { (x₂ , x₃) → C ⊢ x₂ ≤ x₃ }) (zip xs₂ xs₃) →
                     length xs₁ ≡ length xs₃ ×
                       All (λ { (x₁ , x₃) → C ⊢ x₁ ≤ x₃ }) (zip xs₁ xs₃)
          trans' {xs₁ = []} {[]} {[]} (refl , []) (refl , []) = refl , []
          trans' {xs₁ = []} {_ ∷ _} {_} (() , _) _
          trans' {xs₁ = []} {_} {_ ∷ _} (eq₁₂ , _) (eq₂₃ , _)
            with trans eq₁₂ eq₂₃
          ... | ()
          trans' {xs₁ = _ ∷ _} {[]} {_} (() , _) _
          trans' {xs₁ = _ ∷ _} {_} {[]} (eq₁₂ , _) (eq₂₃ , _)
            with trans eq₁₂ eq₂₃
          ... | ()
          trans' {{r}} {xs₁ = x₁ ∷ xs₁} {x₂ ∷ xs₂} {x₃ ∷ xs₃}
            (eq₁₂ , x₁₂≤ ∷ xs₁₂≤) (eq₂₃ , x₂₃≤ ∷ xs₂₃≤) =
              (trans eq₁₂ eq₂₃) ,
              (≤-trans {{r}} x₁₂≤ x₂₃≤) ∷
                proj₂ (trans' (cancel-+-left 1 eq₁₂ , xs₁₂≤)
                              (cancel-+-left 1 eq₂₃ , xs₂₃≤))
          valid : ∀ {A Ctx : Set} {{_ : TypeRel A Ctx}} →
                    {C : Ctx} {xs₁ xs₂ : List A} →
                    length xs₁ ≡ length xs₂ ×
                    All (λ { (x₁ , x₂) → C ⊢ x₁ ≤ x₂ }) (zip xs₁ xs₂) →
                    All (λ { x₁ → C ⊢ x₁ Valid }) xs₁ ×
                    All (λ { x₁ → C ⊢ x₁ Valid }) xs₂
          valid {xs₁ = []} {[]} (refl , []) = [] , []
          valid {xs₁ = []} {x₁ ∷ xs₂} (() , _)
          valid {xs₁ = x₁ ∷ xs₁} {[]} (() , _)
          valid {{r}} {xs₁ = x₁ ∷ xs₁} {x₂ ∷ xs₂} (eq , x≤ ∷ xs≤)
            with ≤-valid {{r}} x≤ | valid (cancel-+-left 1 eq , xs≤)
          ... | x₁⋆ , x₂⋆ | xs₁⋆ , xs₂⋆ = x₁⋆ ∷ xs₁⋆ , x₂⋆ ∷ xs₂⋆
