module Lemmas.SubtypeSubstitution where

open import Util
open import Judgments
open import Lemmas.Subtypes
open import Lemmas.Substitution
open import Lemmas.TypeSubstitution

-- The purpose of this file is to create instance
-- of the following record:
record SubtypeSubstitution (A : Set) {{S : Substitution A}}
                                     {{ST : Subtype A}} : Set where
  constructor subtypeSubstitution
  field
    subst-subtype-weaken :
      ∀ Δ₁ Δ₂ Δ₃ →
        {v₁ v₂ : A} →
        Δ₁ ++ Δ₃ ⊢ v₁ ≤ v₂ →
        Δ₁ ++ Δ₂ ++ Δ₃ ⊢ weaken (length Δ₁) (length Δ₂) v₁ ≤ weaken (length Δ₁) (length Δ₂) v₂
    subst-subtype-inst :
      ∀ Δ₁ {Δ₂ a i} →
        Δ₂ ⊢ i of a instantiation →
        {v₁ v₁' v₂ v₂' : A} →
        Δ₁ ++ a ∷ Δ₂ ⊢ v₁ ≤ v₂ →
        v₁ ⟦ i / length Δ₁ ⟧≡ v₁' →
        v₂ ⟦ i / length Δ₁ ⟧≡ v₂' →
        Δ₁ ++ Δ₂ ⊢ v₁' ≤ v₂'
open SubtypeSubstitution {{...}} public

private
  subtype-weakenᵗ :
    ∀ A {{_ : Substitution A}}
        {{_ : Subtype A}} → Set
  subtype-weakenᵗ A =
    ∀ Δ₁ Δ₂ Δ₃ →
      {v₁ v₂ : A} →
      Δ₁ ++ Δ₃ ⊢ v₁ ≤ v₂ →
      Δ₁ ++ Δ₂ ++ Δ₃ ⊢ weaken (length Δ₁) (length Δ₂) v₁ ≤ weaken (length Δ₁) (length Δ₂) v₂

  mutual
    τ-subtype-weaken : subtype-weakenᵗ Type
    τ-subtype-weaken Δ₁ Δ₂ Δ₃ {α⁼ ι} (α⁼-≤ l)
      with (length Δ₁) ≤? ι | subst-valid-weaken Δ₁ Δ₂ Δ₃ (valid-α⁼ l)
    ... | yes len≤ι | valid-α⁼ l' = α⁼-≤ l'
    ... | no len≰ι | valid-α⁼ l' = α⁼-≤ l'
    τ-subtype-weaken Δ₁ Δ₂ Δ₃ int-≤ = int-≤
    τ-subtype-weaken Δ₁ Δ₂ Δ₃ ns-≤ = ns-≤
    τ-subtype-weaken Δ₁ Δ₂ Δ₃ {∀[ Δ ] Γ} (∀-≤ Γ₁≤Γ₂)
      rewrite sym (List-++-assoc Δ Δ₁ Δ₃)
      with Γ-subtype-weaken (Δ ++ Δ₁) Δ₂ Δ₃ Γ₁≤Γ₂
    ... | Γ₁'≤Γ₂'⋆
      rewrite List-++-assoc Δ Δ₁ (Δ₂ ++ Δ₃)
            | List-length-++ Δ {Δ₁} = ∀-≤ Γ₁'≤Γ₂'⋆
    τ-subtype-weaken Δ₁ Δ₂ Δ₃ (tuple-≤ τs⁻₁≤τs⁻₂) = tuple-≤ (τs⁻-subtype-weaken Δ₁ Δ₂ Δ₃ τs⁻₁≤τs⁻₂)

    τ⁻-subtype-weaken : subtype-weakenᵗ InitType
    τ⁻-subtype-weaken Δ₁ Δ₂ Δ₃ (τ⁻-≤ τ⋆ φ₁≤φ₂) = τ⁻-≤ (subst-valid-weaken Δ₁ Δ₂ Δ₃ τ⋆) φ₁≤φ₂

    τs⁻-subtype-weaken : subtype-weakenᵗ (List InitType)
    τs⁻-subtype-weaken Δ₁ Δ₂ Δ₃ [] = []
    τs⁻-subtype-weaken Δ₁ Δ₂ Δ₃ (τ⁻₁≤τ⁻₂ ∷ τs⁻₁≤τs⁻₂) = τ⁻-subtype-weaken Δ₁ Δ₂ Δ₃ τ⁻₁≤τ⁻₂ ∷ τs⁻-subtype-weaken Δ₁ Δ₂ Δ₃ τs⁻₁≤τs⁻₂

    σ-subtype-weaken : subtype-weakenᵗ StackType
    σ-subtype-weaken Δ₁ Δ₂ Δ₃ {ρ⁼ ι} (ρ⁼-≤ l)
      with (length Δ₁) ≤? ι | subst-valid-weaken Δ₁ Δ₂ Δ₃ (valid-ρ⁼ l)
    ... | yes len≤ι | valid-ρ⁼ l' = ρ⁼-≤ l'
    ... | no len≰ι | valid-ρ⁼ l' = ρ⁼-≤ l'
    σ-subtype-weaken Δ₁ Δ₂ Δ₃ [] = []
    σ-subtype-weaken Δ₁ Δ₂ Δ₃ (τ₁≤τ₂ ∷ σ₁≤σ₂) = τ-subtype-weaken Δ₁ Δ₂ Δ₃ τ₁≤τ₂ ∷ σ-subtype-weaken Δ₁ Δ₂ Δ₃ σ₁≤σ₂

    Γ-subtype-weaken : subtype-weakenᵗ RegisterAssignment
    Γ-subtype-weaken Δ₁ Δ₂ Δ₃ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂) = Γ-≤ (σ-subtype-weaken Δ₁ Δ₂ Δ₃ sp₁≤sp₂) (regs-subtype-weaken Δ₁ Δ₂ Δ₃ regs₁≤regs₂)

    regs-subtype-weaken : ∀ {n} → subtype-weakenᵗ (Vec Type n)
    regs-subtype-weaken Δ₁ Δ₂ Δ₃ [] = []
    regs-subtype-weaken Δ₁ Δ₂ Δ₃ (τ₁≤τ₂ ∷ τs₁≤τs₂) = τ-subtype-weaken Δ₁ Δ₂ Δ₃ τ₁≤τ₂ ∷ regs-subtype-weaken Δ₁ Δ₂ Δ₃ τs₁≤τs₂

  subtype-instᵗ :
    ∀ A {{_ : Substitution A}}
        {{_ : Subtype A}} → Set
  subtype-instᵗ A =
      ∀ Δ₁ {Δ₂ a i} →
        Δ₂ ⊢ i of a instantiation →
        {v₁ v₁' v₂ v₂' : A} →
        Δ₁ ++ a ∷ Δ₂ ⊢ v₁ ≤ v₂ →
        v₁ ⟦ i / length Δ₁ ⟧≡ v₁' →
        v₂ ⟦ i / length Δ₁ ⟧≡ v₂' →
        Δ₁ ++ Δ₂ ⊢ v₁' ≤ v₂'

  mutual
    τ-subtype-inst : subtype-instᵗ Type
    τ-subtype-inst Δ₁ i⋆ (α⁼-≤ l) sub-τ₁ sub-τ₂
      with subst-valid-inst Δ₁ i⋆ (valid-α⁼ l)
    ... | τ , sub-τ , τ⋆
      rewrite subst-unique sub-τ₂ sub-τ₁
            | subst-unique sub-τ sub-τ₁ = ≤-refl τ⋆
    τ-subtype-inst Δ₁ i⋆ int-≤ subst-int subst-int = int-≤
    τ-subtype-inst Δ₁ i⋆ ns-≤ subst-ns subst-ns = ns-≤
    τ-subtype-inst Δ₁ {Δ₂} {a} i⋆ {∀[ Δ ] Γ} (∀-≤ Γ₁≤Γ₂) (subst-∀ sub-Γ₁) (subst-∀ sub-Γ₂)
      rewrite sym (List-++-assoc Δ Δ₁ (a ∷ Δ₂))
            | sym (List-length-++ Δ {Δ₁})
      with Γ-subtype-inst (Δ ++ Δ₁) i⋆ Γ₁≤Γ₂ sub-Γ₁ sub-Γ₂
    ... | Γ₁'≤Γ₂'
      rewrite List-++-assoc Δ Δ₁ Δ₂
        = ∀-≤ Γ₁'≤Γ₂'
    τ-subtype-inst Δ₁ i⋆ (tuple-≤ τs⁻₁≤τs⁻₂) (subst-tuple sub-τs⁻₁) (subst-tuple sub-τs⁻₂) = tuple-≤ (τs⁻-subtype-inst Δ₁ i⋆ τs⁻₁≤τs⁻₂ sub-τs⁻₁ sub-τs⁻₂)

    τ⁻-subtype-inst : subtype-instᵗ InitType
    τ⁻-subtype-inst Δ₁ i⋆ (τ⁻-≤ τ⋆ φ₁≤φ₂) (subst-τ⁻ sub-τ₁) (subst-τ⁻ sub-τ₂)
      with subst-valid-inst Δ₁ i⋆ τ⋆
    ... | τ' , sub-τ , τ'⋆
      rewrite subst-unique sub-τ₂ sub-τ₁
            | subst-unique sub-τ sub-τ₁ = τ⁻-≤ τ'⋆ φ₁≤φ₂

    τs⁻-subtype-inst : subtype-instᵗ (List InitType)
    τs⁻-subtype-inst Δ₁ i⋆ [] [] [] = []
    τs⁻-subtype-inst Δ₁ i⋆ (τ⁻₁≤τ⁻₂ ∷ τs⁻₁≤τs⁻₂) (sub-τ⁻₁ ∷ sub-τs⁻₁) (sub-τ⁻₂ ∷ sub-τs⁻₂) =
      τ⁻-subtype-inst Δ₁ i⋆ τ⁻₁≤τ⁻₂ sub-τ⁻₁ sub-τ⁻₂ ∷ τs⁻-subtype-inst Δ₁ i⋆ τs⁻₁≤τs⁻₂ sub-τs⁻₁ sub-τs⁻₂

    σ-subtype-inst : subtype-instᵗ StackType
    σ-subtype-inst Δ₁ i⋆ (ρ⁼-≤ l) sub-σ₁ sub-σ₂
      with subst-valid-inst Δ₁ i⋆ (valid-ρ⁼ l)
    ... | σ , sub-σ , σ⋆
      rewrite subst-unique sub-σ₂ sub-σ₁
            | subst-unique sub-σ sub-σ₁ = ≤-refl σ⋆
    σ-subtype-inst Δ₁ i⋆ [] [] [] = []
    σ-subtype-inst Δ₁ i⋆ (τ₁≤τ₂ ∷ σ₁≤σ₂) (sub-τ₁ ∷ sub-σ₁) (sub-τ₂ ∷ sub-σ₂) =
      τ-subtype-inst Δ₁ i⋆ τ₁≤τ₂ sub-τ₁ sub-τ₂ ∷ σ-subtype-inst Δ₁ i⋆ σ₁≤σ₂ sub-σ₁ sub-σ₂

    Γ-subtype-inst : subtype-instᵗ RegisterAssignment
    Γ-subtype-inst Δ₁ i⋆ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂) (subst-registerₐ sub-sp₁ sub-regs₁) (subst-registerₐ sub-sp₂ sub-regs₂) =
      Γ-≤ (σ-subtype-inst Δ₁ i⋆ sp₁≤sp₂ sub-sp₁ sub-sp₂) (regs-subtype-inst Δ₁ i⋆ regs₁≤regs₂ sub-regs₁ sub-regs₂)

    regs-subtype-inst : ∀ {n} → subtype-instᵗ (Vec Type n)
    regs-subtype-inst Δ₁ i⋆ [] [] [] = []
    regs-subtype-inst Δ₁ i⋆ (τ₁≤τ₂ ∷ τs₁≤τs₂) (sub-τ₁ ∷ sub-τs₁) (sub-τ₂ ∷ sub-τs₂) =
      τ-subtype-inst Δ₁ i⋆ τ₁≤τ₂ sub-τ₁ sub-τ₂ ∷ regs-subtype-inst Δ₁ i⋆ τs₁≤τs₂ sub-τs₁ sub-τs₂

Vec-SubtypeSubstitution :
  ∀ A {S ST} {{SS : SubtypeSubstitution A {{S}} {{ST}}}} n →
    SubtypeSubstitution (Vec A n) {{Vec-Substitution A n}} {{Vec-Subtype A n}}
Vec-SubtypeSubstitution A {S} {ST} {{SS}} n = subtypeSubstitution xs-subtype-weaken xs-subtype-inst
  where xs-subtype-weaken : ∀ {n} → subtype-weakenᵗ (Vec A n) {{Vec-Substitution A n}} {{Vec-Subtype A n}}
        xs-subtype-weaken Δ₁ Δ₂ Δ₃ [] = []
        xs-subtype-weaken Δ₁ Δ₂ Δ₃ (x₁≤x₂ ∷ xs₁≤xs₂) =
          subst-subtype-weaken {{SS}} Δ₁ Δ₂ Δ₃ x₁≤x₂ ∷ xs-subtype-weaken Δ₁ Δ₂ Δ₃ xs₁≤xs₂

        xs-subtype-inst : ∀ {n} → subtype-instᵗ (Vec A n) {{Vec-Substitution A n}} {{Vec-Subtype A n}}
        xs-subtype-inst Δ₁ i⋆ [] [] [] = []
        xs-subtype-inst Δ₁ i⋆ (x₁≤x₂ ∷ xs₁≤xs₂) (sub-x₁ ∷ sub-xs₁) (sub-x₂ ∷ sub-xs₂) =
          subst-subtype-inst Δ₁ i⋆ x₁≤x₂ sub-x₁ sub-x₂ ∷ xs-subtype-inst Δ₁ i⋆ xs₁≤xs₂ sub-xs₁ sub-xs₂

List-SubtypeSubstitution :
  ∀ A {S ST} {{SS : SubtypeSubstitution A {{S}} {{ST}}}} →
    SubtypeSubstitution (List A) {{List-Substitution A}} {{List-Subtype A}}
List-SubtypeSubstitution A {S} {ST} {{SS}} = subtypeSubstitution xs-subtype-weaken xs-subtype-inst
  where xs-subtype-weaken : subtype-weakenᵗ (List A) {{List-Substitution A}} {{List-Subtype A}}
        xs-subtype-weaken Δ₁ Δ₂ Δ₃ [] = []
        xs-subtype-weaken Δ₁ Δ₂ Δ₃ (x₁≤x₂ ∷ xs₁≤xs₂) =
          subst-subtype-weaken {{SS}} Δ₁ Δ₂ Δ₃ x₁≤x₂ ∷ xs-subtype-weaken Δ₁ Δ₂ Δ₃ xs₁≤xs₂

        xs-subtype-inst : subtype-instᵗ (List A) {{List-Substitution A}} {{List-Subtype A}}
        xs-subtype-inst Δ₁ i⋆ [] [] [] = []
        xs-subtype-inst Δ₁ i⋆ (x₁≤x₂ ∷ xs₁≤xs₂) (sub-x₁ ∷ sub-xs₁) (sub-x₂ ∷ sub-xs₂) =
          subst-subtype-inst Δ₁ i⋆ x₁≤x₂ sub-x₁ sub-x₂ ∷ xs-subtype-inst Δ₁ i⋆ xs₁≤xs₂ sub-xs₁ sub-xs₂

instance
  Type-SubtypeSubstitution : SubtypeSubstitution Type
  Type-SubtypeSubstitution = subtypeSubstitution τ-subtype-weaken τ-subtype-inst

  TypeVec-SubtypeSubstitution : ∀ {m} → SubtypeSubstitution (Vec Type m)
  TypeVec-SubtypeSubstitution = subtypeSubstitution regs-subtype-weaken regs-subtype-inst

  TypeList-SubtypeSubstitution : SubtypeSubstitution (List Type)
  TypeList-SubtypeSubstitution = List-SubtypeSubstitution Type

  InitType-SubtypeSubstitution : SubtypeSubstitution InitType
  InitType-SubtypeSubstitution = subtypeSubstitution τ⁻-subtype-weaken τ⁻-subtype-inst

  InitTypeVec-SubtypeSubstitution :
    ∀ {m} → SubtypeSubstitution (Vec InitType m)
  InitTypeVec-SubtypeSubstitution = Vec-SubtypeSubstitution InitType _

  InitTypeList-SubtypeSubstitution : SubtypeSubstitution (List InitType)
  InitTypeList-SubtypeSubstitution = subtypeSubstitution τs⁻-subtype-weaken τs⁻-subtype-inst

  StackType-SubtypeSubstitution : SubtypeSubstitution StackType
  StackType-SubtypeSubstitution = subtypeSubstitution σ-subtype-weaken σ-subtype-inst

  RegisterAssignment-SubtypeSubstitution :
    SubtypeSubstitution RegisterAssignment
  RegisterAssignment-SubtypeSubstitution = subtypeSubstitution Γ-subtype-weaken Γ-subtype-inst
