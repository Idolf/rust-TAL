module Lemmas.SubtypeSubstitution where

open import Util
open import Judgments
open import Lemmas.Misc
open import Lemmas.Subtypes
open import Lemmas.Substitution
open import Lemmas.TypeSubstitution

-- The purpose of this file is to create instance
-- of the following record:
record SubtypeSubstitution (A : Set) {{S : Substitution A}}
                                     {{ST : Subtype A}} : Set where
  constructor subtypeSubstitution
  field
    valid-subtype :
      ∀ {Δ Δ' cᵥ ι} {v₁ v₁' v₂ v₂' : A} →
        Δ ⊢ cᵥ / ι Valid →
        Run Δ ⟦ cᵥ / ι ⟧≡ Δ' →
        Δ ⊢ v₁ ≤ v₂ →
        v₁ ⟦ Strong→Weak cᵥ / ι ⟧≡ v₁' →
        v₂ ⟦ Strong→Weak cᵥ / ι ⟧≡ v₂' →
        Δ' ⊢ v₁' ≤ v₂'
open SubtypeSubstitution {{...}} public

private
  mutual
    subtypeᵗ : ∀ A {{_ : Substitution A}}
                   {{_ : Subtype A}} → Set
    subtypeᵗ A = ∀ {Δ Δ' cᵥ ι} {v₁ v₁' v₂ v₂' : A} →
                   Δ ⊢ cᵥ / ι Valid →
                   Run Δ ⟦ cᵥ / ι ⟧≡ Δ' →
                   Δ ⊢ v₁ ≤ v₂ →
                   v₁ ⟦ Strong→Weak cᵥ / ι ⟧≡ v₁' →
                   v₂ ⟦ Strong→Weak cᵥ / ι ⟧≡ v₂' →
                   Δ' ⊢ v₁' ≤ v₂'

    τ-subtype : subtypeᵗ Type
    τ-subtype c⋆ run-Δ (α⁼-≤ l) sub-τ₁ sub-τ₂
      rewrite subst-unique sub-τ₁ sub-τ₂ =
        ≤-refl (subst-valid c⋆ run-Δ (valid-α⁼ l) sub-τ₂)
    τ-subtype c⋆ run-Δ int-≤ subst-int subst-int = int-≤
    τ-subtype c⋆ run-Δ ns-≤ subst-ns subst-ns = ns-≤
    τ-subtype {v₁ = ∀[ Δ ] Γ₁} c⋆ run-Δ (∀-≤ Δ⋆ Γ₁≤Γ₂)
      (subst-∀ sub-Δ₁ sub-Γ₁) (subst-∀ sub-Δ₂ sub-Γ₂)
      rewrite subst-unique sub-Δ₁ sub-Δ₂ =
        ∀-≤ (subst-valid c⋆ run-Δ Δ⋆ sub-Δ₂)
            (Γ-subtype (c-valid-add-left Δ c⋆)
              (run-combine sub-Δ₂ run-Δ) Γ₁≤Γ₂ sub-Γ₁ sub-Γ₂)
    τ-subtype c⋆ run-Δ (tuple-≤ τs⁻₁≤τs⁻₂)
      (subst-tuple sub-τs⁻₁) (subst-tuple sub-τs⁻₂) =
        tuple-≤ (τs⁻-subtype c⋆ run-Δ τs⁻₁≤τs⁻₂ sub-τs⁻₁ sub-τs⁻₂)

    τ⁻-subtype : subtypeᵗ InitType
    τ⁻-subtype c⋆ run-Δ (τ⁻-≤ τ⋆ φ₁≤φ₂) (subst-τ⁻ sub-τ₁) (subst-τ⁻ sub-τ₂)
      rewrite subst-unique sub-τ₁ sub-τ₂ =
        τ⁻-≤ (subst-valid c⋆ run-Δ τ⋆ sub-τ₂) φ₁≤φ₂

    τs⁻-subtype : subtypeᵗ (List InitType)
    τs⁻-subtype c⋆ run-Δ [] [] [] = []
    τs⁻-subtype c⋆ run-Δ (τ⁻₁≤τ⁻₂ ∷ τs⁻₁≤τs⁻₂)
      (sub-τ⁻₁ ∷ sub-τs⁻₁) (sub-τ⁻₂ ∷ sub-τs⁻₂) =
        τ⁻-subtype c⋆ run-Δ τ⁻₁≤τ⁻₂ sub-τ⁻₁ sub-τ⁻₂ ∷
        τs⁻-subtype c⋆ run-Δ τs⁻₁≤τs⁻₂ sub-τs⁻₁ sub-τs⁻₂

    σ-subtype : subtypeᵗ StackType
    σ-subtype c⋆ run-Δ (ρ⁼-≤ l) sub-σ₁ sub-σ₂
      rewrite subst-unique sub-σ₁ sub-σ₂ =
        ≤-refl (subst-valid c⋆ run-Δ (valid-ρ⁼ l) sub-σ₂)
    σ-subtype c⋆ run-Δ [] subst-[] subst-[] = []
    σ-subtype c⋆ run-Δ (τ₁≤τ₂ ∷ σ₁≤σ₂)
      (sub-τ₁ ∷ sub-σ₁) (sub-τ₂ ∷ sub-σ₂) =
        τ-subtype c⋆ run-Δ τ₁≤τ₂ sub-τ₁ sub-τ₂ ∷
        σ-subtype c⋆ run-Δ σ₁≤σ₂ sub-σ₁ sub-σ₂

    Γ-subtype : subtypeᵗ RegisterAssignment
    Γ-subtype c⋆ run-Δ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
      (subst-registerₐ sub-sp₁ sub-regs₁)
      (subst-registerₐ sub-sp₂ sub-regs₂) =
        Γ-≤ (σ-subtype c⋆ run-Δ sp₁≤sp₂ sub-sp₁ sub-sp₂)
            (regs-subtype c⋆ run-Δ regs₁≤regs₂ sub-regs₁ sub-regs₂)

    regs-subtype : ∀ {m} → subtypeᵗ (Vec Type m)
    regs-subtype c⋆ run-Δ [] [] [] = []
    regs-subtype c⋆ run-Δ (τ₁≤τ₂ ∷ τs₁≤τs₂)
      (sub-τ₁ ∷ sub-τs₁) (sub-τ₂ ∷ sub-τs₂) =
        τ-subtype c⋆ run-Δ τ₁≤τ₂ sub-τ₁ sub-τ₂ ∷
        regs-subtype c⋆ run-Δ τs₁≤τs₂ sub-τs₁ sub-τs₂

Vec-SubtypeSubstitution :
  ∀ A {S ST} {{_ : SubtypeSubstitution A {{S}} {{ST}}}} m →
    SubtypeSubstitution (Vec A m) {{Vec-Substitution A m}} {{Vec-Subtype A m}}
Vec-SubtypeSubstitution A {S} {ST} m = subtypeSubstitution xs-subtype
  where xs-subtype : ∀ {m} → subtypeᵗ (Vec A m)
                             {{Vec-Substitution A m}} {{Vec-Subtype A m}}
        xs-subtype c⋆ run-Δ [] [] [] = []
        xs-subtype c⋆ run-Δ (x₁≤x₂ ∷ xs₁≤xs₂)
          (sub-x₁ ∷ sub-xs₁) (sub-x₂ ∷ sub-xs₂) =
            valid-subtype c⋆ run-Δ x₁≤x₂ sub-x₁ sub-x₂ ∷
            xs-subtype c⋆ run-Δ xs₁≤xs₂ sub-xs₁ sub-xs₂

List-SubtypeSubstitution :
  ∀ A {S ST} {{_ : SubtypeSubstitution A {{S}} {{ST}}}} →
    SubtypeSubstitution (List A) {{List-Substitution A}} {{List-Subtype A}}
List-SubtypeSubstitution A {S} {ST} = subtypeSubstitution xs-subtype
  where xs-subtype : subtypeᵗ (List A)
                     {{List-Substitution A}} {{List-Subtype A}}
        xs-subtype c⋆ run-Δ [] [] [] = []
        xs-subtype c⋆ run-Δ (x₁≤x₂ ∷ xs₁≤xs₂)
          (sub-x₁ ∷ sub-xs₁) (sub-x₂ ∷ sub-xs₂) =
            valid-subtype c⋆ run-Δ x₁≤x₂ sub-x₁ sub-x₂ ∷
            xs-subtype c⋆ run-Δ xs₁≤xs₂ sub-xs₁ sub-xs₂

instance
  Type-SubtypeSubstitution : SubtypeSubstitution Type
  Type-SubtypeSubstitution = subtypeSubstitution τ-subtype

  TypeVec-SubtypeSubstitution : ∀ {m} → SubtypeSubstitution (Vec Type m)
  TypeVec-SubtypeSubstitution = Vec-SubtypeSubstitution Type _

  TypeList-SubtypeSubstitution : SubtypeSubstitution (List Type)
  TypeList-SubtypeSubstitution = List-SubtypeSubstitution Type

  InitType-SubtypeSubstitution : SubtypeSubstitution InitType
  InitType-SubtypeSubstitution = subtypeSubstitution τ⁻-subtype

  InitTypeVec-SubtypeSubstitution :
    ∀ {m} → SubtypeSubstitution (Vec InitType m)
  InitTypeVec-SubtypeSubstitution = Vec-SubtypeSubstitution InitType _

  InitTypeList-SubtypeSubstitution : SubtypeSubstitution (List InitType)
  InitTypeList-SubtypeSubstitution = List-SubtypeSubstitution InitType

  StackType-SubtypeSubstitution : SubtypeSubstitution StackType
  StackType-SubtypeSubstitution = subtypeSubstitution σ-subtype

  RegisterAssignment-SubtypeSubstitution :
    SubtypeSubstitution RegisterAssignment
  RegisterAssignment-SubtypeSubstitution = subtypeSubstitution Γ-subtype
