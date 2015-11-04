module SubstitutionLemmas2 where

open import Util
open import Grammar
open import Subtyping
open import Substitution
open import SubstitutionLemmas
open import TypeJudgments
import Data.Nat.Properties as NP
import Algebra as A
open A.CommutativeSemiring NP.commutativeSemiring using (+-comm ; +-assoc)

private
  mutual
    subtypeᵗ : ∀ A {t} {{_ : Substitution A ℕ}}
                       {{_ : Subtype {A} t}} → Set
    subtypeᵗ A = ∀ {Δ Δ' c} {v₁ v₁' v₂ v₂' : A} →
                   Δ ⊢ c Valid →
                   Run Δ ⟦ c ⟧≡ Δ' →
                   Δ ⊢ v₁ ≤ v₂ →
                   v₁ ⟦ Strong→WeakCast c ⟧≡ v₁' →
                   v₂ ⟦ Strong→WeakCast c ⟧≡ v₂' →
                   Δ' ⊢ v₁' ≤ v₂'

    τ-subtype : subtypeᵗ Type
    τ-subtype c⋆ run-Δ (α⁼-≤ τ⋆) sub-τ₁ sub-τ₂
      rewrite subst-unique {W = ℕ} sub-τ₁ sub-τ₂ = ≤-refl (subst-valid c⋆ run-Δ τ⋆ sub-τ₂)
    τ-subtype c⋆ run-Δ int-≤ subst-int subst-int = int-≤
    τ-subtype c⋆ run-Δ ns-≤ subst-ns subst-ns = ns-≤
    τ-subtype {c = cᵥ / ι} {∀[ Δ ] Γ₁} c⋆ run-Δ (∀-≤ Δ⋆ Γ₁≤Γ₂) (subst-∀ sub-Δ₁ sub-Γ₁) (subst-∀ sub-Δ₂ sub-Γ₂)
      rewrite subst-unique {W = ℕ} sub-Δ₁ sub-Δ₂ = ∀-≤ (subst-valid c⋆ run-Δ Δ⋆ sub-Δ₂) (Γ-subtype (c-valid-add-left Δ c⋆) (run-combine sub-Δ₂ run-Δ) Γ₁≤Γ₂ sub-Γ₁ sub-Γ₂)
    τ-subtype c⋆ run-Δ (tuple-≤ τs⁻₁≤τs⁻₂) (subst-tuple sub-τs⁻₁) (subst-tuple sub-τs⁻₂) = tuple-≤ (τs⁻-subtype c⋆ run-Δ τs⁻₁≤τs⁻₂ sub-τs⁻₁ sub-τs⁻₂)

    τ⁻-subtype : subtypeᵗ InitType
    τ⁻-subtype c⋆ run-Δ (τ⁻-≤ τ⋆ φ₁≤φ₂) (subst-τ⁻ sub-τ₁) (subst-τ⁻ sub-τ₂)
      rewrite subst-unique {W = ℕ} sub-τ₁ sub-τ₂ = τ⁻-≤ (subst-valid c⋆ run-Δ τ⋆ sub-τ₂) φ₁≤φ₂

    τs⁻-subtype : subtypeᵗ (List InitType)
    τs⁻-subtype c⋆ run-Δ [] [] [] = []
    τs⁻-subtype c⋆ run-Δ (τ⁻₁≤τ⁻₂ ∷ τs⁻₁≤τs⁻₂) (sub-τ⁻₁ ∷ sub-τs⁻₁) (sub-τ⁻₂ ∷ sub-τs⁻₂) = τ⁻-subtype c⋆ run-Δ τ⁻₁≤τ⁻₂ sub-τ⁻₁ sub-τ⁻₂ ∷ τs⁻-subtype c⋆ run-Δ τs⁻₁≤τs⁻₂ sub-τs⁻₁ sub-τs⁻₂

    σ-subtype : subtypeᵗ StackType
    σ-subtype c⋆ run-Δ (ρ⁼-≤ σ⋆) sub-σ₁ sub-σ₂
      rewrite subst-unique {W = ℕ} sub-σ₁ sub-σ₂ = ≤-refl (subst-valid c⋆ run-Δ σ⋆ sub-σ₂)
    σ-subtype c⋆ run-Δ [] subst-[] subst-[] = []
    σ-subtype c⋆ run-Δ (τ₁≤τ₂ ∷ σ₁≤σ₂) (sub-τ₁ ∷ sub-σ₁) (sub-τ₂ ∷ sub-σ₂) = τ-subtype c⋆ run-Δ τ₁≤τ₂ sub-τ₁ sub-τ₂ ∷ σ-subtype c⋆ run-Δ σ₁≤σ₂ sub-σ₁ sub-σ₂

    Γ-subtype : subtypeᵗ RegisterAssignment
    Γ-subtype c⋆ run-Δ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂) (subst-registerₐ sub-sp₁ sub-regs₁) (subst-registerₐ sub-sp₂ sub-regs₂) = Γ-≤ (σ-subtype c⋆ run-Δ sp₁≤sp₂ sub-sp₁ sub-sp₂) (regs-subtype c⋆ run-Δ regs₁≤regs₂ sub-regs₁ sub-regs₂)

    regs-subtype : ∀ {m} → subtypeᵗ (Vec Type m)
    regs-subtype c⋆ run-Δ [] [] [] = []
    regs-subtype c⋆ run-Δ (τ₁≤τ₂ ∷ τs₁≤τs₂) (sub-τ₁ ∷ sub-τs₁) (sub-τ₂ ∷ sub-τs₂) = τ-subtype c⋆ run-Δ τ₁≤τ₂ sub-τ₁ sub-τ₂ ∷ regs-subtype c⋆ run-Δ τs₁≤τs₂ sub-τs₁ sub-τs₂

record Subtype⁺ (A : Set) t (_ : Substitution A ℕ) (_ : Subtype {A} t) : Set where
  constructor subtype⁺
  field
    valid-subtype :
      ∀ {Δ Δ' c} {v₁ v₁' v₂ v₂' : A} →
        Δ ⊢ c Valid →
        Run Δ ⟦ c ⟧≡ Δ' →
        Δ ⊢ v₁ ≤ v₂ →
        v₁ ⟦ Strong→WeakCast c ⟧≡ v₁' →
        v₂ ⟦ Strong→WeakCast c ⟧≡ v₂' →
        Δ' ⊢ v₁' ≤ v₂'

open Subtype⁺ {{...}} public

Vec-Subtype⁺ : ∀ {A t subs subt m} {{_ : Subtype⁺ A t subs subt}} →
                 Subtype⁺ (Vec A m) Vec-typeLike Vec-Substitution Vec-subtype
Vec-Subtype⁺ {A} {t} {subs} {subt} = subtype⁺ xs-subtype
  where xs-subtype : ∀ {m} → subtypeᵗ (Vec A m) {{Vec-Substitution}} {{Vec-subtype}}
        xs-subtype c⋆ run-Δ [] [] [] = []
        xs-subtype c⋆ run-Δ (x₁≤x₂ ∷ xs₁≤xs₂) (sub-x₁ ∷ sub-xs₁) (sub-x₂ ∷ sub-xs₂) =
          valid-subtype c⋆ run-Δ x₁≤x₂ sub-x₁ sub-x₂ ∷ xs-subtype c⋆ run-Δ xs₁≤xs₂ sub-xs₁ sub-xs₂

List-Subtype⁺ : ∀ {A t subs subt} {{_ : Subtype⁺ A t subs subt}} →
                  Subtype⁺ (List A) List-typeLike List-Substitution List-subtype
List-Subtype⁺ {A} {t} {subs} {subt} = subtype⁺ xs-subtype
  where xs-subtype : subtypeᵗ (List A) {{List-Substitution}} {{List-subtype}}
        xs-subtype c⋆ run-Δ [] [] [] = []
        xs-subtype c⋆ run-Δ (x₁≤x₂ ∷ xs₁≤xs₂) (sub-x₁ ∷ sub-xs₁) (sub-x₂ ∷ sub-xs₂) =
          valid-subtype c⋆ run-Δ x₁≤x₂ sub-x₁ sub-x₂ ∷ xs-subtype c⋆ run-Δ xs₁≤xs₂ sub-xs₁ sub-xs₂

instance
  Type-Subtype⁺ : Subtype⁺ Type Type-typeLike Type-Substitution Type-subtype
  Type-Subtype⁺ = subtype⁺ τ-subtype

  TypeVec-Subtype⁺ : ∀ {m} → Subtype⁺ (Vec Type m) TypeVec-typeLike TypeVec-Substitution TypeVec-subType
  TypeVec-Subtype⁺ = Vec-Subtype⁺

  TypeList-Subtype⁺ : Subtype⁺ (List Type) TypeList-typeLike TypeList-Substitution TypeList-subType
  TypeList-Subtype⁺ = List-Subtype⁺

  InitType-Subtype⁺ : Subtype⁺ InitType InitType-typeLike InitType-Substitution InitType-subtype
  InitType-Subtype⁺ = subtype⁺ τ⁻-subtype

  InitTypeVec-Subtype⁺ : ∀ {m} → Subtype⁺ (Vec InitType m) InitTypeVec-typeLike InitTypeVec-Substitution InitTypeVec-subType
  InitTypeVec-Subtype⁺ = Vec-Subtype⁺

  InitTypeList-Subtype⁺ : Subtype⁺ (List InitType) InitTypeList-typeLike InitTypeList-Substitution InitTypeList-subType
  InitTypeList-Subtype⁺ = List-Subtype⁺

  StackType-Subtype⁺ : Subtype⁺ StackType StackType-typeLike StackType-Substitution StackType-subtype
  StackType-Subtype⁺ = subtype⁺ σ-subtype

  RegisterAssignment-Subtype⁺ : Subtype⁺ RegisterAssignment RegisterAssignment-typeLike RegisterAssignment-Substitution RegisterAssignment-subtype
  RegisterAssignment-Subtype⁺ = subtype⁺ Γ-subtype
