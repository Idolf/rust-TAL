module Lemmas.SubtypeSubstitution where

open import Util
open import Judgments
open import Lemmas.Subtypes
open import Lemmas.Substitution
open import Lemmas.TypeSubstitution

import Data.Nat.Properties as NP

-- The purpose of this file is to create instance
-- of the following record:
record SubtypeSubstitution (A : Set) {S} {{S⁺ : Substitution⁺ A {{S}}}}
                                     {{ST : Subtype A}} : Set where
  constructor subtypeSubstitution
  field
    subtype-weaken :
      ∀ Δ₁ Δ₂ Δ₃ →
        {v₁ v₂ : A} →
        Δ₁ ++ Δ₃ ⊢ v₁ ≤ v₂ →
        Δ₁ ++ Δ₂ ++ Δ₃ ⊢ weaken (length Δ₁) (length Δ₂) v₁ ≤ weaken (length Δ₁) (length Δ₂) v₂
    subtype-subst-exists :
      ∀ Δ₁ {Δ₂ a i} →
        Δ₂ ⊢ i of a instantiation →
        {v₁ v₂ : A} →
        Δ₁ ++ a ∷ Δ₂ ⊢ v₁ ≤ v₂ →
        ∃₂ λ v₁' v₂' →
          v₁ ⟦ i / length Δ₁ ⟧≡ v₁' ×
          v₂ ⟦ i / length Δ₁ ⟧≡ v₂' ×
          Δ₁ ++ Δ₂ ⊢ v₁' ≤ v₂'
    subtype-pre-exists :
      ∀ Δ₁ {Δ₂ a i} →
        Δ₂ ⊢ i of a instantiation →
        {v₁' v₂' : A} →
        Δ₁ ++ Δ₂ ⊢ v₁' ≤ v₂' →
        ∃₂ λ v₁ v₂ →
          v₁ ⟦ i / length Δ₁ ⟧≡ v₁' ×
          v₂ ⟦ i / length Δ₁ ⟧≡ v₂' ×
          Δ₁ ++ a ∷ Δ₂ ⊢ v₁ ≤ v₂

  subtype-subst-exists-many :
    ∀ Δ₁ {Δ₂ Δ₃ is} →
      Δ₃ ⊢ is of Δ₂ instantiations →
      {v₁ v₂ : A} →
      Δ₁ ++ Δ₂ ++ Δ₃ ⊢ v₁ ≤ v₂ →
      ∃₂ λ v₁' v₂' →
        v₁ ⟦ is / length Δ₁ ⟧many≡ v₁' ×
        v₂ ⟦ is / length Δ₁ ⟧many≡ v₂' ×
        Δ₁ ++ Δ₃ ⊢ v₁' ≤ v₂'
  subtype-subst-exists-many Δ₁ [] v₁≤v₂ = _ , _ , [] , [] , v₁≤v₂
  subtype-subst-exists-many Δ₁ {a ∷ Δ₂} {Δ₃} (i⋆ ∷ is⋆) v₁≤v₂
    rewrite sym (List-++-assoc Δ₁ ([ a ]) (Δ₂ ++ Δ₃))
    with subtype-subst-exists-many (Δ₁ ++ [ a ]) {Δ₂} {Δ₃} is⋆ v₁≤v₂
  ... | v₁' , v₂' , subs-v₁ , subs-v₂ , v₁'≤v₂'
    rewrite List-++-assoc Δ₁ ([ a ]) Δ₃
    with subtype-subst-exists Δ₁ i⋆ v₁'≤v₂'
  ... | v₁ₑ , v₂ₑ , sub-v₁ , sub-v₂ , v₁ₑ≤v₂ₑ
    rewrite List-length-++ Δ₁ {[ a ]}
          | +-comm (length Δ₁) 1
    = v₁ₑ , v₂ₑ , sub-v₁ ∷ subs-v₁ , sub-v₂ ∷ subs-v₂ , v₁ₑ≤v₂ₑ

  subtype-pre-exists-many :
    ∀ Δ₁ {Δ₂ Δ₃ is} →
      Δ₃ ⊢ is of Δ₂ instantiations →
      {v₁' v₂' : A} →
      Δ₁ ++ Δ₃ ⊢ v₁' ≤ v₂' →
      ∃₂ λ v₁ v₂ →
        v₁ ⟦ is / length Δ₁ ⟧many≡ v₁' ×
        v₂ ⟦ is / length Δ₁ ⟧many≡ v₂' ×
        Δ₁ ++ Δ₂ ++ Δ₃ ⊢ v₁ ≤ v₂
  subtype-pre-exists-many Δ₁ [] v₁ₑ≤v₂ₑ = _ , _ , [] , [] , v₁ₑ≤v₂ₑ
  subtype-pre-exists-many Δ₁ {a ∷ Δ₂} {Δ₃} (i⋆ ∷ is⋆) v₁ₑ≤v₂ₑ
    with subtype-pre-exists Δ₁ i⋆ v₁ₑ≤v₂ₑ
  ... | v₁' , v₂' , sub-v₁ , sub-v₂ , v₁'≤v₂'
    rewrite sym (List-++-assoc Δ₁ ([ a ]) Δ₃)
    with subtype-pre-exists-many (Δ₁ ++ [ a ]) {Δ₂} {Δ₃} is⋆ v₁'≤v₂'
  ... | v₁ , v₂ , subs-v₁ , subs-v₂ , v₁≤v₂
    rewrite List-length-++ Δ₁ {[ a ]}
          | +-comm (length Δ₁) 1
          | List-++-assoc Δ₁ ([ a ]) (Δ₂ ++ Δ₃)
    = v₁ , v₂ , sub-v₁ ∷ subs-v₁ , sub-v₂ ∷ subs-v₂ , v₁≤v₂

  subtype-subst :
    ∀ Δ₁ {Δ₂ a i} →
      Δ₂ ⊢ i of a instantiation →
      {v₁ v₁' v₂ v₂' : A} →
      Δ₁ ++ a ∷ Δ₂ ⊢ v₁ ≤ v₂ →
      v₁ ⟦ i / length Δ₁ ⟧≡ v₁' →
      v₂ ⟦ i / length Δ₁ ⟧≡ v₂' →
      Δ₁ ++ Δ₂ ⊢ v₁' ≤ v₂'
  subtype-subst Δ₁ i⋆ v₁≤v₂ sub-v₁ sub-v₂
    with subtype-subst-exists Δ₁ i⋆ v₁≤v₂
  ... | v₁'' , v₂'' , sub-v₁' , sub-v₂' , v₁''≤v₂''
    rewrite subst-unique sub-v₁ sub-v₁'
          | subst-unique sub-v₂ sub-v₂' = v₁''≤v₂''

  subtype-subst-many :
      ∀ Δ₁ {Δ₂ Δ₃ is} →
        Δ₃ ⊢ is of Δ₂ instantiations →
        {v₁ v₁' v₂ v₂' : A} →
        Δ₁ ++ Δ₂ ++ Δ₃ ⊢ v₁ ≤ v₂ →
        v₁ ⟦ is / length Δ₁ ⟧many≡ v₁' →
        v₂ ⟦ is / length Δ₁ ⟧many≡ v₂' →
        Δ₁ ++ Δ₃ ⊢ v₁' ≤ v₂'
  subtype-subst-many Δ₁ [] v₁≤v₂ [] [] = v₁≤v₂
  subtype-subst-many Δ₁ {a ∷ Δ₂} {Δ₃} (i⋆ ∷ is⋆) v₁≤v₂ (sub-v₁ ∷ subs-v₁) (sub-v₂ ∷ subs-v₂)
    rewrite sym (List-++-assoc Δ₁ ([ a ]) (Δ₂ ++ Δ₃))
          | +-comm 1 (length Δ₁)
          | sym (List-length-++ Δ₁ {[ a ]})
    with subtype-subst-many (Δ₁ ++ [ a ]) {Δ₂} {Δ₃} is⋆ v₁≤v₂ subs-v₁ subs-v₂
  ... | v₁'≤v₂'
    rewrite List-++-assoc Δ₁ ([ a ]) Δ₃
    = subtype-subst Δ₁ i⋆ v₁'≤v₂' sub-v₁ sub-v₂

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
      with (length Δ₁) ≤? ι | valid-weaken Δ₁ Δ₂ Δ₃ (valid-α⁼ l)
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
    τ⁻-subtype-weaken Δ₁ Δ₂ Δ₃ (τ⁻-≤ τ⋆ φ₁≤φ₂) = τ⁻-≤ (valid-weaken Δ₁ Δ₂ Δ₃ τ⋆) φ₁≤φ₂

    τs⁻-subtype-weaken : subtype-weakenᵗ (List InitType)
    τs⁻-subtype-weaken Δ₁ Δ₂ Δ₃ [] = []
    τs⁻-subtype-weaken Δ₁ Δ₂ Δ₃ (τ⁻₁≤τ⁻₂ ∷ τs⁻₁≤τs⁻₂) = τ⁻-subtype-weaken Δ₁ Δ₂ Δ₃ τ⁻₁≤τ⁻₂ ∷ τs⁻-subtype-weaken Δ₁ Δ₂ Δ₃ τs⁻₁≤τs⁻₂

    σ-subtype-weaken : subtype-weakenᵗ StackType
    σ-subtype-weaken Δ₁ Δ₂ Δ₃ {ρ⁼ ι} (ρ⁼-≤ l)
      with (length Δ₁) ≤? ι | valid-weaken Δ₁ Δ₂ Δ₃ (valid-ρ⁼ l)
    ... | yes len≤ι | valid-ρ⁼ l' = ρ⁼-≤ l'
    ... | no len≰ι | valid-ρ⁼ l' = ρ⁼-≤ l'
    σ-subtype-weaken Δ₁ Δ₂ Δ₃ [] = []
    σ-subtype-weaken Δ₁ Δ₂ Δ₃ (τ₁≤τ₂ ∷ σ₁≤σ₂) = τ-subtype-weaken Δ₁ Δ₂ Δ₃ τ₁≤τ₂ ∷ σ-subtype-weaken Δ₁ Δ₂ Δ₃ σ₁≤σ₂

    Γ-subtype-weaken : subtype-weakenᵗ RegisterAssignment
    Γ-subtype-weaken Δ₁ Δ₂ Δ₃ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂) = Γ-≤ (σ-subtype-weaken Δ₁ Δ₂ Δ₃ sp₁≤sp₂) (regs-subtype-weaken Δ₁ Δ₂ Δ₃ regs₁≤regs₂)

    regs-subtype-weaken : ∀ {n} → subtype-weakenᵗ (Vec Type n)
    regs-subtype-weaken Δ₁ Δ₂ Δ₃ [] = []
    regs-subtype-weaken Δ₁ Δ₂ Δ₃ (τ₁≤τ₂ ∷ τs₁≤τs₂) = τ-subtype-weaken Δ₁ Δ₂ Δ₃ τ₁≤τ₂ ∷ regs-subtype-weaken Δ₁ Δ₂ Δ₃ τs₁≤τs₂
  subtype-subst-existsᵗ :
    ∀ A {{_ : Substitution A}}
        {{_ : Subtype A}} → Set
  subtype-subst-existsᵗ A =
      ∀ Δ₁ {Δ₂ a i} →
        Δ₂ ⊢ i of a instantiation →
        {v₁ v₂ : A} →
        Δ₁ ++ a ∷ Δ₂ ⊢ v₁ ≤ v₂ →
        ∃₂ λ v₁' v₂' →
          v₁ ⟦ i / length Δ₁ ⟧≡ v₁' ×
          v₂ ⟦ i / length Δ₁ ⟧≡ v₂' ×
          Δ₁ ++ Δ₂ ⊢ v₁' ≤ v₂'

  mutual
    τ-subtype-subst-exists : subtype-subst-existsᵗ Type
    τ-subtype-subst-exists Δ₁ i⋆ (α⁼-≤ l)
      with valid-subst-exists Δ₁ i⋆ (valid-α⁼ l)
    ... | τ' , sub-τ , τ'⋆ = τ' , τ' , sub-τ , sub-τ , ≤-refl τ'⋆
    τ-subtype-subst-exists Δ₁ i⋆ int-≤ = int , int , subst-int , subst-int , int-≤
    τ-subtype-subst-exists Δ₁ i⋆ ns-≤ = ns , ns , subst-ns , subst-ns , ns-≤
    τ-subtype-subst-exists Δ₁ {Δ₂} {a} i⋆ {∀[ Δ ] Γ} (∀-≤ Γ₂≤Γ₁)
      rewrite sym (List-++-assoc Δ Δ₁ (a ∷ Δ₂))
      with Γ-subtype-subst-exists (Δ ++ Δ₁) i⋆ Γ₂≤Γ₁
    ... | Γ₂' , Γ₁' , sub-Γ₂ , sub-Γ₁ , Γ₂'≤Γ₁'
      rewrite List-length-++ Δ {Δ₁}
            | List-++-assoc Δ Δ₁ Δ₂ =
        _ , _ , subst-∀ sub-Γ₁ , subst-∀ sub-Γ₂ , ∀-≤ Γ₂'≤Γ₁'
    τ-subtype-subst-exists Δ₁ i⋆ (tuple-≤ τs⁻₁≤τs⁻₂)
      with τs⁻-subtype-subst-exists Δ₁ i⋆ τs⁻₁≤τs⁻₂
    ... | τs⁻₁' , τs⁻₂' , sub-τs⁻₁ , sub-τs⁻₂ , τs⁻₁'≤τs⁻₂'
      = _ , _ , subst-tuple sub-τs⁻₁ , subst-tuple sub-τs⁻₂ , tuple-≤ τs⁻₁'≤τs⁻₂'

    τ⁻-subtype-subst-exists : subtype-subst-existsᵗ InitType
    τ⁻-subtype-subst-exists Δ₁ i⋆ (τ⁻-≤ τ⋆ φ₁≤φ₂)
      with valid-subst-exists Δ₁ i⋆ τ⋆
    ... | τ' , sub-τ , τ'⋆ = _ , _ , subst-τ⁻ sub-τ , subst-τ⁻ sub-τ , τ⁻-≤ τ'⋆ φ₁≤φ₂

    τs⁻-subtype-subst-exists : subtype-subst-existsᵗ (List InitType)
    τs⁻-subtype-subst-exists Δ₁ i⋆ [] = [] , [] , [] , [] , []
    τs⁻-subtype-subst-exists Δ₁ i⋆ (τ⁻₁≤τ⁻₂ ∷ τs⁻₁≤τs⁻₂)
      with τ⁻-subtype-subst-exists Δ₁ i⋆ τ⁻₁≤τ⁻₂
    ... | τ⁻₁' , τ⁻₂' , sub-τ⁻₁ , sub-τ⁻₂ , τ⁻₁'≤τ⁻₂'
      with τs⁻-subtype-subst-exists Δ₁ i⋆ τs⁻₁≤τs⁻₂
    ... | τs⁻₁' , τs⁻₂' , sub-τs⁻₁ , sub-τs⁻₂ , τs⁻₁'≤τs⁻₂'
      = _ , _ , sub-τ⁻₁ ∷ sub-τs⁻₁ , sub-τ⁻₂ ∷ sub-τs⁻₂ , τ⁻₁'≤τ⁻₂' ∷ τs⁻₁'≤τs⁻₂'

    σ-subtype-subst-exists : subtype-subst-existsᵗ StackType
    σ-subtype-subst-exists Δ₁ i⋆ (ρ⁼-≤ l)
      with valid-subst-exists Δ₁ i⋆ (valid-ρ⁼ l)
    ... | τ' , sub-τ , τ'⋆ = τ' , τ' , sub-τ , sub-τ , ≤-refl τ'⋆
    σ-subtype-subst-exists Δ₁ i⋆ [] = [] , [] , [] , [] , []
    σ-subtype-subst-exists Δ₁ i⋆ (τ₁≤τ₂ ∷ σ₁≤σ₂)
      with τ-subtype-subst-exists Δ₁ i⋆ τ₁≤τ₂
    ... | τ₁' , τ₂' , sub-τ₁ , sub-τ₂ , τ₁'≤τ₂'
      with σ-subtype-subst-exists Δ₁ i⋆ σ₁≤σ₂
    ... | σ₁' , σ₂' , sub-σ₁ , sub-σ₂ , σ₁'≤σ₂'
      = _ , _ , sub-τ₁ ∷ sub-σ₁ , sub-τ₂ ∷ sub-σ₂ , τ₁'≤τ₂' ∷ σ₁'≤σ₂'

    Γ-subtype-subst-exists : subtype-subst-existsᵗ RegisterAssignment
    Γ-subtype-subst-exists Δ₁ i⋆ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
      with σ-subtype-subst-exists Δ₁ i⋆ sp₁≤sp₂
    ... | sp₁' , sp₂' , sub-sp₁ , sub-sp₂ , sp₁'≤sp₂'
      with regs-subtype-subst-exists Δ₁ i⋆ regs₁≤regs₂
    ... | regs₁' , regs₂' , sub-regs₁ , sub-regs₂ , regs₁'≤regs₂'
      = _ , _ ,
        subst-registerₐ sub-sp₁ sub-regs₁ ,
        subst-registerₐ sub-sp₂ sub-regs₂ ,
        Γ-≤ sp₁'≤sp₂' regs₁'≤regs₂'

    regs-subtype-subst-exists : ∀ {n} → subtype-subst-existsᵗ (Vec Type n)
    regs-subtype-subst-exists Δ₁ i⋆ [] = [] , [] , [] , [] , []
    regs-subtype-subst-exists Δ₁ i⋆ (τ₁≤τ₂ ∷ τs₁≤τs₂)
      with τ-subtype-subst-exists Δ₁ i⋆ τ₁≤τ₂
    ... | τ₁' , τ₂' , sub-τ₁ , sub-τ₂ , τ₁'≤τ₂'
      with regs-subtype-subst-exists Δ₁ i⋆ τs₁≤τs₂
    ... | τs₁' , τs₂' , sub-τs₁ , sub-τs₂ , τs₁'≤τs₂'
      = _ , _ , sub-τ₁ ∷ sub-τs₁ , sub-τ₂ ∷ sub-τs₂ , τ₁'≤τ₂' ∷ τs₁'≤τs₂'
  subtype-pre-existsᵗ :
    ∀ A {{_ : Substitution A}}
        {{_ : Subtype A}} → Set
  subtype-pre-existsᵗ A =
      ∀ Δ₁ {Δ₂ a i} →
        Δ₂ ⊢ i of a instantiation →
        {v₁' v₂' : A} →
        Δ₁ ++ Δ₂ ⊢ v₁' ≤ v₂' →
        ∃₂ λ v₁ v₂ →
          v₁ ⟦ i / length Δ₁ ⟧≡ v₁' ×
          v₂ ⟦ i / length Δ₁ ⟧≡ v₂' ×
          Δ₁ ++ a ∷ Δ₂ ⊢ v₁ ≤ v₂

  mutual
    τ-subtype-pre-exists : subtype-pre-existsᵗ Type
    τ-subtype-pre-exists Δ₁ {Δ₂} {a} i⋆ {α⁼ ι} (α⁼-≤ l)
      with valid-pre-exists Δ₁ i⋆ (valid-α⁼ l)
    ... | τ , sub-τ , τ⋆ = τ , τ , sub-τ , sub-τ , ≤-refl τ⋆
    τ-subtype-pre-exists Δ₁ i⋆ int-≤ = int , int , subst-int , subst-int , int-≤
    τ-subtype-pre-exists Δ₁ i⋆ ns-≤ = ns , ns , subst-ns , subst-ns , ns-≤
    τ-subtype-pre-exists Δ₁ {Δ₂} {a} i⋆ {∀[ Δ ] Γ₁'} (∀-≤ Γ₂'≤Γ₁')
      rewrite sym (List-++-assoc Δ Δ₁ Δ₂)
      with Γ-subtype-pre-exists (Δ ++ Δ₁) i⋆ Γ₂'≤Γ₁'
    ... | Γ₂ , Γ₁ , sub-Γ₂ , sub-Γ₁ , Γ₂≤Γ₁
      rewrite List-++-assoc Δ Δ₁ (a ∷ Δ₂)
            | List-length-++ Δ {Δ₁}
        = ∀[ Δ ] Γ₁ , ∀[ Δ ] Γ₂ , subst-∀ sub-Γ₁ , subst-∀ sub-Γ₂ , ∀-≤ Γ₂≤Γ₁
    τ-subtype-pre-exists Δ₁ i⋆ (tuple-≤ τs⁻₁'≤τs⁻₂')
      with τs⁻-subtype-pre-exists Δ₁ i⋆ τs⁻₁'≤τs⁻₂'
    ... | τs⁻₁ , τs⁻₂ , sub-τs⁻₁ , sub-τs⁻₂ , τs⁻₁≤τs⁻₂
      = tuple τs⁻₁ , tuple τs⁻₂ , subst-tuple sub-τs⁻₁ , subst-tuple sub-τs⁻₂ , tuple-≤ τs⁻₁≤τs⁻₂

    τ⁻-subtype-pre-exists : subtype-pre-existsᵗ InitType
    τ⁻-subtype-pre-exists Δ₁ i⋆ (τ⁻-≤ τ'⋆ φ₁'≤φ₂')
      with valid-pre-exists Δ₁ i⋆ τ'⋆
    ... | τ , sub-τ , τ⋆ = _ , _ , subst-τ⁻ sub-τ , subst-τ⁻ sub-τ , τ⁻-≤ τ⋆ φ₁'≤φ₂'

    τs⁻-subtype-pre-exists : subtype-pre-existsᵗ (List InitType)
    τs⁻-subtype-pre-exists Δ₁ i⋆ [] = [] , [] , [] , [] , []
    τs⁻-subtype-pre-exists Δ₁ i⋆ (τ⁻₁'≤τ⁻₂' ∷ τs⁻₁'≤τs⁻₂')
      with τ⁻-subtype-pre-exists Δ₁ i⋆ τ⁻₁'≤τ⁻₂'
    ... | τ⁻₁ , τ⁻₂ , sub-τ⁻₁ , sub-τ⁻₂ , τ⁻₁≤τ⁻₂
      with τs⁻-subtype-pre-exists Δ₁ i⋆ τs⁻₁'≤τs⁻₂'
    ... | τs⁻₁ , τs⁻₂ , sub-τs⁻₁ , sub-τs⁻₂ , τs⁻₁≤τs⁻₂
      = τ⁻₁ ∷ τs⁻₁ , τ⁻₂ ∷ τs⁻₂ , sub-τ⁻₁ ∷ sub-τs⁻₁ , sub-τ⁻₂ ∷ sub-τs⁻₂ , τ⁻₁≤τ⁻₂ ∷ τs⁻₁≤τs⁻₂

    σ-subtype-pre-exists : subtype-pre-existsᵗ StackType
    σ-subtype-pre-exists Δ₁ {Δ₂} {a} i⋆ {ρ⁼ ι} (ρ⁼-≤ l)
      with valid-pre-exists Δ₁ i⋆ (valid-ρ⁼ l)
    ... | σ , sub-σ , σ⋆ = σ , σ , sub-σ , sub-σ , ≤-refl σ⋆
    σ-subtype-pre-exists Δ₁ i⋆ [] = [] , [] , [] , [] , []
    σ-subtype-pre-exists Δ₁ i⋆ (τ₁'≤τ₂' ∷ σ₁'≤σ₂')
      with τ-subtype-pre-exists Δ₁ i⋆ τ₁'≤τ₂'
    ... | τ₁ , τ₂ , sub-τ₁ , sub-τ₂ , τ₁≤τ₂
      with σ-subtype-pre-exists Δ₁ i⋆ σ₁'≤σ₂'
    ... | σ₁ , σ₂ , sub-σ₁ , sub-σ₂ , σ₁≤σ₂
      = τ₁ ∷ σ₁ , τ₂ ∷ σ₂ , sub-τ₁ ∷ sub-σ₁ , sub-τ₂ ∷ sub-σ₂ , τ₁≤τ₂ ∷ σ₁≤σ₂

    Γ-subtype-pre-exists : subtype-pre-existsᵗ RegisterAssignment
    Γ-subtype-pre-exists Δ₁ i⋆ (Γ-≤ sp₁'≤sp₂' regs₁'≤regs₂')
      with σ-subtype-pre-exists Δ₁ i⋆ sp₁'≤sp₂'
    ... | sp₁ , sp₂ , sub-sp₁ , sub-sp₂ , sp₁≤sp₂
      with regs-subtype-pre-exists Δ₁ i⋆ regs₁'≤regs₂'
    ... | regs₁ , regs₂ , sub-regs₁ , sub-regs₂ , regs₁≤regs₂
      = _ , _ ,
          subst-registerₐ sub-sp₁ sub-regs₁ ,
          subst-registerₐ sub-sp₂ sub-regs₂ , Γ-≤ sp₁≤sp₂ regs₁≤regs₂

    regs-subtype-pre-exists : ∀ {n} → subtype-pre-existsᵗ (Vec Type n)
    regs-subtype-pre-exists Δ₁ i⋆ [] = [] , [] , [] , [] , []
    regs-subtype-pre-exists Δ₁ i⋆ (τ₁'≤τ₂' ∷ τs₁'≤τs₂')
      with τ-subtype-pre-exists Δ₁ i⋆ τ₁'≤τ₂'
    ... | τ₁ , τ₂ , sub-τ₁ , sub-τ₂ , τ₁≤τ₂
      with regs-subtype-pre-exists Δ₁ i⋆ τs₁'≤τs₂'
    ... | τs₁ , τs₂ , sub-τs₁ , sub-τs₂ , τs₁≤τs₂
      = τ₁ ∷ τs₁ , τ₂ ∷ τs₂ , sub-τ₁ ∷ sub-τs₁ , sub-τ₂ ∷ sub-τs₂ , τ₁≤τ₂ ∷ τs₁≤τs₂


Vec-SubtypeSubstitution :
  ∀ A {S S⁺ ST} {{SS : SubtypeSubstitution A {S} {{S⁺}} {{ST}}}} n →
    SubtypeSubstitution (Vec A n) {{Vec-Substitution⁺ A n}} {{Vec-Subtype A n}}
Vec-SubtypeSubstitution A {S} {S⁺} {ST} {{SS}} n = subtypeSubstitution xs-subtype-weaken xs-subtype-subst-exists xs-pre-exists
  where xs-subtype-weaken : ∀ {n} → subtype-weakenᵗ (Vec A n) {{Vec-Substitution A n}} {{Vec-Subtype A n}}
        xs-subtype-weaken Δ₁ Δ₂ Δ₃ [] = []
        xs-subtype-weaken Δ₁ Δ₂ Δ₃ (x₁≤x₂ ∷ xs₁≤xs₂) =
          subtype-weaken {{SS}} Δ₁ Δ₂ Δ₃ x₁≤x₂ ∷ xs-subtype-weaken Δ₁ Δ₂ Δ₃ xs₁≤xs₂

        xs-subtype-subst-exists : ∀ {n} → subtype-subst-existsᵗ (Vec A n) {{Vec-Substitution A n}} {{Vec-Subtype A n}}
        xs-subtype-subst-exists Δ₁ i⋆ [] = [] , [] , [] , [] , []
        xs-subtype-subst-exists Δ₁ i⋆ (x₁≤x₂ ∷ xs₁≤xs₂)
          with subtype-subst-exists Δ₁ i⋆ x₁≤x₂
        ... | x₁' , x₂' , sub-x₁ , sub-x₂ , x₁'≤x₂'
          with xs-subtype-subst-exists Δ₁ i⋆ xs₁≤xs₂
        ... | xs₁' , xs₂' , sub-xs₁ , sub-xs₂ , xs₁'≤xs₂'
            = _ , _ , sub-x₁ ∷ sub-xs₁ , sub-x₂ ∷ sub-xs₂ , x₁'≤x₂' ∷ xs₁'≤xs₂'

        xs-pre-exists : ∀ {n} → subtype-pre-existsᵗ (Vec A n) {{Vec-Substitution A n}} {{Vec-Subtype A n}}
        xs-pre-exists Δ₁ i⋆ [] = [] , [] , [] , [] , []
        xs-pre-exists Δ₁ i⋆ (x₁'≤x₂' ∷ xs₁'≤xs₂')
          with subtype-pre-exists Δ₁ i⋆ x₁'≤x₂'
        ... | x₁ , x₂ , sub-x₁ , sub-x₂ , x₁≤x₂
          with xs-pre-exists Δ₁ i⋆ xs₁'≤xs₂'
        ... | xs₁ , xs₂ , sub-xs₁ , sub-xs₂ , xs₁≤xs₂
            = _ , _ , sub-x₁ ∷ sub-xs₁ , sub-x₂ ∷ sub-xs₂ , x₁≤x₂ ∷ xs₁≤xs₂

List-SubtypeSubstitution :
  ∀ A {S S⁺ ST} {{SS : SubtypeSubstitution A {S} {{S⁺}} {{ST}}}} →
    SubtypeSubstitution (List A) {{List-Substitution⁺ A}} {{List-Subtype A}}
List-SubtypeSubstitution A {S} {S⁺} {ST} {{SS}} = subtypeSubstitution xs-subtype-weaken xs-subtype-subst-exists xs-pre-exists
  where xs-subtype-weaken : subtype-weakenᵗ (List A) {{List-Substitution A}} {{List-Subtype A}}
        xs-subtype-weaken Δ₁ Δ₂ Δ₃ [] = []
        xs-subtype-weaken Δ₁ Δ₂ Δ₃ (x₁≤x₂ ∷ xs₁≤xs₂) =
          subtype-weaken {{SS}} Δ₁ Δ₂ Δ₃ x₁≤x₂ ∷ xs-subtype-weaken Δ₁ Δ₂ Δ₃ xs₁≤xs₂

        xs-subtype-subst-exists : subtype-subst-existsᵗ (List A) {{List-Substitution A}} {{List-Subtype A}}
        xs-subtype-subst-exists Δ₁ i⋆ [] = [] , [] , [] , [] , []
        xs-subtype-subst-exists Δ₁ i⋆ (x₁≤x₂ ∷ xs₁≤xs₂)
          with subtype-subst-exists Δ₁ i⋆ x₁≤x₂
        ... | x₁' , x₂' , sub-x₁ , sub-x₂ , x₁'≤x₂'
          with xs-subtype-subst-exists Δ₁ i⋆ xs₁≤xs₂
        ... | xs₁' , xs₂' , sub-xs₁ , sub-xs₂ , xs₁'≤xs₂'
            = _ , _ , sub-x₁ ∷ sub-xs₁ , sub-x₂ ∷ sub-xs₂ , x₁'≤x₂' ∷ xs₁'≤xs₂'

        xs-pre-exists : subtype-pre-existsᵗ (List A) {{List-Substitution A}} {{List-Subtype A}}
        xs-pre-exists Δ₁ i⋆ [] = [] , [] , [] , [] , []
        xs-pre-exists Δ₁ i⋆ (x₁'≤x₂' ∷ xs₁'≤xs₂')
          with subtype-pre-exists Δ₁ i⋆ x₁'≤x₂'
        ... | x₁ , x₂ , sub-x₁ , sub-x₂ , x₁≤x₂
          with xs-pre-exists Δ₁ i⋆ xs₁'≤xs₂'
        ... | xs₁ , xs₂ , sub-xs₁ , sub-xs₂ , xs₁≤xs₂
            = _ , _ , sub-x₁ ∷ sub-xs₁ , sub-x₂ ∷ sub-xs₂ , x₁≤x₂ ∷ xs₁≤xs₂

instance
  Type-SubtypeSubstitution : SubtypeSubstitution Type
  Type-SubtypeSubstitution = subtypeSubstitution τ-subtype-weaken τ-subtype-subst-exists τ-subtype-pre-exists

  TypeVec-SubtypeSubstitution : ∀ {m} → SubtypeSubstitution (Vec Type m)
  TypeVec-SubtypeSubstitution = subtypeSubstitution regs-subtype-weaken regs-subtype-subst-exists regs-subtype-pre-exists

  TypeList-SubtypeSubstitution : SubtypeSubstitution (List Type)
  TypeList-SubtypeSubstitution = List-SubtypeSubstitution Type

  InitType-SubtypeSubstitution : SubtypeSubstitution InitType
  InitType-SubtypeSubstitution = subtypeSubstitution τ⁻-subtype-weaken τ⁻-subtype-subst-exists τ⁻-subtype-pre-exists

  InitTypeVec-SubtypeSubstitution :
    ∀ {m} → SubtypeSubstitution (Vec InitType m)
  InitTypeVec-SubtypeSubstitution = Vec-SubtypeSubstitution InitType _

  InitTypeList-SubtypeSubstitution : SubtypeSubstitution (List InitType)
  InitTypeList-SubtypeSubstitution = subtypeSubstitution τs⁻-subtype-weaken τs⁻-subtype-subst-exists τs⁻-subtype-pre-exists

  StackType-SubtypeSubstitution : SubtypeSubstitution StackType
  StackType-SubtypeSubstitution = subtypeSubstitution σ-subtype-weaken σ-subtype-subst-exists σ-subtype-pre-exists

  RegisterAssignment-SubtypeSubstitution :
    SubtypeSubstitution RegisterAssignment
  RegisterAssignment-SubtypeSubstitution = subtypeSubstitution Γ-subtype-weaken Γ-subtype-subst-exists Γ-subtype-pre-exists
