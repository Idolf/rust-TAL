module Lemmas.TypeSubstitution where

open import Util
open import Judgments
open import Lemmas.Substitution
open import Lemmas.Types

import Data.Nat as N
import Data.Nat.Properties as NP
open import Data.List.Properties using (map-id)

-- The purpose of this file is
-- to include instances of this record.
record TypeSubstitution (A : Set) {S} {T} {{S⁺ : Substitution⁺ A {{S}}}}
                                          {{T⁺ : TypeLike⁺ A {{T}}}} : Set where
  constructor typeSubstitution
  field
    weaken-outside-ctx :
      ∀ {Δ} ι inc {v : A} →
        Δ ⊢ v Valid →
        weaken (length Δ + ι) inc v ≡ v
    subst-outside-ctx :
      ∀ {Δ i ι} {v : A} →
        Δ ⊢ v Valid →
        v ⟦ i / length Δ + ι ⟧≡ v
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

  valid-weaken :
    ∀ Δ₁ Δ₂ Δ₃ {v : A} →
      Δ₁ ++ Δ₃ ⊢ v Valid →
      Δ₁ ++ Δ₂ ++ Δ₃ ⊢ weaken (length Δ₁) (length Δ₂) v Valid
  valid-weaken Δ₁ Δ₂ Δ₃ v⋆ = proj₁ (≤-valid (subtype-weaken Δ₁ Δ₂ Δ₃ (≤-refl v⋆)))

  valid-subst-exists :
    ∀ Δ₁ {Δ₂ a i} →
      Δ₂ ⊢ i of a instantiation →
      {v : A} →
      Δ₁ ++ a ∷ Δ₂ ⊢ v Valid →
      ∃ λ v' →
        v ⟦ i / length Δ₁ ⟧≡ v' ×
        Δ₁ ++ Δ₂ ⊢ v' Valid
  valid-subst-exists Δ₁ i⋆ v⋆
    with subtype-subst-exists Δ₁ i⋆ (≤-refl v⋆)
  ... | v₁ , v₂ , sub-v₁ , sub-v₂ , v₁≤v₂
    = _ , sub-v₁ , proj₁ (≤-valid v₁≤v₂)

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
    with subtype-subst-exists Δ₁ i⋆ v₁≤v₂
  ... | v₁' , v₂' , sub-v₁ , sub-v₂ , v₁'≤v₂'
    with subtype-subst-exists-many Δ₁ is⋆ v₁'≤v₂'
  ... | v₁ₑ , v₂ₑ , subs-v₁ , subs-v₂ , v₁ₑ≤v₂ₑ
    = _ , _ , sub-v₁ ∷ subs-v₁ , sub-v₂ ∷ subs-v₂ , v₁ₑ≤v₂ₑ

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

  weaken-outside-ctx-0 :
    ∀ {Δ} inc {v : A} →
      Δ ⊢ v Valid →
      weaken (length Δ) inc v ≡ v
  weaken-outside-ctx-0 {Δ} inc v⋆
    with weaken-outside-ctx 0 inc v⋆
  ... | eq rewrite +-comm (length Δ) 0 = eq

  valid-subst-exists-many :
    ∀ Δ₁ {Δ₂ Δ₃ is} →
      Δ₃ ⊢ is of Δ₂ instantiations →
      {v : A} →
      Δ₁ ++ Δ₂ ++ Δ₃ ⊢ v Valid →
      ∃ λ v' →
        v ⟦ is / length Δ₁ ⟧many≡ v' ×
        Δ₁ ++ Δ₃ ⊢ v' Valid
  valid-subst-exists-many Δ₁ [] v⋆ = _ , [] , v⋆
  valid-subst-exists-many Δ₁ {a ∷ Δ₂} {Δ₃} {i ∷ is}(i⋆ ∷ is⋆) v⋆
    with valid-subst-exists Δ₁ i⋆ v⋆
  ... | v' , sub-v , v'⋆
    with valid-subst-exists-many Δ₁ is⋆ v'⋆
  ... | vₑ , subs-v , vₑ⋆
    = _ , sub-v ∷ subs-v , vₑ⋆

  valid-subst-many :
      ∀ Δ₁ {Δ₂ Δ₃ is} →
        Δ₃ ⊢ is of Δ₂ instantiations →
        {v v' : A} →
        Δ₁ ++ Δ₂ ++ Δ₃ ⊢ v Valid →
        v ⟦ is / length Δ₁ ⟧many≡ v' →
        Δ₁ ++ Δ₃ ⊢ v' Valid
  valid-subst-many Δ₁ is⋆ v⋆ subs-v
    with valid-subst-exists-many Δ₁ is⋆ v⋆
  ... | v'' , subs-v' , v''⋆
    rewrite subst-unique-many subs-v subs-v' = v''⋆

  ≤-++ : ∀ {Δ Δ'} {v₁ v₂ : A} →
           Δ ⊢ v₁ ≤ v₂ →
           Δ ++ Δ' ⊢ v₁ ≤ v₂
  ≤-++ {Δ} {Δ'} {v₁} {v₂} v₁≤v₂
    with subtype-weaken Δ Δ' [] (subst (λ Δ → Δ ⊢ v₁ ≤ v₂) (sym (List-++-right-identity Δ)) v₁≤v₂)
  ... | v₁'≤v₂'
    rewrite List-++-right-identity Δ'
          | weaken-outside-ctx-0 (length Δ') (proj₁ (≤-valid v₁≤v₂))
          | weaken-outside-ctx-0 (length Δ') (proj₂ (≤-valid v₁≤v₂))
    = v₁'≤v₂'

  valid-++ : ∀ {Δ Δ'} {v : A} → Δ ⊢ v Valid → Δ ++ Δ' ⊢ v Valid
  valid-++ v⋆ = proj₁ (≤-valid (≤-++ (≤-refl v⋆)))

open TypeSubstitution {{...}} public

private
  mutual
    weaken-outside-ctxᵗ : ∀ A {{_ : Substitution A}}
                              {{_ : TypeLike A}} → Set
    weaken-outside-ctxᵗ A = ∀ {Δ} ι inc {v : A} →
                               Δ ⊢ v Valid →
                               weaken (length Δ + ι) inc v ≡ v

    τ-weaken-outside-ctx : weaken-outside-ctxᵗ Type
    τ-weaken-outside-ctx {Δ} ι₁ inc {v = α⁼ ι₂} (valid-α⁼ l)
      with ↓-to-< l | length Δ + ι₁ ≤? ι₂
    ... | ι₂<len | no len+ι₁≰ι₂ = refl
    ... | ι₂<len | yes len+ι₁≤ι₂
      with NP.1+n≰n (Nat-≤-trans ι₂<len (Nat-≤-trans (NP.m≤m+n (length Δ) ι₁) len+ι₁≤ι₂))
    ... | ()
    τ-weaken-outside-ctx ι inc valid-int = refl
    τ-weaken-outside-ctx ι inc valid-ns = refl
    τ-weaken-outside-ctx {Δ} ι inc {v = ∀[ Δ' ] Γ} (valid-∀ Γ⋆)
      with Γ-weaken-outside-ctx {Δ' ++ Δ} ι inc {Γ} Γ⋆
    ... | eq
      rewrite List-length-++ Δ' {Δ}
            | +-assoc (length Δ') (length Δ) ι = cong (∀[_]_ Δ') eq
    τ-weaken-outside-ctx ι inc (valid-tuple τs⁻⋆) = cong tuple (τs⁻-weaken-outside-ctx ι inc τs⁻⋆)

    τ⁻-weaken-outside-ctx : weaken-outside-ctxᵗ InitType
    τ⁻-weaken-outside-ctx ι inc (valid-τ⁻ τ⋆) = cong₂ _,_ (τ-weaken-outside-ctx ι inc τ⋆) refl

    τs⁻-weaken-outside-ctx : weaken-outside-ctxᵗ (List InitType)
    τs⁻-weaken-outside-ctx ι inc [] = refl
    τs⁻-weaken-outside-ctx ι inc (τ⁻⋆ ∷ τs⁻⋆) = cong₂ _∷_ (τ⁻-weaken-outside-ctx ι inc τ⁻⋆) (τs⁻-weaken-outside-ctx ι inc τs⁻⋆)

    σ-weaken-outside-ctx : weaken-outside-ctxᵗ StackType
    σ-weaken-outside-ctx {Δ} ι₁ inc {v = ρ⁼ ι₂} (valid-ρ⁼ l)
      with ↓-to-< l | length Δ + ι₁ ≤? ι₂
    ... | ι₂<len | no len+ι₁≰ι₂ = refl
    ... | ι₂<len | yes len+ι₁≤ι₂
      with NP.1+n≰n (Nat-≤-trans ι₂<len (Nat-≤-trans (NP.m≤m+n (length Δ) ι₁) len+ι₁≤ι₂))
    ... | ()
    σ-weaken-outside-ctx ι inc [] = refl
    σ-weaken-outside-ctx ι inc (τ⋆ ∷ σ⋆) = cong₂ _∷_ (τ-weaken-outside-ctx ι inc τ⋆) (σ-weaken-outside-ctx ι inc σ⋆)

    Γ-weaken-outside-ctx : weaken-outside-ctxᵗ RegisterAssignment
    Γ-weaken-outside-ctx ι inc (valid-registerₐ sp⋆ regs⋆) = cong₂ registerₐ (σ-weaken-outside-ctx ι inc sp⋆) (regs-weaken-outside-ctx ι inc regs⋆)

    regs-weaken-outside-ctx : ∀ {n} → weaken-outside-ctxᵗ (Vec Type n)
    regs-weaken-outside-ctx ι inc [] = refl
    regs-weaken-outside-ctx ι inc (τ⋆ ∷ τs⋆) = cong₂ _∷_ (τ-weaken-outside-ctx ι inc τ⋆) (regs-weaken-outside-ctx ι inc τs⋆)

  eq-help : ∀ (Δ : TypeAssumptions) a →
              length (Δ ++ [ a ]) ≡ suc (length Δ)
  eq-help Δ a =
    begin
      length (Δ ++ [ a ])
    ≡⟨ List-length-++ Δ ⟩
      length Δ + 1
    ≡⟨ +-comm (length Δ) 1 ⟩
      1 + length Δ
    ∎ where open Eq-Reasoning

  ≤-help : ∀ (Δ : TypeAssumptions) a {ι} →
             ι ≥ length Δ →
             suc ι ≥ length (Δ ++ [ a ])
  ≤-help Δ a {ι} ι≥len =
    begin
      length (Δ ++ [ a ])
    ≡⟨ eq-help Δ a ⟩
      1 + length Δ
    ≤⟨ s≤s ι≥len ⟩
      suc ι
    ∎ where open N.≤-Reasoning

  mutual
    subst-outside-ctxᵗ : ∀ A {{_ : Substitution A}}
                       {{_ : TypeLike A}} → Set
    subst-outside-ctxᵗ A = ∀ {Δ i ι} {v : A} →
                       Δ ⊢ v Valid →
                       v ⟦ i / length Δ + ι ⟧≡ v

    τ-subst-outside-ctx : subst-outside-ctxᵗ Type
    τ-subst-outside-ctx {Δ} {ι = ι} (valid-α⁼ l) =
      subst-α-< (Nat-≤-trans (↓-to-< l) (NP.m≤m+n (length Δ) ι))
    τ-subst-outside-ctx valid-int = subst-int
    τ-subst-outside-ctx valid-ns = subst-ns
    τ-subst-outside-ctx {Δ} {i} {ι} {∀[ Δ' ] Γ} (valid-∀ Γ⋆)
      with Γ-subst-outside-ctx {Δ' ++ Δ} {ι = ι} Γ⋆
    ... | sub-Γ
      rewrite List-length-++ Δ' {Δ}
            | +-assoc (length Δ') (length Δ) ι = subst-∀ sub-Γ
    τ-subst-outside-ctx (valid-tuple τs⁻⋆) = subst-tuple (τs⁻-subst-outside-ctx τs⁻⋆)

    τ⁻-subst-outside-ctx : subst-outside-ctxᵗ InitType
    τ⁻-subst-outside-ctx (valid-τ⁻ τ⋆) = subst-τ⁻ (τ-subst-outside-ctx τ⋆)

    τs⁻-subst-outside-ctx : subst-outside-ctxᵗ (List InitType)
    τs⁻-subst-outside-ctx [] = []
    τs⁻-subst-outside-ctx (τ⁻⋆ ∷ τs⁻⋆) = τ⁻-subst-outside-ctx τ⁻⋆ ∷ τs⁻-subst-outside-ctx τs⁻⋆

    σ-subst-outside-ctx : subst-outside-ctxᵗ StackType
    σ-subst-outside-ctx {Δ} {ι = ι} (valid-ρ⁼ l) =
      subst-ρ-< (Nat-≤-trans (↓-to-< l) (NP.m≤m+n (length Δ) ι))
    σ-subst-outside-ctx [] = []
    σ-subst-outside-ctx (τ⋆ ∷ σ⋆) = τ-subst-outside-ctx τ⋆ ∷ σ-subst-outside-ctx σ⋆

    Γ-subst-outside-ctx : subst-outside-ctxᵗ RegisterAssignment
    Γ-subst-outside-ctx (valid-registerₐ sp⋆ regs⋆) =
      subst-registerₐ (σ-subst-outside-ctx sp⋆) (regs-subst-outside-ctx regs⋆)

    regs-subst-outside-ctx : ∀ {m} → subst-outside-ctxᵗ (Vec Type m)
    regs-subst-outside-ctx [] = []
    regs-subst-outside-ctx (τ⋆ ∷ τs⋆) = τ-subst-outside-ctx τ⋆ ∷ regs-subst-outside-ctx τs⋆

  subtype-weakenᵗ :
    ∀ A {{_ : Substitution A}}
        {{_ : TypeLike A}} → Set
  subtype-weakenᵗ A =
    ∀ Δ₁ Δ₂ Δ₃ →
      {v₁ v₂ : A} →
      Δ₁ ++ Δ₃ ⊢ v₁ ≤ v₂ →
      Δ₁ ++ Δ₂ ++ Δ₃ ⊢ weaken (length Δ₁) (length Δ₂) v₁ ≤ weaken (length Δ₁) (length Δ₂) v₂

  mutual
    τ-subtype-weaken : subtype-weakenᵗ Type
    τ-subtype-weaken Δ₁ Δ₂ Δ₃ {α⁼ ι} (α⁼-≤ l)
      with (length Δ₁) ≤? ι
    ... | no len≰ι = α⁼-≤ (↓-add-right (Δ₂ ++ Δ₃) (↓-remove-right Δ₁ (NP.≰⇒> len≰ι) l))
    ... | yes len≤ι
      with ↓-add-left Δ₁ (↓-add-left Δ₂ (↓-remove-left Δ₁ len≤ι l))
    ... | l'
      with
        begin
          length Δ₁ + (length Δ₂ + (ι ∸ length Δ₁))
        ⟨ +-assoc (length Δ₁) (length Δ₂) (ι ∸ length Δ₁) ⟩≡
          length Δ₁ + length Δ₂ + (ι ∸ length Δ₁)
        ≡⟨ +-comm (length Δ₁) (length Δ₂) ∥ (λ v → v + (ι ∸ length Δ₁)) ⟩
          length Δ₂ + length Δ₁ + (ι ∸ length Δ₁)
        ≡⟨ +-assoc (length Δ₂) (length Δ₁) (ι ∸ length Δ₁) ⟩
          length Δ₂ + (length Δ₁ + (ι ∸ length Δ₁))
        ≡⟨ NP.m+n∸m≡n len≤ι ∥ (λ v → length Δ₂ + v) ⟩
          length Δ₂ + ι
        ∎ where open Eq-Reasoning
    ... | eq rewrite eq = α⁼-≤ l'
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
    τ⁻-subtype-weaken Δ₁ Δ₂ Δ₃ (τ⁻-≤ τ⋆ φ₁≤φ₂)
      = τ⁻-≤ (proj₁ (≤-valid (τ-subtype-weaken Δ₁ Δ₂ Δ₃ (≤-refl τ⋆)))) φ₁≤φ₂

    τs⁻-subtype-weaken : subtype-weakenᵗ (List InitType)
    τs⁻-subtype-weaken Δ₁ Δ₂ Δ₃ [] = []
    τs⁻-subtype-weaken Δ₁ Δ₂ Δ₃ (τ⁻₁≤τ⁻₂ ∷ τs⁻₁≤τs⁻₂) = τ⁻-subtype-weaken Δ₁ Δ₂ Δ₃ τ⁻₁≤τ⁻₂ ∷ τs⁻-subtype-weaken Δ₁ Δ₂ Δ₃ τs⁻₁≤τs⁻₂

    σ-subtype-weaken : subtype-weakenᵗ StackType
    σ-subtype-weaken Δ₁ Δ₂ Δ₃ {ρ⁼ ι} (ρ⁼-≤ l)
      with (length Δ₁) ≤? ι
    ... | no len≰ι = ρ⁼-≤ (↓-add-right (Δ₂ ++ Δ₃) (↓-remove-right Δ₁ (NP.≰⇒> len≰ι) l))
    ... | yes len≤ι
      with ↓-add-left Δ₁ (↓-add-left Δ₂ (↓-remove-left Δ₁ len≤ι l))
    ... | l'
      with
        begin
          length Δ₁ + (length Δ₂ + (ι ∸ length Δ₁))
        ⟨ +-assoc (length Δ₁) (length Δ₂) (ι ∸ length Δ₁) ⟩≡
          length Δ₁ + length Δ₂ + (ι ∸ length Δ₁)
        ≡⟨ +-comm (length Δ₁) (length Δ₂) ∥ (λ v → v + (ι ∸ length Δ₁)) ⟩
          length Δ₂ + length Δ₁ + (ι ∸ length Δ₁)
        ≡⟨ +-assoc (length Δ₂) (length Δ₁) (ι ∸ length Δ₁) ⟩
          length Δ₂ + (length Δ₁ + (ι ∸ length Δ₁))
        ≡⟨ NP.m+n∸m≡n len≤ι ∥ (λ v → length Δ₂ + v) ⟩
          length Δ₂ + ι
        ∎ where open Eq-Reasoning
    ... | eq rewrite eq = ρ⁼-≤ l'
    σ-subtype-weaken Δ₁ Δ₂ Δ₃ [] = []
    σ-subtype-weaken Δ₁ Δ₂ Δ₃ (τ₁≤τ₂ ∷ σ₁≤σ₂) = τ-subtype-weaken Δ₁ Δ₂ Δ₃ τ₁≤τ₂ ∷ σ-subtype-weaken Δ₁ Δ₂ Δ₃ σ₁≤σ₂

    Γ-subtype-weaken : subtype-weakenᵗ RegisterAssignment
    Γ-subtype-weaken Δ₁ Δ₂ Δ₃ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂) = Γ-≤ (σ-subtype-weaken Δ₁ Δ₂ Δ₃ sp₁≤sp₂) (regs-subtype-weaken Δ₁ Δ₂ Δ₃ regs₁≤regs₂)

    regs-subtype-weaken : ∀ {n} → subtype-weakenᵗ (Vec Type n)
    regs-subtype-weaken Δ₁ Δ₂ Δ₃ [] = []
    regs-subtype-weaken Δ₁ Δ₂ Δ₃ (τ₁≤τ₂ ∷ τs₁≤τs₂) = τ-subtype-weaken Δ₁ Δ₂ Δ₃ τ₁≤τ₂ ∷ regs-subtype-weaken Δ₁ Δ₂ Δ₃ τs₁≤τs₂

  subtype-subst-existsᵗ :
    ∀ A {{_ : Substitution A}}
        {{_ : TypeLike A}} → Set
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
    τ-subtype-subst-exists Δ₁ {Δ₂} i⋆ {α⁼ ι} (α⁼-≤ l)
      with Nat-cmp ι (length Δ₁)
    ... | tri< ι<len _ _ = _ , _ , subst-α-< ι<len , subst-α-< ι<len , α⁼-≤ (↓-add-right Δ₂ (↓-remove-right Δ₁ ι<len l))
    τ-subtype-subst-exists Δ₁ {Δ₂} (of-α τ⋆) {α⁼ .(length Δ₁)} (α⁼-≤ l)
        | tri≈ _ refl _ = _ , _ , subst-α-≡ , subst-α-≡ , τ-subtype-weaken [] Δ₁ Δ₂ (≤-refl τ⋆)
    τ-subtype-subst-exists Δ₁ {Δ₂} (of-ρ σ⋆) {α⁼ .(length Δ₁)} (α⁼-≤ l)
        | tri≈ _ refl _
      with ↓-remove-left Δ₁ (NP.n≤m+n 0 (length Δ₁)) l
    ... | l'
      rewrite NP.n∸n≡0 (length Δ₁)
      with l'
    ... | ()
    τ-subtype-subst-exists Δ₁ {Δ₂} {a} {τ} i⋆ {α⁼ (suc ι)} (α⁼-≤ l)
        | tri> _ _ (s≤s ι≥len)
      rewrite sym (List-++-assoc Δ₁ [ a ] Δ₂)
      with ↓-add-left Δ₁ (↓-remove-left (Δ₁ ++ [ a ]) (≤-help Δ₁ a ι≥len) l)
    ... | l'
      rewrite eq-help Δ₁ a
            | NP.m+n∸m≡n ι≥len
        = _ , _ , subst-α-> (s≤s ι≥len) , subst-α-> (s≤s ι≥len) , α⁼-≤ l'
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
      with τ-subtype-subst-exists Δ₁ i⋆ (≤-refl τ⋆)
    ... | τ₁ , τ₂ , sub-τ₁ , sub-τ₂ , τ₁≤τ₂
      rewrite subst-unique sub-τ₁ sub-τ₂
      = _ , _ , subst-τ⁻ sub-τ₂ , subst-τ⁻ sub-τ₂ , τ⁻-≤ (proj₁ (≤-valid τ₁≤τ₂)) φ₁≤φ₂

    τs⁻-subtype-subst-exists : subtype-subst-existsᵗ (List InitType)
    τs⁻-subtype-subst-exists Δ₁ i⋆ [] = [] , [] , [] , [] , []
    τs⁻-subtype-subst-exists Δ₁ i⋆ (τ⁻₁≤τ⁻₂ ∷ τs⁻₁≤τs⁻₂)
      with τ⁻-subtype-subst-exists Δ₁ i⋆ τ⁻₁≤τ⁻₂
    ... | τ⁻₁' , τ⁻₂' , sub-τ⁻₁ , sub-τ⁻₂ , τ⁻₁'≤τ⁻₂'
      with τs⁻-subtype-subst-exists Δ₁ i⋆ τs⁻₁≤τs⁻₂
    ... | τs⁻₁' , τs⁻₂' , sub-τs⁻₁ , sub-τs⁻₂ , τs⁻₁'≤τs⁻₂'
      = _ , _ , sub-τ⁻₁ ∷ sub-τs⁻₁ , sub-τ⁻₂ ∷ sub-τs⁻₂ , τ⁻₁'≤τ⁻₂' ∷ τs⁻₁'≤τs⁻₂'

    σ-subtype-subst-exists : subtype-subst-existsᵗ StackType
    σ-subtype-subst-exists Δ₁ {Δ₂} i⋆ {ρ⁼ ι} (ρ⁼-≤ l)
      with Nat-cmp ι (length Δ₁)
    ... | tri< ι<len _ _ = _ , _ , subst-ρ-< ι<len , subst-ρ-< ι<len , ρ⁼-≤ (↓-add-right Δ₂ (↓-remove-right Δ₁ ι<len l))
    σ-subtype-subst-exists Δ₁ {Δ₂} (of-ρ σ⋆) {ρ⁼ .(length Δ₁)} (ρ⁼-≤ l)
        | tri≈ _ refl _ = _ , _ , subst-ρ-≡ , subst-ρ-≡ , σ-subtype-weaken [] Δ₁ Δ₂ (≤-refl σ⋆)
    σ-subtype-subst-exists Δ₁ {Δ₂} (of-α τ⋆) {ρ⁼ .(length Δ₁)} (ρ⁼-≤ l)
        | tri≈ _ refl _
      with ↓-remove-left Δ₁ (NP.n≤m+n 0 (length Δ₁)) l
    ... | l'
      rewrite NP.n∸n≡0 (length Δ₁)
      with l'
    ... | ()
    σ-subtype-subst-exists Δ₁ {Δ₂} {a} {σ} i⋆ {ρ⁼ (suc ι)} (ρ⁼-≤ l)
        | tri> _ _ (s≤s ι≥len)
      rewrite sym (List-++-assoc Δ₁ [ a ] Δ₂)
      with ↓-add-left Δ₁ (↓-remove-left (Δ₁ ++ [ a ]) (≤-help Δ₁ a ι≥len) l)
    ... | l'
      rewrite eq-help Δ₁ a
            | NP.m+n∸m≡n ι≥len
        = _ , _ , subst-ρ-> (s≤s ι≥len) , subst-ρ-> (s≤s ι≥len) , ρ⁼-≤ l'
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

List-TypeSubstitution :
  ∀ A {S S⁺ T T⁺} {{TS : TypeSubstitution A {S} {T} {{S⁺}} {{T⁺}}}} →
    TypeSubstitution (List A) {{List-Substitution⁺ A}} {{List-TypeLike⁺ A}}
List-TypeSubstitution A {S} {T} {S⁺} {T⁺} {{TS}} = typeSubstitution
    (λ ι inc → All-≡-left (weaken _ inc) ∘ All-map (weaken-outside-ctx ι inc))
    (All→AllZip ∘ All-map subst-outside-ctx)
    (λ Δ₁ Δ₂ Δ₃ → AllZip-map' _ _ (subtype-weaken Δ₁ Δ₂ Δ₃))
    (λ Δ₁ i⋆ → AllZip-∃₂→ ∘ AllZip-map (subtype-subst-exists Δ₁ i⋆))

instance
  Type-TypeSubstitution : TypeSubstitution Type
  Type-TypeSubstitution =
    typeSubstitution τ-weaken-outside-ctx τ-subst-outside-ctx τ-subtype-weaken τ-subtype-subst-exists

  TypeVec-TypeSubstitution : ∀ {m} → TypeSubstitution (Vec Type m)
  TypeVec-TypeSubstitution = typeSubstitution regs-weaken-outside-ctx regs-subst-outside-ctx regs-subtype-weaken regs-subtype-subst-exists

  TypeList-TypeSubstitution : TypeSubstitution (List Type)
  TypeList-TypeSubstitution = List-TypeSubstitution Type

  InitType-TypeSubstitution : TypeSubstitution InitType
  InitType-TypeSubstitution = typeSubstitution τ⁻-weaken-outside-ctx τ⁻-subst-outside-ctx τ⁻-subtype-weaken τ⁻-subtype-subst-exists

  InitTypeList-TypeSubstitution : TypeSubstitution (List InitType)
  InitTypeList-TypeSubstitution = typeSubstitution τs⁻-weaken-outside-ctx τs⁻-subst-outside-ctx τs⁻-subtype-weaken τs⁻-subtype-subst-exists

  StackType-TypeSubstitution : TypeSubstitution StackType
  StackType-TypeSubstitution = typeSubstitution
    σ-weaken-outside-ctx σ-subst-outside-ctx σ-subtype-weaken σ-subtype-subst-exists

  RegisterAssignment-TypeSubstitution : TypeSubstitution RegisterAssignment
  RegisterAssignment-TypeSubstitution = typeSubstitution
    Γ-weaken-outside-ctx Γ-subst-outside-ctx Γ-subtype-weaken Γ-subtype-subst-exists
