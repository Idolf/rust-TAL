module Lemmas.TypeSubstitution where

open import Util
open import Judgments
open import Lemmas.Substitution
open import Lemmas.Types

import Data.Nat as N
import Data.Nat.Properties as NP

-- The purpose of this file is
-- to include instances of this record.
record TypeSubstitution (A : Set) {S} {{S⁺ : Substitution⁺ A {{S}}}}
                                  {{T : TypeLike A}} : Set where
  constructor typeSubstitution
  field
    valid-weaken :
      ∀ Δ₁ Δ₂ Δ₃ {v : A} →
        Δ₁ ++ Δ₃ ⊢ v Valid →
        Δ₁ ++ Δ₂ ++ Δ₃ ⊢ weaken (length Δ₁) (length Δ₂) v Valid
    weaken-outside-ctx :
      ∀ {Δ} ι inc {v : A} →
        Δ ⊢ v Valid →
        weaken (length Δ + ι) inc v ≡ v
    valid-subst-exists :
      ∀ Δ₁ {Δ₂ a i} →
        Δ₂ ⊢ i of a instantiation →
        {v : A} →
        Δ₁ ++ a ∷ Δ₂ ⊢ v Valid →
        ∃ λ v' →
          v ⟦ i / length Δ₁ ⟧≡ v' ×
          Δ₁ ++ Δ₂ ⊢ v' Valid
    subst-outside-ctx :
      ∀ {Δ i ι} {v : A} →
        Δ ⊢ v Valid →
        v ⟦ i / length Δ + ι ⟧≡ v

  weaken-outside-ctx-0 :
    ∀ {Δ} inc {v : A} →
      Δ ⊢ v Valid →
      weaken (length Δ) inc v ≡ v
  weaken-outside-ctx-0 {Δ} inc v⋆
    with weaken-outside-ctx 0 inc v⋆
  ... | eq rewrite +-comm (length Δ) 0 = eq

  weaken-empty-ctx :
    ∀ pos inc {v : A} →
      [] ⊢ v Valid →
      weaken pos inc v ≡ v
  weaken-empty-ctx pos inc v⋆ = weaken-outside-ctx pos inc v⋆

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

  valid-subst :
      ∀ Δ₁ {Δ₂ a i} →
        Δ₂ ⊢ i of a instantiation →
        {v v' : A} →
        Δ₁ ++ a ∷ Δ₂ ⊢ v Valid →
        v ⟦ i / length Δ₁ ⟧≡ v' →
        Δ₁ ++ Δ₂ ⊢ v' Valid
  valid-subst Δ₁ i⋆ v⋆ sub-v
    with valid-subst-exists Δ₁ i⋆ v⋆
  ... | v'' , sub-v' , v''⋆
    rewrite subst-unique sub-v sub-v' = v''⋆

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

open TypeSubstitution {{...}} public

private
  mutual
    valid-weakenᵗ : ∀ A {{_ : Substitution A}}
                        {{_ : TypeLike A}} → Set
    valid-weakenᵗ A = ∀ Δ₁ Δ₂ Δ₃ {v : A} →
                        Δ₁ ++ Δ₃ ⊢ v Valid →
                        Δ₁ ++ Δ₂ ++ Δ₃ ⊢ weaken (length Δ₁) (length Δ₂) v Valid

    τ-valid-weaken : valid-weakenᵗ Type
    τ-valid-weaken Δ₁ Δ₂ Δ₃ {α⁼ ι} (valid-α⁼ l)
      with (length Δ₁) ≤? ι
    ... | no len≰ι = valid-α⁼ (↓-add-right (Δ₂ ++ Δ₃) (↓-remove-right Δ₁ (NP.≰⇒> len≰ι) l))
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
    ... | eq rewrite eq = valid-α⁼ l'
    τ-valid-weaken Δ₁ Δ₂ Δ₃ valid-int = valid-int
    τ-valid-weaken Δ₁ Δ₂ Δ₃ valid-ns = valid-ns
    τ-valid-weaken Δ₁ Δ₂ Δ₃ {∀[ Δ ] Γ} (valid-∀ Γ⋆)
      rewrite sym (List-++-assoc Δ Δ₁ Δ₃)
      with Γ-valid-weaken (Δ ++ Δ₁) Δ₂ Δ₃ Γ⋆
    ... | Γ'⋆
      rewrite List-++-assoc Δ Δ₁ (Δ₂ ++ Δ₃)
            | List-length-++ Δ {Δ₁} = valid-∀ Γ'⋆
    τ-valid-weaken Δ₁ Δ₂ Δ₃ (valid-tuple τs⁻⋆) = valid-tuple (τs⁻-valid-weaken Δ₁ Δ₂ Δ₃ τs⁻⋆)

    τ⁻-valid-weaken : valid-weakenᵗ InitType
    τ⁻-valid-weaken Δ₁ Δ₂ Δ₃ (valid-τ⁻ τ⋆) = valid-τ⁻ (τ-valid-weaken Δ₁ Δ₂ Δ₃ τ⋆)

    τs⁻-valid-weaken : valid-weakenᵗ (List InitType)
    τs⁻-valid-weaken Δ₁ Δ₂ Δ₃ [] = []
    τs⁻-valid-weaken Δ₁ Δ₂ Δ₃ (τ⁻⋆ ∷ τs⁻⋆) = τ⁻-valid-weaken Δ₁ Δ₂ Δ₃ τ⁻⋆ ∷ τs⁻-valid-weaken Δ₁ Δ₂ Δ₃ τs⁻⋆

    σ-valid-weaken : valid-weakenᵗ StackType
    σ-valid-weaken Δ₁ Δ₂ Δ₃ {ρ⁼ ι} (valid-ρ⁼ l)
      with (length Δ₁) ≤? ι
    ... | no len≰ι = valid-ρ⁼ (↓-add-right (Δ₂ ++ Δ₃) (↓-remove-right Δ₁ (NP.≰⇒> len≰ι) l))
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
    ... | eq rewrite eq = valid-ρ⁼ l'
    σ-valid-weaken Δ₁ Δ₂ Δ₃ [] = []
    σ-valid-weaken Δ₁ Δ₂ Δ₃ (τ⋆ ∷ σ⋆) = τ-valid-weaken Δ₁ Δ₂ Δ₃ τ⋆ ∷ σ-valid-weaken Δ₁ Δ₂ Δ₃ σ⋆

    Γ-valid-weaken : valid-weakenᵗ RegisterAssignment
    Γ-valid-weaken Δ₁ Δ₂ Δ₃ (valid-registerₐ sp⋆ regs⋆) = valid-registerₐ (σ-valid-weaken Δ₁ Δ₂ Δ₃ sp⋆) (regs-valid-weaken Δ₁ Δ₂ Δ₃ regs⋆)

    regs-valid-weaken : ∀ {n} → valid-weakenᵗ (Vec Type n)
    regs-valid-weaken Δ₁ Δ₂ Δ₃ [] = []
    regs-valid-weaken Δ₁ Δ₂ Δ₃ (τ⋆ ∷ τs⋆) = τ-valid-weaken Δ₁ Δ₂ Δ₃ τ⋆ ∷ regs-valid-weaken Δ₁ Δ₂ Δ₃ τs⋆

    i-valid-weaken : valid-weakenᵗ Instantiation
    i-valid-weaken Δ₁ Δ₂ Δ₃ (valid-α τ⋆) = valid-α (τ-valid-weaken Δ₁ Δ₂ Δ₃ τ⋆)
    i-valid-weaken Δ₁ Δ₂ Δ₃ (valid-ρ σ⋆) = valid-ρ (σ-valid-weaken Δ₁ Δ₂ Δ₃ σ⋆)

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

    i-weaken-outside-ctx : weaken-outside-ctxᵗ Instantiation
    i-weaken-outside-ctx ι inc (valid-α τ⋆) = cong α (τ-weaken-outside-ctx ι inc τ⋆)
    i-weaken-outside-ctx ι inc (valid-ρ σ⋆) = cong ρ (σ-weaken-outside-ctx ι inc σ⋆)

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
    valid-subst-existsᵗ : ∀ A {{_ : Substitution A}}
                      {{_ : TypeLike A}} → Set
    valid-subst-existsᵗ A = ∀ Δ₁ {Δ₂ a i} →
                      Δ₂ ⊢ i of a instantiation →
                      {v : A} →
                      Δ₁ ++ a ∷ Δ₂ ⊢ v Valid →
                      ∃ λ v' →
                        v ⟦ i / length Δ₁ ⟧≡ v' ×
                        Δ₁ ++ Δ₂ ⊢ v' Valid

    τ-valid-subst-exists : valid-subst-existsᵗ Type
    τ-valid-subst-exists Δ₁ {Δ₂} i⋆ {α⁼ ι} (valid-α⁼ l)
      with Nat-cmp ι (length Δ₁)
    ... | tri< ι<len _ _ = α⁼ ι , subst-α-< ι<len , valid-α⁼ (↓-add-right Δ₂ (↓-remove-right Δ₁ ι<len l))
    τ-valid-subst-exists Δ₁ {Δ₂} (of-α τ⋆) {α⁼ .(length Δ₁)} (valid-α⁼ l)
        | tri≈ _ refl _ = _ , subst-α-≡ , τ-valid-weaken [] Δ₁ Δ₂ τ⋆
    τ-valid-subst-exists Δ₁ {Δ₂} (of-ρ σ⋆) {α⁼ .(length Δ₁)} (valid-α⁼ l)
        | tri≈ _ refl _
      with ↓-remove-left Δ₁ (NP.n≤m+n 0 (length Δ₁)) l
    ... | l'
      rewrite NP.n∸n≡0 (length Δ₁)
      with l'
    ... | ()
    τ-valid-subst-exists Δ₁ {Δ₂} {a} {τ} i⋆ {α⁼ (suc ι)} (valid-α⁼ l)
        | tri> _ _ (s≤s ι≥len)
      rewrite sym (List-++-assoc Δ₁ [ a ] Δ₂)
      with ↓-add-left Δ₁ (↓-remove-left (Δ₁ ++ [ a ]) (≤-help Δ₁ a ι≥len) l)
    ... | l'
      rewrite eq-help Δ₁ a
            | NP.m+n∸m≡n ι≥len
      = α⁼ ι , subst-α-> (s≤s ι≥len) , valid-α⁼ l'
    τ-valid-subst-exists Δ₁ i⋆ valid-int = int , subst-int , valid-int
    τ-valid-subst-exists Δ₁ i⋆ valid-ns = ns , subst-ns , valid-ns
    τ-valid-subst-exists Δ₁ {Δ₂} {a} i⋆ {∀[ Δ ] Γ} (valid-∀ Γ⋆)
      rewrite sym (List-++-assoc Δ Δ₁ (a ∷ Δ₂))
      with Γ-valid-subst-exists (Δ ++ Δ₁) {Δ₂} i⋆ Γ⋆
    ... | Γ' , sub-Γ , Γ'⋆
      rewrite List-++-assoc Δ Δ₁ Δ₂
            | List-length-++ Δ {Δ₁}
        = ∀[ Δ ] Γ' , subst-∀ sub-Γ , valid-∀ Γ'⋆
    τ-valid-subst-exists Δ₁ i⋆ (valid-tuple τs⁻⋆)
      = Σ-map tuple (Σ-map subst-tuple valid-tuple) (τs⁻-valid-subst-exists Δ₁ i⋆ τs⁻⋆)

    τ⁻-valid-subst-exists : valid-subst-existsᵗ InitType
    τ⁻-valid-subst-exists Δ₁ i⋆ (valid-τ⁻ τ'⋆)
      = Σ-map _ (Σ-map subst-τ⁻ valid-τ⁻) (τ-valid-subst-exists Δ₁ i⋆ τ'⋆)

    τs⁻-valid-subst-exists : valid-subst-existsᵗ (List InitType)
    τs⁻-valid-subst-exists Δ₁ i⋆ [] = [] , [] , []
    τs⁻-valid-subst-exists Δ₁ i⋆ (τ⁻⋆ ∷ τs⁻⋆)
      = Σ-zip _∷_ (Σ-zip _∷_ _∷_) (τ⁻-valid-subst-exists Δ₁ i⋆ τ⁻⋆) (τs⁻-valid-subst-exists Δ₁ i⋆ τs⁻⋆)

    σ-valid-subst-exists : valid-subst-existsᵗ StackType
    σ-valid-subst-exists Δ₁ {Δ₂} i⋆ {ρ⁼ ι} (valid-ρ⁼ l)
      with Nat-cmp ι (length Δ₁)
    ... | tri< ι<len _ _ = ρ⁼ ι , subst-ρ-< ι<len , valid-ρ⁼ (↓-add-right Δ₂ (↓-remove-right Δ₁ ι<len l))
    σ-valid-subst-exists Δ₁ {Δ₂} (of-α τ⋆) {ρ⁼ .(length Δ₁)} (valid-ρ⁼ l)
        | tri≈ _ refl _
      with ↓-remove-left Δ₁ (NP.n≤m+n 0 (length Δ₁)) l
    ... | l'
      rewrite NP.n∸n≡0 (length Δ₁)
      with l'
    ... | ()
    σ-valid-subst-exists Δ₁ {Δ₂} (of-ρ σ⋆) {ρ⁼ .(length Δ₁)} (valid-ρ⁼ l)
        | tri≈ _ refl _ = _ , subst-ρ-≡ , σ-valid-weaken [] Δ₁ Δ₂ σ⋆
    σ-valid-subst-exists Δ₁ {Δ₂} {a} {σ} i⋆ {ρ⁼ (suc ι)} (valid-ρ⁼ l)
        | tri> _ _ (s≤s ι≥len)
      rewrite sym (List-++-assoc Δ₁ [ a ] Δ₂)
      with ↓-add-left Δ₁ (↓-remove-left (Δ₁ ++ [ a ]) (≤-help Δ₁ a ι≥len) l)
    ... | l'
      rewrite eq-help Δ₁ a
            | NP.m+n∸m≡n ι≥len
      = ρ⁼ ι , subst-ρ-> (s≤s ι≥len) , valid-ρ⁼ l'
    σ-valid-subst-exists Δ₁ i⋆ [] = [] , [] , []
    σ-valid-subst-exists Δ₁ i⋆ (τ⋆ ∷ σ⋆)
      = Σ-zip _∷_ (Σ-zip _∷_ _∷_) (τ-valid-subst-exists Δ₁ i⋆ τ⋆) (σ-valid-subst-exists Δ₁ i⋆ σ⋆)

    Γ-valid-subst-exists : valid-subst-existsᵗ RegisterAssignment
    Γ-valid-subst-exists Δ₁ i⋆ (valid-registerₐ sp⋆ regs⋆)
      = Σ-zip registerₐ (Σ-zip subst-registerₐ valid-registerₐ) (σ-valid-subst-exists Δ₁ i⋆ sp⋆) (regs-valid-subst-exists Δ₁ i⋆ regs⋆)

    regs-valid-subst-exists : ∀ {n} → valid-subst-existsᵗ (Vec Type n)
    regs-valid-subst-exists Δ₁ i⋆ [] = [] , [] , []
    regs-valid-subst-exists Δ₁ i⋆ (τ'⋆ ∷ τs⋆)
      = Σ-zip _∷_ (Σ-zip _∷_ _∷_) (τ-valid-subst-exists Δ₁ i⋆ τ'⋆) (regs-valid-subst-exists Δ₁ i⋆ τs⋆)

    i-valid-subst-exists : valid-subst-existsᵗ Instantiation
    i-valid-subst-exists Δ₁ i⋆ (valid-α τ⋆) = Σ-map α (Σ-map subst-α valid-α) (τ-valid-subst-exists Δ₁ i⋆ τ⋆)
    i-valid-subst-exists Δ₁ i⋆ (valid-ρ σ⋆) = Σ-map ρ (Σ-map subst-ρ valid-ρ) (σ-valid-subst-exists Δ₁ i⋆ σ⋆)

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

    i-subst-outside-ctx : subst-outside-ctxᵗ Instantiation
    i-subst-outside-ctx (valid-α τ⋆) = subst-α (τ-subst-outside-ctx τ⋆)
    i-subst-outside-ctx (valid-ρ σ⋆) = subst-ρ (σ-subst-outside-ctx σ⋆)

Vec-TypeSubstitution :
  ∀ A {S S⁺ T} {{TS : TypeSubstitution A {S} {{S⁺}} {{T}}}} n →
    TypeSubstitution (Vec A n) {{Vec-Substitution⁺ A n}} {{Vec-TypeLike A n}}
Vec-TypeSubstitution A {S} {S⁺} {T} {{TS}} n =
    typeSubstitution xs-valid-weaken xs-weaken-outside-ctx xs-valid-subst-exists xs-subst-outside-ctx
  where xs-valid-weaken :
          ∀ {n} (Δ₁ Δ₂ Δ₃ : TypeAssumptions) {xs : Vec A n} →
            _⊢_Valid {{Vec-TypeLike A n}} (Δ₁ ++ Δ₃) xs →
            _⊢_Valid {{Vec-TypeLike A n}} (Δ₁ ++ Δ₂ ++ Δ₃)
              (weaken {{Vec-Substitution A n}} (length Δ₁) (length Δ₂) xs)
        xs-valid-weaken Δ₁ Δ₂ Δ₃ [] = []
        xs-valid-weaken Δ₁ Δ₂ Δ₃ (x⋆ ∷ xs⋆) =
          valid-weaken {{TS}} Δ₁ Δ₂ Δ₃ x⋆ ∷ xs-valid-weaken Δ₁ Δ₂ Δ₃ xs⋆

        xs-weaken-outside-ctx : ∀ {n} → weaken-outside-ctxᵗ (Vec A n) {{Vec-Substitution A n}} {{Vec-TypeLike A n}}
        xs-weaken-outside-ctx ι inc [] = refl
        xs-weaken-outside-ctx ι inc (x⋆ ∷ xs⋆) = cong₂ _∷_ (weaken-outside-ctx {{TS}} ι inc x⋆) (xs-weaken-outside-ctx ι inc xs⋆)

        xs-valid-subst-exists :
          ∀ {n} Δ₁ {Δ₂ a i} →
            Δ₂ ⊢ i of a instantiation →
            {xs : Vec A n} →
            _⊢_Valid {{Vec-TypeLike A n}} (Δ₁ ++ a ∷ Δ₂) xs →
            ∃ λ xs' →
              _⟦_/_⟧≡_ {{Vec-Substitution A n}} xs i (length Δ₁) xs' ×
              _⊢_Valid {{Vec-TypeLike A n}} (Δ₁ ++ Δ₂) xs'
        xs-valid-subst-exists Δ₁ i⋆ [] = [] , [] , []
        xs-valid-subst-exists Δ₁ i⋆ (x⋆ ∷ xs⋆) =
          Σ-zip _∷_ (Σ-zip _∷_ _∷_) (valid-subst-exists {{TS}} Δ₁ i⋆ x⋆) (xs-valid-subst-exists Δ₁ i⋆ xs⋆)

        xs-subst-outside-ctx :
          ∀ {Δ i ι n} {xs : Vec A n} →
            _⊢_Valid {{Vec-TypeLike A n}} Δ xs →
            _⟦_/_⟧≡_ {{Vec-Substitution A n}} xs i (length Δ + ι) xs
        xs-subst-outside-ctx [] = []
        xs-subst-outside-ctx (x⋆ ∷ xs⋆) = subst-outside-ctx {{TS}} x⋆ ∷ xs-subst-outside-ctx xs⋆

List-TypeSubstitution :
  ∀ A {S S⁺ T} {{TS : TypeSubstitution A {S} {{S⁺}} {{T}}}} →
    TypeSubstitution (List A) {{List-Substitution⁺ A}} {{List-TypeLike A}}
List-TypeSubstitution A {S} {S⁺} {T} {{TS}} =
    typeSubstitution xs-valid-weaken xs-weaken-outside-ctx xs-valid-subst-exists xs-subst-outside-ctx
  where xs-valid-weaken :
          ∀ (Δ₁ Δ₂ Δ₃ : TypeAssumptions) {xs : List A} →
            _⊢_Valid {{List-TypeLike A}} (Δ₁ ++ Δ₃) xs →
            _⊢_Valid {{List-TypeLike A}} (Δ₁ ++ Δ₂ ++ Δ₃)
              (weaken {{List-Substitution A}} (length Δ₁) (length Δ₂) xs)
        xs-valid-weaken Δ₁ Δ₂ Δ₃ [] = []
        xs-valid-weaken Δ₁ Δ₂ Δ₃ (x⋆ ∷ xs⋆) =
          valid-weaken {{TS}} Δ₁ Δ₂ Δ₃ x⋆ ∷ xs-valid-weaken Δ₁ Δ₂ Δ₃ xs⋆

        xs-weaken-outside-ctx : weaken-outside-ctxᵗ (List A) {{List-Substitution A}} {{List-TypeLike A}}
        xs-weaken-outside-ctx ι inc [] = refl
        xs-weaken-outside-ctx ι inc (x⋆ ∷ xs⋆) = cong₂ _∷_ (weaken-outside-ctx {{TS}} ι inc x⋆) (xs-weaken-outside-ctx ι inc xs⋆)

        xs-valid-subst-exists :
          ∀ Δ₁ {Δ₂ a i} →
            Δ₂ ⊢ i of a instantiation →
            {xs : List A} →
            _⊢_Valid {{List-TypeLike A}} (Δ₁ ++ a ∷ Δ₂) xs →
            ∃ λ xs' →
              _⟦_/_⟧≡_ {{List-Substitution A}} xs i (length Δ₁) xs' ×
              _⊢_Valid {{List-TypeLike A}} (Δ₁ ++ Δ₂) xs'
        xs-valid-subst-exists Δ₁ i⋆ [] = [] , [] , []
        xs-valid-subst-exists Δ₁ i⋆ (x⋆ ∷ xs⋆) =
          Σ-zip _∷_ (Σ-zip _∷_ _∷_) (valid-subst-exists {{TS}} Δ₁ i⋆ x⋆) (xs-valid-subst-exists Δ₁ i⋆ xs⋆)

        xs-subst-outside-ctx :
          ∀ {Δ i ι} {xs : List A} →
            _⊢_Valid {{List-TypeLike A}} Δ xs →
            _⟦_/_⟧≡_ {{List-Substitution A}} xs i (length Δ + ι) xs
        xs-subst-outside-ctx [] = []
        xs-subst-outside-ctx (x⋆ ∷ xs⋆) = subst-outside-ctx {{TS}} x⋆ ∷ xs-subst-outside-ctx xs⋆

instance
  Type-TypeSubstitution : TypeSubstitution Type
  Type-TypeSubstitution =
    typeSubstitution τ-valid-weaken τ-weaken-outside-ctx τ-valid-subst-exists  τ-subst-outside-ctx

  TypeVec-TypeSubstitution : ∀ {m} → TypeSubstitution (Vec Type m)
  TypeVec-TypeSubstitution = typeSubstitution regs-valid-weaken regs-weaken-outside-ctx regs-valid-subst-exists regs-subst-outside-ctx

  TypeList-TypeSubstitution : TypeSubstitution (List Type)
  TypeList-TypeSubstitution = List-TypeSubstitution Type

  InitType-TypeSubstitution : TypeSubstitution InitType
  InitType-TypeSubstitution = typeSubstitution
    τ⁻-valid-weaken τ⁻-weaken-outside-ctx τ⁻-valid-subst-exists τ⁻-subst-outside-ctx

  InitTypeVec-TypeSubstitution : ∀ {m} → TypeSubstitution (Vec InitType m)
  InitTypeVec-TypeSubstitution = Vec-TypeSubstitution InitType _

  InitTypeList-TypeSubstitution : TypeSubstitution (List InitType)
  InitTypeList-TypeSubstitution = typeSubstitution τs⁻-valid-weaken τs⁻-weaken-outside-ctx τs⁻-valid-subst-exists τs⁻-subst-outside-ctx

  StackType-TypeSubstitution : TypeSubstitution StackType
  StackType-TypeSubstitution = typeSubstitution
    σ-valid-weaken σ-weaken-outside-ctx σ-valid-subst-exists σ-subst-outside-ctx

  RegisterAssignment-TypeSubstitution : TypeSubstitution RegisterAssignment
  RegisterAssignment-TypeSubstitution = typeSubstitution
    Γ-valid-weaken Γ-weaken-outside-ctx Γ-valid-subst-exists Γ-subst-outside-ctx

  Instantiation-TypeSubstitution : TypeSubstitution Instantiation
  Instantiation-TypeSubstitution = typeSubstitution
    i-valid-weaken i-weaken-outside-ctx i-valid-subst-exists i-subst-outside-ctx
