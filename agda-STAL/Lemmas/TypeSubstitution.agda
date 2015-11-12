module Lemmas.TypeSubstitution where

open import Util
open import Judgments
open import Lemmas.Substitution

import Data.Nat as N
import Data.Nat.Properties as NP

-- The purpose of this file is
-- to include instances of this record.
record TypeSubstitution (A : Set) {S} {{S⁺ : Substitution⁺ A {{S}}}}
                                  {{T : TypeLike A}} : Set where
  constructor typeSubstitution
  field
    subst-valid-weaken :
      ∀ Δ₁ Δ₂ Δ₃ {v : A} →
        Δ₁ ++ Δ₃ ⊢ v Valid →
        Δ₁ ++ Δ₂ ++ Δ₃ ⊢ weaken (length Δ₁) (length Δ₂) v Valid
    subst-valid-inst :
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
    valid-instᵗ : ∀ A {{_ : Substitution A}}
                      {{_ : TypeLike A}} → Set
    valid-instᵗ A = ∀ Δ₁ {Δ₂ a i} →
                      Δ₂ ⊢ i of a instantiation →
                      {v : A} →
                      Δ₁ ++ a ∷ Δ₂ ⊢ v Valid →
                      ∃ λ v' →
                        v ⟦ i / length Δ₁ ⟧≡ v' ×
                        Δ₁ ++ Δ₂ ⊢ v' Valid

    τ-valid-inst : valid-instᵗ Type
    τ-valid-inst Δ₁ {Δ₂} i⋆ {α⁼ ι} (valid-α⁼ l)
      with Nat-cmp ι (length Δ₁)
    ... | tri< ι<len _ _ = α⁼ ι , subst-α-< ι<len , valid-α⁼ (↓-add-right Δ₂ (↓-remove-right Δ₁ ι<len l))
    τ-valid-inst Δ₁ {Δ₂} {i = α τ} (of-α τ⋆) {α⁼ .(length Δ₁)} (valid-α⁼ l)
        | tri≈ _ refl _ = weaken 0 (length Δ₁) τ , subst-α-≡ , τ-valid-weaken [] Δ₁ Δ₂ τ⋆
    τ-valid-inst Δ₁ {Δ₂} (of-ρ σ⋆) {α⁼ .(length Δ₁)} (valid-α⁼ l)
        | tri≈ _ refl _
      with ↓-remove-left Δ₁ (NP.n≤m+n 0 (length Δ₁)) l
    ... | l'
      rewrite NP.n∸n≡0 (length Δ₁)
      with l'
    ... | ()
    τ-valid-inst Δ₁ {Δ₂} {a} {τ} i⋆ {α⁼ (suc ι)} (valid-α⁼ l)
        | tri> _ _ (s≤s ι≥len)
      rewrite sym (List-++-assoc Δ₁ [ a ] Δ₂)
      with ↓-add-left Δ₁ (↓-remove-left (Δ₁ ++ [ a ]) (≤-help Δ₁ a ι≥len) l)
    ... | l'
      rewrite eq-help Δ₁ a
            | NP.m+n∸m≡n ι≥len
      = α⁼ ι , subst-α-> (s≤s ι≥len) , valid-α⁼ l'
    τ-valid-inst Δ₁ i⋆ valid-int = int , subst-int , valid-int
    τ-valid-inst Δ₁ i⋆ valid-ns = ns , subst-ns , valid-ns
    τ-valid-inst Δ₁ {Δ₂} {a} i⋆ {∀[ Δ ] Γ} (valid-∀ Γ⋆)
      rewrite sym (List-++-assoc Δ Δ₁ (a ∷ Δ₂))
      with Γ-valid-inst (Δ ++ Δ₁) i⋆ Γ⋆
    ... | Γ' , sub-Γ , Γ'⋆
      rewrite List-++-assoc Δ Δ₁ Δ₂
            | List-length-++ Δ {Δ₁}
        = ∀[ Δ ] Γ' , subst-∀ sub-Γ , valid-∀ Γ'⋆
    τ-valid-inst Δ₁ i⋆ (valid-tuple τs⁻⋆)
      = Σ-map tuple (Σ-map subst-tuple valid-tuple) (τs⁻-valid-inst Δ₁ i⋆ τs⁻⋆)

    τ⁻-valid-inst : valid-instᵗ InitType
    τ⁻-valid-inst Δ₁ i⋆ (valid-τ⁻ τ'⋆)
      = Σ-map _ (Σ-map subst-τ⁻ valid-τ⁻) (τ-valid-inst Δ₁ i⋆ τ'⋆)

    τs⁻-valid-inst : valid-instᵗ (List InitType)
    τs⁻-valid-inst Δ₁ i⋆ [] = [] , [] , []
    τs⁻-valid-inst Δ₁ i⋆ (τ⁻⋆ ∷ τs⁻⋆)
      = Σ-zip _∷_ (Σ-zip _∷_ _∷_) (τ⁻-valid-inst Δ₁ i⋆ τ⁻⋆) (τs⁻-valid-inst Δ₁ i⋆ τs⁻⋆)

    σ-valid-inst : valid-instᵗ StackType
    σ-valid-inst Δ₁ {Δ₂} i⋆ {ρ⁼ ι} (valid-ρ⁼ l)
      with Nat-cmp ι (length Δ₁)
    ... | tri< ι<len _ _ = ρ⁼ ι , subst-ρ-< ι<len , valid-ρ⁼ (↓-add-right Δ₂ (↓-remove-right Δ₁ ι<len l))
    σ-valid-inst Δ₁ {Δ₂} {i = α τ} (of-α τ⋆) {ρ⁼ .(length Δ₁)} (valid-ρ⁼ l)
        | tri≈ _ refl _
      with ↓-remove-left Δ₁ (NP.n≤m+n 0 (length Δ₁)) l
    ... | l'
      rewrite NP.n∸n≡0 (length Δ₁)
      with l'
    ... | ()
    σ-valid-inst Δ₁ {Δ₂} {i = ρ σ} (of-ρ σ⋆) {ρ⁼ .(length Δ₁)} (valid-ρ⁼ l)
        | tri≈ _ refl _ = weaken 0 (length Δ₁) σ , subst-ρ-≡ , σ-valid-weaken [] Δ₁ Δ₂ σ⋆
    σ-valid-inst Δ₁ {Δ₂} {a} i⋆ {ρ⁼ (suc ι)} (valid-ρ⁼ l)
        | tri> _ _ (s≤s ι≥len)
      rewrite sym (List-++-assoc Δ₁ [ a ] Δ₂)
      with ↓-add-left Δ₁ (↓-remove-left (Δ₁ ++ [ a ]) (≤-help Δ₁ a ι≥len) l)
    ... | l'
      rewrite eq-help Δ₁ a
            | NP.m+n∸m≡n ι≥len
      = ρ⁼ ι , subst-ρ-> (s≤s ι≥len) , valid-ρ⁼ l'
    σ-valid-inst Δ₁ i⋆ [] = [] , [] , []
    σ-valid-inst Δ₁ i⋆ (τ'⋆ ∷ σ⋆)
      = Σ-zip _∷_ (Σ-zip _∷_ _∷_) (τ-valid-inst Δ₁ i⋆ τ'⋆) (σ-valid-inst Δ₁ i⋆ σ⋆)

    Γ-valid-inst : valid-instᵗ RegisterAssignment
    Γ-valid-inst Δ₁ i⋆ (valid-registerₐ sp⋆ regs⋆)
      = Σ-zip registerₐ (Σ-zip subst-registerₐ valid-registerₐ) (σ-valid-inst Δ₁ i⋆ sp⋆) (regs-valid-inst Δ₁ i⋆ regs⋆)

    regs-valid-inst : ∀ {n} → valid-instᵗ (Vec Type n)
    regs-valid-inst Δ₁ i⋆ [] = [] , [] , []
    regs-valid-inst Δ₁ i⋆ (τ'⋆ ∷ τs⋆)
      = Σ-zip _∷_ (Σ-zip _∷_ _∷_) (τ-valid-inst Δ₁ i⋆ τ'⋆) (regs-valid-inst Δ₁ i⋆ τs⋆)

  mutual
    outside-ctxᵗ : ∀ A {{_ : Substitution A}}
                       {{_ : TypeLike A}} → Set
    outside-ctxᵗ A = ∀ {Δ i ι} {v : A} →
                       Δ ⊢ v Valid →
                       v ⟦ i / length Δ + ι ⟧≡ v

    τ-outside-ctx : outside-ctxᵗ Type
    τ-outside-ctx {Δ} {ι = ι} (valid-α⁼ l) =
      subst-α-< (Nat-≤-trans (↓-to-< l) (NP.m≤m+n (length Δ) ι))
    τ-outside-ctx valid-int = subst-int
    τ-outside-ctx valid-ns = subst-ns
    τ-outside-ctx {Δ} {i} {ι} {∀[ Δ' ] Γ} (valid-∀ Γ⋆)
      with Γ-outside-ctx {Δ' ++ Δ} {i} {ι} Γ⋆
    ... | sub-Γ
      rewrite List-length-++ Δ' {Δ}
            | +-assoc (length Δ') (length Δ) ι = subst-∀ sub-Γ
    τ-outside-ctx (valid-tuple τs⁻⋆) = subst-tuple (τs⁻-outside-ctx τs⁻⋆)

    τ⁻-outside-ctx : outside-ctxᵗ InitType
    τ⁻-outside-ctx (valid-τ⁻ τ⋆) = subst-τ⁻ (τ-outside-ctx τ⋆)

    τs⁻-outside-ctx : outside-ctxᵗ (List InitType)
    τs⁻-outside-ctx [] = []
    τs⁻-outside-ctx (τ⁻⋆ ∷ τs⁻⋆) = τ⁻-outside-ctx τ⁻⋆ ∷ τs⁻-outside-ctx τs⁻⋆

    σ-outside-ctx : outside-ctxᵗ StackType
    σ-outside-ctx {Δ} {ι = ι} (valid-ρ⁼ l) =
      subst-ρ-< (Nat-≤-trans (↓-to-< l) (NP.m≤m+n (length Δ) ι))
    σ-outside-ctx [] = []
    σ-outside-ctx (τ⋆ ∷ σ⋆) = τ-outside-ctx τ⋆ ∷ σ-outside-ctx σ⋆

    Γ-outside-ctx : outside-ctxᵗ RegisterAssignment
    Γ-outside-ctx (valid-registerₐ sp⋆ regs⋆) =
      subst-registerₐ (σ-outside-ctx sp⋆) (regs-outside-ctx regs⋆)

    regs-outside-ctx : ∀ {m} → outside-ctxᵗ (Vec Type m)
    regs-outside-ctx [] = []
    regs-outside-ctx (τ⋆ ∷ τs⋆) = τ-outside-ctx τ⋆ ∷ regs-outside-ctx τs⋆

Vec-TypeSubstitution :
  ∀ A {S S⁺ T} {{TS : TypeSubstitution A {S} {{S⁺}} {{T}}}} n →
    TypeSubstitution (Vec A n) {{Vec-Substitution⁺ A n}} {{Vec-TypeLike A n}}
Vec-TypeSubstitution A {S} {S⁺} {T} {{TS}} n =
    typeSubstitution xs-valid-weaken xs-valid-inst xs-outside-ctx
  where xs-valid-weaken :
          ∀ {n} (Δ₁ Δ₂ Δ₃ : TypeAssumptions) {xs : Vec A n} →
            _⊢_Valid {{Vec-TypeLike A n}} (Δ₁ ++ Δ₃) xs →
            _⊢_Valid {{Vec-TypeLike A n}} (Δ₁ ++ Δ₂ ++ Δ₃)
              (weaken {{Vec-Substitution A n}} (length Δ₁) (length Δ₂) xs)
        xs-valid-weaken Δ₁ Δ₂ Δ₃ [] = []
        xs-valid-weaken Δ₁ Δ₂ Δ₃ (x⋆ ∷ xs⋆) =
          subst-valid-weaken {{TS}} Δ₁ Δ₂ Δ₃ x⋆ ∷ xs-valid-weaken Δ₁ Δ₂ Δ₃ xs⋆

        xs-valid-inst :
          ∀ {n} Δ₁ {Δ₂ a i} →
            Δ₂ ⊢ i of a instantiation →
            {xs : Vec A n} →
            _⊢_Valid {{Vec-TypeLike A n}} (Δ₁ ++ a ∷ Δ₂) xs →
            ∃ λ xs' →
              _⟦_/_⟧≡_ {{Vec-Substitution A n}} xs i (length Δ₁) xs' ×
              _⊢_Valid {{Vec-TypeLike A n}} (Δ₁ ++ Δ₂) xs'
        xs-valid-inst Δ₁ i⋆ [] = [] , [] , []
        xs-valid-inst Δ₁ i⋆ (x⋆ ∷ xs⋆) =
          Σ-zip _∷_ (Σ-zip _∷_ _∷_) (subst-valid-inst {{TS}} Δ₁ i⋆ x⋆) (xs-valid-inst Δ₁ i⋆ xs⋆)

        xs-outside-ctx :
          ∀ {Δ i ι n} {xs : Vec A n} →
            _⊢_Valid {{Vec-TypeLike A n}} Δ xs →
            _⟦_/_⟧≡_ {{Vec-Substitution A n}} xs i (length Δ + ι) xs
        xs-outside-ctx [] = []
        xs-outside-ctx (x⋆ ∷ xs⋆) = subst-outside-ctx {{TS}} x⋆ ∷ xs-outside-ctx xs⋆

List-TypeSubstitution :
  ∀ A {S S⁺ T} {{TS : TypeSubstitution A {S} {{S⁺}} {{T}}}} →
    TypeSubstitution (List A) {{List-Substitution⁺ A}} {{List-TypeLike A}}
List-TypeSubstitution A {S} {S⁺} {T} {{TS}} =
    typeSubstitution xs-valid-weaken xs-valid-inst xs-outside-ctx
  where xs-valid-weaken :
          ∀ (Δ₁ Δ₂ Δ₃ : TypeAssumptions) {xs : List A} →
            _⊢_Valid {{List-TypeLike A}} (Δ₁ ++ Δ₃) xs →
            _⊢_Valid {{List-TypeLike A}} (Δ₁ ++ Δ₂ ++ Δ₃)
              (weaken {{List-Substitution A}} (length Δ₁) (length Δ₂) xs)
        xs-valid-weaken Δ₁ Δ₂ Δ₃ [] = []
        xs-valid-weaken Δ₁ Δ₂ Δ₃ (x⋆ ∷ xs⋆) =
          subst-valid-weaken {{TS}} Δ₁ Δ₂ Δ₃ x⋆ ∷ xs-valid-weaken Δ₁ Δ₂ Δ₃ xs⋆

        xs-valid-inst :
          ∀ Δ₁ {Δ₂ a i} →
            Δ₂ ⊢ i of a instantiation →
            {xs : List A} →
            _⊢_Valid {{List-TypeLike A}} (Δ₁ ++ a ∷ Δ₂) xs →
            ∃ λ xs' →
              _⟦_/_⟧≡_ {{List-Substitution A}} xs i (length Δ₁) xs' ×
              _⊢_Valid {{List-TypeLike A}} (Δ₁ ++ Δ₂) xs'
        xs-valid-inst Δ₁ i⋆ [] = [] , [] , []
        xs-valid-inst Δ₁ i⋆ (x⋆ ∷ xs⋆) =
          Σ-zip _∷_ (Σ-zip _∷_ _∷_) (subst-valid-inst {{TS}} Δ₁ i⋆ x⋆) (xs-valid-inst Δ₁ i⋆ xs⋆)

        xs-outside-ctx :
          ∀ {Δ i ι} {xs : List A} →
            _⊢_Valid {{List-TypeLike A}} Δ xs →
            _⟦_/_⟧≡_ {{List-Substitution A}} xs i (length Δ + ι) xs
        xs-outside-ctx [] = []
        xs-outside-ctx (x⋆ ∷ xs⋆) = subst-outside-ctx {{TS}} x⋆ ∷ xs-outside-ctx xs⋆

instance
  Type-TypeSubstitution : TypeSubstitution Type
  Type-TypeSubstitution =
    typeSubstitution τ-valid-weaken τ-valid-inst τ-outside-ctx

  TypeVec-TypeSubstitution : ∀ {m} → TypeSubstitution (Vec Type m)
  TypeVec-TypeSubstitution = typeSubstitution regs-valid-weaken regs-valid-inst regs-outside-ctx

  TypeList-TypeSubstitution : TypeSubstitution (List Type)
  TypeList-TypeSubstitution = List-TypeSubstitution Type

  InitType-TypeSubstitution : TypeSubstitution InitType
  InitType-TypeSubstitution = typeSubstitution
    τ⁻-valid-weaken τ⁻-valid-inst τ⁻-outside-ctx

  InitTypeVec-TypeSubstitution : ∀ {m} → TypeSubstitution (Vec InitType m)
  InitTypeVec-TypeSubstitution = Vec-TypeSubstitution InitType _

  InitTypeList-TypeSubstitution : TypeSubstitution (List InitType)
  InitTypeList-TypeSubstitution = typeSubstitution τs⁻-valid-weaken τs⁻-valid-inst τs⁻-outside-ctx

  StackType-TypeSubstitution : TypeSubstitution StackType
  StackType-TypeSubstitution = typeSubstitution
    σ-valid-weaken σ-valid-inst σ-outside-ctx

  RegisterAssignment-TypeSubstitution : TypeSubstitution RegisterAssignment
  RegisterAssignment-TypeSubstitution = typeSubstitution
    Γ-valid-weaken Γ-valid-inst Γ-outside-ctx
