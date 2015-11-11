module Lemmas.TypeSubstitution where

open import Util
open import Judgments
open import Lemmas.Misc
open import Lemmas.Substitution

import Data.Nat.Properties as NP

-- The purpose of this file is
-- to include instances of this record.
record TypeSubstitution (A : Set) {S} {{S⁺ : Substitution⁺ A {{S}}}}
                                  {{T : TypeLike A}} : Set where
  constructor typeSubstitution
  field
    subst-valid-inst :
      ∀ {Δ₁ Δ₁' Δ₂ a i} →
        a ∷ Δ₂ ⊢ i Valid →
        Δ₁ ⟦ inst {W = ℕ} i / zero ⟧≡ Δ₁' →
        {v : A} →
        Δ₁ ++ a ∷ Δ₂ ⊢ v Valid →
        ∃ λ v' →
          v ⟦ inst i / length Δ₁ ⟧≡ v' ×
          Δ₁' ++ Δ₂ ⊢ v' Valid
    subst-valid-weaken :
      ∀ Δ⁺ {Δ₁ Δ₁' Δ₂} →
        Δ₁ ⟦ weaken (length Δ⁺) / zero ⟧≡ Δ₁' →
        {v : A} →
        Δ₁ ++ Δ₂ ⊢ v Valid →
        ∃ λ v' →
          v ⟦ weaken (length Δ⁺) / length Δ₁ ⟧≡ v' ×
          Δ₁' ++ Δ⁺ ++ Δ₂ ⊢ v' Valid
    subst-valid-pre :
      ∀ {Δ₁ Δ₂ cᵥ ι} {v v' : A} →
        Run Δ₁ ⟦ cᵥ / ι ⟧≡ Δ₂ →
        v ⟦ Strong→Weak cᵥ / ι ⟧≡ v' →
        Δ₂ ⊢ v' Valid →
        Δ₁ ⊢ v Valid
    subst-outside-ctx :
      ∀ {Δ cᵥ ι} {v : A} →
        Δ ⊢ v Valid →
        v ⟦ cᵥ / length Δ + ι ⟧≡ v
  can-subst : ∀ {Δ Δ' cᵥ ι} {v : A} →
                Δ ⊢ cᵥ / ι Valid →
                Run Δ ⟦ cᵥ / ι ⟧≡ Δ' →
                Δ ⊢ v Valid →
                ∃ λ v' →
                  v ⟦ Strong→Weak cᵥ / ι ⟧≡ v' ×
                  Δ' ⊢ v' Valid
  can-subst {cᵥ = inst i} {ι} c⋆ run-Δ v⋆ with run-split run-Δ
  ... | Δ₁ , Δ₁' , (a ∷ Δ₂) , .Δ₂ , sub-Δ₁ , run-inst m , eq₁ , eq₂ , eq₃
    rewrite eq₁ | eq₂ | eq₃ with valid-i-split Δ₁ c⋆
  ... | valid-inst i⋆ = subst-valid-inst i⋆ sub-Δ₁ v⋆
  can-subst {cᵥ = weaken Δ⁺} {ι} c⋆ run-Δ v⋆ with run-split run-Δ
  ... | Δ₁ , Δ₁' , Δ₂ , .(Δ⁺ ++ Δ₂) , sub-Δ₁ , run-weaken , eq₁ , eq₂ , eq₃
    rewrite eq₁ | eq₂ | eq₃ =
      subst-valid-weaken Δ⁺ sub-Δ₁ v⋆

  subst-valid : ∀ {Δ Δ' cᵥ ι} {v v' : A} →
                  Δ ⊢ cᵥ / ι Valid →
                  Run Δ ⟦ cᵥ / ι ⟧≡ Δ' →
                  Δ ⊢ v Valid →
                  v ⟦ Strong→Weak cᵥ / ι ⟧≡ v' →
                  Δ' ⊢ v' Valid
  subst-valid c⋆ run-Δ v⋆ sub-v
    with can-subst c⋆ run-Δ v⋆
  ... | v'' , sub-v'' , v''⋆ with subst-unique sub-v sub-v''
  ... | eq rewrite eq = v''⋆
open TypeSubstitution {{...}} public

private
  mutual
    valid-weakenᵗ : ∀ A {{_ : Substitution A}}
                        {{_ : TypeLike A}} → Set
    valid-weakenᵗ A = ∀ Δ⁺ {Δ₁ Δ₁' Δ₂} →
                        Δ₁ ⟦ weaken (length Δ⁺) / zero ⟧≡ Δ₁' →
                        {v : A} →
                        Δ₁ ++ Δ₂ ⊢ v Valid →
                        ∃ λ v' →
                          v ⟦ weaken (length Δ⁺) / length Δ₁ ⟧≡ v' ×
                          Δ₁' ++ Δ⁺ ++ Δ₂ ⊢ v' Valid

    τ-valid-weaken : valid-weakenᵗ Type
    τ-valid-weaken Δ⁺ {Δ₁} {Δ₁'} {Δ₂} sub-Δ (valid-α⁼ {ι} l)
      with length Δ₁ ≤? ι
    ... | yes ι≥len = α⁼ (length Δ⁺ + ι) ,
                      subst-α-¬inst (subst-weaken-≥ ι≥len) ,
                      valid-α⁼
                      (subst-↓-replace sub-Δ (NP.≤-steps (length Δ⁺) ι≥len)
                                             (↓-add-middle Δ₁ Δ⁺ ι≥len l))
    ... | no ι≱len with NP.≰⇒> ι≱len
    ... | ι<len with subst-↓ (↓-remove-right Δ₂ ι<len l) sub-Δ
    ... | α , l' , subst-α = α⁼ ι , subst-α-¬inst (subst-< ι<len) ,
                                    valid-α⁼ (↓-add-right (Δ⁺ ++ Δ₂) l')
    τ-valid-weaken Δ⁺ sub-Δ valid-int = int , subst-int , valid-int
    τ-valid-weaken Δ⁺ sub-Δ valid-ns = ns , subst-ns , valid-ns
    τ-valid-weaken Δ⁺ {Δ₁} {Δ₁'} {Δ₂} sub-Δ (valid-∀ {Δ} {Γ} Δ⋆ Γ⋆)
      with Δ-valid-weaken Δ⁺ sub-Δ Δ⋆
    ... | Δ' , sub-Δ' , Δ'⋆
      rewrite sym (List-++-assoc Δ Δ₁ Δ₂)
      with Γ-valid-weaken Δ⁺ (subst-combine sub-Δ' sub-Δ) Γ⋆
    ... | Γ' , sub-Γ , Γ'⋆
      rewrite List-length-++ Δ {Δ₁}
            | List-++-assoc Δ' Δ₁' (Δ⁺ ++ Δ₂)
       = ∀[ Δ' ] Γ' , subst-∀ sub-Δ' sub-Γ , valid-∀ Δ'⋆ Γ'⋆
    τ-valid-weaken Δ⁺ sub-Δ (valid-tuple τs⁻)
      with τs⁻-valid-weaken Δ⁺ sub-Δ τs⁻
    ... | τs⁻' , sub-τs⁻ , τs⁻'⋆ =
      tuple τs⁻' , subst-tuple sub-τs⁻ , valid-tuple τs⁻'⋆

    τ⁻-valid-weaken : valid-weakenᵗ InitType
    τ⁻-valid-weaken Δ⁺ sub-Δ (valid-τ⁻ τ⋆)
      with τ-valid-weaken Δ⁺ sub-Δ τ⋆
    ... | τ' , sub-τ , τ'⋆ = _ , subst-τ⁻ sub-τ , valid-τ⁻ τ'⋆

    τs⁻-valid-weaken : valid-weakenᵗ (List InitType)
    τs⁻-valid-weaken Δ⁺ sub-Δ [] = [] , [] , []
    τs⁻-valid-weaken Δ⁺ sub-Δ (τ⁻⋆ ∷ τs⁻⋆)
      with τ⁻-valid-weaken Δ⁺ sub-Δ τ⁻⋆
         | τs⁻-valid-weaken Δ⁺ sub-Δ τs⁻⋆
    ...  | τ⁻' , sub-τ⁻ , τ⁻'⋆ | τs⁻' , sub-τs⁻ , τs⁻'⋆
      = τ⁻' ∷ τs⁻' , sub-τ⁻ ∷ sub-τs⁻ , τ⁻'⋆ ∷ τs⁻'⋆

    σ-valid-weaken : valid-weakenᵗ StackType
    σ-valid-weaken Δ⁺ {Δ₁} {Δ₁'} {Δ₂} sub-Δ (valid-ρ⁼ {ι} l)
      with length Δ₁ ≤? ι
    ... | yes ι≥len = ρ⁼ (length Δ⁺ + ι) ,
                      subst-ρ-¬inst (subst-weaken-≥ ι≥len) ,
                      valid-ρ⁼
                      (subst-↓-replace sub-Δ (NP.≤-steps (length Δ⁺) ι≥len)
                                             (↓-add-middle Δ₁ Δ⁺ ι≥len l))
    ... | no ι≱len with NP.≰⇒> ι≱len
    ... | ι<len with subst-↓ (↓-remove-right Δ₂ ι<len l) sub-Δ
    ... | ρ , l' , subst-ρ = ρ⁼ ι , subst-ρ-¬inst (subst-< ι<len) ,
                                    valid-ρ⁼ (↓-add-right (Δ⁺ ++ Δ₂) l')
    σ-valid-weaken Δ⁺ sub-Δ valid-[] = [] , subst-[] , valid-[]
    σ-valid-weaken Δ⁺ sub-Δ (τ⋆ ∷ σ⋆)
      with τ-valid-weaken Δ⁺ sub-Δ τ⋆
         | σ-valid-weaken Δ⁺ sub-Δ σ⋆
    ...  | τ' , sub-τ , τ'⋆ | σ' , sub-σ , σ'⋆
      = τ' ∷ σ' , sub-τ ∷ sub-σ , τ'⋆ ∷ σ'⋆

    Δ-valid-weaken : valid-weakenᵗ TypeAssignment
    Δ-valid-weaken Δ⁺ sub-Δ [] = [] , [] , []
    Δ-valid-weaken Δ⁺ {Δ₁} {Δ₁'} {Δ₂} sub-Δ {a ∷ Δ} (a⋆ ∷ Δ⋆)
      with Δ-valid-weaken Δ⁺ sub-Δ Δ⋆
    ... | Δ' , sub-Δ' , Δ'⋆
      rewrite sym (List-++-assoc Δ Δ₁ Δ₂)
      with a-valid-weaken Δ⁺ (subst-combine sub-Δ' sub-Δ) a⋆
    ... | a' , sub-a , a'⋆
      rewrite List-length-++ Δ {Δ₁}
            | List-++-assoc Δ' Δ₁' (Δ⁺ ++ Δ₂)
      = a' ∷ Δ' , sub-a ∷ sub-Δ' , a'⋆ ∷ Δ'⋆

    a-valid-weaken : valid-weakenᵗ TypeAssignmentValue
    a-valid-weaken Δ⁺ sub-Δ valid-α = α , subst-α , valid-α
    a-valid-weaken Δ⁺ sub-Δ valid-ρ = ρ , subst-ρ , valid-ρ

    Γ-valid-weaken : valid-weakenᵗ RegisterAssignment
    Γ-valid-weaken Δ⁺ sub-Δ (valid-registerₐ sp⋆ regs⋆)
      with σ-valid-weaken Δ⁺ sub-Δ sp⋆
         | regs-valid-weaken Δ⁺ sub-Δ regs⋆
    ...  | sp' , sub-sp , sp'⋆ | regs' , sub-regs , regs'⋆
      = registerₐ sp' regs' ,
        subst-registerₐ sub-sp sub-regs ,
        valid-registerₐ sp'⋆ regs'⋆

    regs-valid-weaken : ∀ {m} → valid-weakenᵗ (Vec Type m)
    regs-valid-weaken Δ⁺ sub-Δ [] = [] , [] , []
    regs-valid-weaken Δ⁺ sub-Δ (τ⋆ ∷ τs⋆)
      with τ-valid-weaken Δ⁺ sub-Δ τ⋆
         | regs-valid-weaken Δ⁺ sub-Δ τs⋆
    ...  | τ' , sub-τ , τ'⋆ | τs' , sub-τs , τs'⋆
      = τ' ∷ τs' , sub-τ ∷ sub-τs , τ'⋆ ∷ τs'⋆

  mutual
    valid-instᵗ : ∀ A {{_ : Substitution A}}
                      {{_ : TypeLike A}} → Set
    valid-instᵗ T = ∀ {Δ₁ Δ₁' Δ₂ a i} →
                       a ∷ Δ₂ ⊢ i Valid →
                       Δ₁ ⟦ inst {W = ℕ} i / zero ⟧≡ Δ₁' →
                       {v : T} →
                       Δ₁ ++ a ∷ Δ₂ ⊢ v Valid →
                       ∃ λ v' →
                         v ⟦ inst {W = ℕ} i / length Δ₁ ⟧≡ v' ×
                         Δ₁' ++ Δ₂ ⊢ v' Valid

    τ-valid-inst : valid-instᵗ Type
    τ-valid-inst {Δ₁} {Δ₁'} {Δ₂} {a} i⋆ sub-Δ {α⁼ ι} (valid-α⁼ l)
      with Nat-cmp ι (length Δ₁)
    ... | tri< ι<len _ _
      with subst-↓ (↓-remove-right (a ∷ Δ₂) ι<len l) sub-Δ
    ... | α , l' , subst-α =
      α⁼ ι , subst-α-¬inst (subst-< ι<len) , valid-α⁼ (↓-add-right Δ₂ l')
    τ-valid-inst {Δ₁} {Δ₁'} {Δ₂} {a} i⋆ sub-Δ {α⁼ ._} (valid-α⁼ l)
        | tri≈ _ refl _
      with subst (λ i → a ∷ Δ₂ ↓ i ⇒ α)
                 (NP.n∸n≡0 (length Δ₁))
                 (↓-remove-left Δ₁ (NP.n≤m+n 0 (length Δ₁)) l)
    τ-valid-inst {Δ₁} {Δ₁'} (valid-α {τ = τ} τ⋆) sub-Δ {α⁼ ._} (valid-α⁼ l)
        | tri≈ _ refl _ | here
      with τ-valid-weaken Δ₁' [] τ⋆
    ... | τ' , sub-τ , τ'⋆ rewrite subst-length sub-Δ
      = τ' , subst-α-inst sub-τ , τ'⋆
    τ-valid-inst {Δ₁} {Δ₁'} {Δ₂} {a} i⋆ sub-Δ {α⁼ .(suc ι)} (valid-α⁼ l)
        | tri> _ _ (s≤s {n = ι} ι≥len)
      with begin
             length (Δ₁ ++ [ a ])
           ≡⟨ List-length-++ Δ₁ ⟩
             length Δ₁ + 1
           ≡⟨ +-comm (length Δ₁) 1 ⟩
             suc (length Δ₁)
           ∎ where open Eq-Reasoning
    ... | eq
      rewrite sym (List-++-assoc Δ₁ [ a ] Δ₂)
      with ↓-add-left Δ₁' (↓-remove-left
                            (Δ₁ ++ [ a ])
                            (subst (_≥_ (suc ι)) (sym eq) (s≤s ι≥len))
                            l)
    ... | l' rewrite eq | sym (subst-length sub-Δ) | NP.m+n∸m≡n ι≥len
      = α⁼ ι , subst-α-¬inst (subst-inst-> (s≤s ι≥len)) , valid-α⁼ l'
    τ-valid-inst i⋆ sub-Δ valid-int = int , subst-int , valid-int
    τ-valid-inst i⋆ sub-Δ valid-ns = ns , subst-ns , valid-ns
    τ-valid-inst {Δ₁} {Δ₁'} {i = i} i⋆ sub-Δ {∀[ Δ ] Γ} (valid-∀ Δ⋆ Γ⋆)
      with Δ-valid-inst i⋆ sub-Δ Δ⋆
    ... | Δ' , sub-Δ' , Δ'⋆
      with Γ-valid-inst i⋆ (subst-combine sub-Δ' sub-Δ)
             (subst₂ _⊢_Valid (sym (List-++-assoc Δ Δ₁ _)) refl Γ⋆)
    ... | Γ' , sub-Γ , Γ'⋆ =
      (∀[ Δ' ] Γ') ,
      subst-∀ sub-Δ' (ι-subst (List-length-++ Δ) sub-Γ) ,
      valid-∀ Δ'⋆ (subst₂ _⊢_Valid (List-++-assoc Δ' Δ₁' _) refl Γ'⋆)
    τ-valid-inst i⋆ sub-Δ (valid-tuple τs⁻⋆)
      with τs⁻-valid-inst i⋆ sub-Δ τs⁻⋆
    ... | τs⁻' , sub-τs⁻ , τs⁻'⋆ =
      tuple τs⁻' ,
      subst-tuple sub-τs⁻ ,
      valid-tuple τs⁻'⋆

    τ⁻-valid-inst : valid-instᵗ InitType
    τ⁻-valid-inst i⋆ sub-Δ (valid-τ⁻ τ⋆)
      with τ-valid-inst i⋆ sub-Δ τ⋆
    ... | τ' , sub-τ , τ'⋆ = _ , subst-τ⁻ sub-τ , valid-τ⁻ τ'⋆

    τs⁻-valid-inst : valid-instᵗ (List InitType)
    τs⁻-valid-inst i⋆ sub-Δ [] = [] , [] , []
    τs⁻-valid-inst i⋆ sub-Δ (τ⁻⋆ ∷ τs⁻⋆)
      with τ⁻-valid-inst i⋆ sub-Δ τ⁻⋆
         | τs⁻-valid-inst i⋆ sub-Δ τs⁻⋆
    ... | τ⁻' , sub-τ⁻ , τ⁻'⋆
        | τs⁻' , sub-τs⁻ , τs⁻'⋆ =
            τ⁻' ∷ τs⁻' , sub-τ⁻ ∷ sub-τs⁻ , τ⁻'⋆ ∷ τs⁻'⋆

    σ-valid-inst : valid-instᵗ StackType
    σ-valid-inst {Δ₁} {Δ₁'} {Δ₂} {a} i⋆ sub-Δ {ρ⁼ ι} (valid-ρ⁼ l)
      with Nat-cmp ι (length Δ₁)
    ... | tri< ι<len _ _
      with subst-↓ (↓-remove-right (a ∷ Δ₂) ι<len l) sub-Δ
    ... | ρ , l' , subst-ρ = ρ⁼ ι ,
                             subst-ρ-¬inst (subst-< ι<len) ,
                             valid-ρ⁼ (↓-add-right Δ₂ l')
    σ-valid-inst {Δ₁} {Δ₁'} {Δ₂} {a} i⋆ sub-Δ {ρ⁼ ._} (valid-ρ⁼ l)
        | tri≈ _ refl _
      with subst (λ i → a ∷ Δ₂ ↓ i ⇒ ρ)
                 (NP.n∸n≡0 (length Δ₁))
                 (↓-remove-left Δ₁ (NP.n≤m+n 0 (length Δ₁)) l)
    σ-valid-inst {Δ₁} {Δ₁'} (valid-ρ {σ = σ} σ⋆) sub-Δ {ρ⁼ ._} (valid-ρ⁼ l)
        | tri≈ _ refl _ | here
      with σ-valid-weaken Δ₁' [] σ⋆
    ... | σ' , sub-σ , σ'⋆ rewrite subst-length sub-Δ
      = σ' , subst-ρ-inst sub-σ , σ'⋆
    σ-valid-inst {Δ₁} {Δ₁'} {Δ₂} {a} i⋆ sub-Δ {ρ⁼ .(suc ι)} (valid-ρ⁼ l)
        | tri> _ _ (s≤s {n = ι} ι≥len)
      with begin
             length (Δ₁ ++ [ a ])
           ≡⟨ List-length-++ Δ₁ ⟩
             length Δ₁ + 1
           ≡⟨ +-comm (length Δ₁) 1 ⟩
             suc (length Δ₁)
           ∎ where open Eq-Reasoning
    ... | eq
      rewrite sym (List-++-assoc Δ₁ [ a ] Δ₂)
      with ↓-add-left Δ₁' (↓-remove-left
                            (Δ₁ ++ [ a ])
                            (subst (_≥_ (suc ι)) (sym eq) (s≤s ι≥len))
                            l)
    ... | l' rewrite eq | sym (subst-length sub-Δ) | NP.m+n∸m≡n ι≥len
      = ρ⁼ ι , subst-ρ-¬inst (subst-inst-> (s≤s ι≥len)) , valid-ρ⁼ l'
    σ-valid-inst i⋆ sub-Δ valid-[] = [] , subst-[] , valid-[]
    σ-valid-inst i⋆ sub-Δ (τ⋆ ∷ σ⋆)
      with τ-valid-inst i⋆ sub-Δ τ⋆
         | σ-valid-inst i⋆ sub-Δ σ⋆
    ... | τ' , sub-τ , τ'⋆
        | σ' , sub-σ , σ'⋆ = τ' ∷ σ' , sub-τ ∷ sub-σ , τ'⋆ ∷ σ'⋆

    Δ-valid-inst : valid-instᵗ TypeAssignment
    Δ-valid-inst i⋆ sub-Δ [] = [] , [] , []
    Δ-valid-inst {Δ₁} {Δ₁'} {Δ₂} i⋆ sub-Δ {a ∷ Δ} (a⋆ ∷ Δ⋆)
      with Δ-valid-inst i⋆ sub-Δ Δ⋆
    ... | Δ' , sub-Δ' , Δ'⋆
      with a-valid-inst i⋆ (subst-combine sub-Δ' sub-Δ)
             (subst₂ _⊢_Valid (sym (List-++-assoc Δ Δ₁ _) ) refl a⋆)
    ... | a' , sub-a , a'⋆
      rewrite List-length-++ Δ {Δ₁} |
              List-++-assoc Δ' Δ₁' Δ₂
        = a' ∷ Δ' , sub-a ∷ sub-Δ' , a'⋆ ∷ Δ'⋆

    a-valid-inst : valid-instᵗ TypeAssignmentValue
    a-valid-inst i⋆ sub-Δ valid-α = α , subst-α , valid-α
    a-valid-inst i⋆ sub-Δ valid-ρ = ρ , subst-ρ , valid-ρ

    Γ-valid-inst : valid-instᵗ RegisterAssignment
    Γ-valid-inst i⋆ sub-Δ (valid-registerₐ sp⋆ regs⋆)
      with σ-valid-inst i⋆ sub-Δ sp⋆
         | regs-valid-inst i⋆ sub-Δ regs⋆
    ... | sp' , sub-sp , sp'⋆
        | regs' , sub-regs , regs'⋆ = registerₐ sp' regs' ,
                                      subst-registerₐ sub-sp sub-regs ,
                                      valid-registerₐ sp'⋆ regs'⋆

    regs-valid-inst : ∀ {m} → valid-instᵗ (Vec Type m)
    regs-valid-inst i⋆ sub-Δ [] = [] , [] , []
    regs-valid-inst i⋆ sub-Δ (τ⋆ ∷ τs⋆)
      with τ-valid-inst i⋆ sub-Δ τ⋆
         | regs-valid-inst i⋆ sub-Δ τs⋆
    ... | τ' , sub-τ , τ'⋆
        | τs' , sub-τs , τs'⋆ = τ' ∷ τs' , sub-τ ∷ sub-τs , τ'⋆ ∷ τs'⋆

  mutual
    valid-preᵗ : ∀ A {{_ : Substitution A}}
                     {{_ : TypeLike A}} → Set
    valid-preᵗ A = ∀ {Δ₁ Δ₂ cᵥ ι} {v₁ v₂ : A} →
                     Run Δ₁ ⟦ cᵥ / ι ⟧≡ Δ₂ →
                     v₁ ⟦ Strong→Weak cᵥ / ι ⟧≡ v₂ →
                     Δ₂ ⊢ v₂ Valid →
                     Δ₁ ⊢ v₁ Valid

    τ-valid-pre : valid-preᵗ Type
    τ-valid-pre {cᵥ = inst i} {ι₂} {α⁼ ι₁} run-Δ
      (subst-α-¬inst (subst-< ι₁<ι₂)) (valid-α⁼ l)
      with run-split run-Δ
    ... | Δ₁ , Δ₁' , Δ₂ , Δ₂' , sub-Δ₁ , run-Δ₂ , eq₁ , eq₂ , eq₃
      rewrite eq₁ | eq₂ | eq₃
      with ↓-remove-right Δ₂'
             (subst (λ len → ι₁ < len) (subst-length sub-Δ₁) ι₁<ι₂) l
    ... | l' with subst-↓-pre l' sub-Δ₁
    ... | α , l'' , subst-α = valid-α⁼ (↓-add-right Δ₂ l'')
    τ-valid-pre {cᵥ = inst i} {ι₂} {α⁼ (suc ι₁)} run-Δ
      (subst-α-¬inst (subst-inst-> (s≤s ι₁≥ι₂))) (valid-α⁼ l)
      with run-split run-Δ
    ... | Δ₁ , Δ₁' , a ∷ .Δ₂' , Δ₂' , sub-Δ₁ , run-inst m , eq₁ , eq₂ , eq₃
      rewrite eq₁ | eq₂ | eq₃
      with ↓-remove-left Δ₁'
             (subst (λ len → ι₁ ≥ len) (subst-length sub-Δ₁) ι₁≥ι₂) l
    ... | l' with ↓-add-left Δ₁ (there {x = a} l')
    ... | l'' with
      begin
        length Δ₁ + suc (ι₁ ∸ length Δ₁')
      ⟨ subst-length sub-Δ₁ ∥ (λ v → length Δ₁ + suc (ι₁ ∸ v)) ⟩≡
        length Δ₁ + suc (ι₁ ∸ length Δ₁)
      ≡⟨ +-comm (length Δ₁) _ ⟩
        suc (ι₁ ∸ length Δ₁) + length Δ₁
      ≡⟨ refl ⟩
        suc (ι₁ ∸ length Δ₁ + length Δ₁)
      ≡⟨ +-comm _ (length Δ₁) ∥ (λ v → suc v) ⟩
        suc (length Δ₁ + (ι₁ ∸ length Δ₁))
      ≡⟨ NP.m+n∸m≡n ι₁≥ι₂ ∥ (λ v → suc v) ⟩
        suc ι₁
      ∎ where open Eq-Reasoning
    ... | eq rewrite eq = valid-α⁼ l''
    τ-valid-pre {cᵥ = inst (α τ)} {ι} {α⁼ .ι} run-Δ
      (subst-α-inst sub-τ) τ₂⋆ = valid-α⁼ (run-α⇒↓ run-Δ)
    τ-valid-pre {cᵥ = weaken Δ⁺} {ι₂} {α⁼ ι₁} run-Δ
      (subst-α-¬inst (subst-< ι₁<ι₂)) (valid-α⁼ l)
      with run-split run-Δ
    ... | Δ₁ , Δ₁' , Δ₂ , Δ₂' , sub-Δ₁ , run-Δ₂ , eq₁ , eq₂ , eq₃
      rewrite eq₁ | eq₂ | eq₃
      with ↓-remove-right {xs₁ = Δ₁'} Δ₂'
             (subst (λ len → ι₁ < len) (subst-length sub-Δ₁) ι₁<ι₂) l
    ... | l' with subst-↓-pre l' sub-Δ₁
    ... | α , l'' , subst-α = valid-α⁼ (↓-add-right Δ₂ l'')
    τ-valid-pre {cᵥ = weaken Δ⁺} {ι₂} {α⁼ ι₁} run-Δ
      (subst-α-¬inst (subst-weaken-≥ ι₁≥ι₂)) (valid-α⁼ l)
      with run-split run-Δ
    ... | Δ₁ , Δ₁' , Δ₂ , .(Δ⁺ ++ Δ₂) , sub-Δ₁ , run-weaken , eq₁ , eq₂ , eq₃
      rewrite eq₁ | eq₂ | eq₃ | subst-length sub-Δ₁
      with ↓-remove-left Δ₁' (Nat-≤-trans ι₁≥ι₂ (NP.n≤m+n (length Δ⁺) ι₁)) l
    ... | l'
      rewrite NP.+-∸-assoc (length Δ⁺) ι₁≥ι₂
      with ↓-remove-left Δ⁺ (NP.m≤m+n (length Δ⁺) _) l'
    ... | l'' with ↓-add-left Δ₁ l''
    ... | l''' with
      begin
        length Δ₁ + (length Δ⁺ + (ι₁ ∸ length Δ₁') ∸ length Δ⁺)
      ≡⟨ +-comm (length Δ⁺) _ ∥ (λ v → length Δ₁ + (v ∸ length Δ⁺)) ⟩
        length Δ₁ + (ι₁ ∸ length Δ₁' + length Δ⁺ ∸ length Δ⁺)
      ≡⟨ NP.m+n∸n≡m (ι₁ ∸ length Δ₁') (length Δ⁺) ∥ (λ v → length Δ₁ + v) ⟩
        length Δ₁ + (ι₁ ∸ length Δ₁')
      ≡⟨ subst-length sub-Δ₁ ∥ (λ v → v + (ι₁ ∸ length Δ₁')) ⟩
        length Δ₁' + (ι₁ ∸ length Δ₁')
      ≡⟨ NP.m+n∸m≡n ι₁≥ι₂ ⟩
        ι₁
      ∎ where open Eq-Reasoning
    ... | eq rewrite eq = valid-α⁼ l'''
    τ-valid-pre {v₁ = int} run-Δ subst-int valid-int = valid-int
    τ-valid-pre {v₁ = ns} run-Δ subst-ns valid-ns = valid-ns
    τ-valid-pre {v₁ = ∀[ Δ ] Γ} run-Δ
      (subst-∀ sub-Δ sub-Γ) (valid-∀ Δ₂⋆ Γ₂⋆) =
        valid-∀ (Δ-valid-pre run-Δ sub-Δ Δ₂⋆)
                (Γ-valid-pre (run-combine sub-Δ run-Δ) sub-Γ Γ₂⋆)
    τ-valid-pre {v₁ = tuple τs⁻} run-Δ
      (subst-tuple sub-τs⁻) (valid-tuple τs⁻₂⋆) =
        valid-tuple (τs⁻-valid-pre run-Δ sub-τs⁻ τs⁻₂⋆)

    τ⁻-valid-pre : valid-preᵗ InitType
    τ⁻-valid-pre run-Δ (subst-τ⁻ sub-τ) (valid-τ⁻ τ⋆) =
      valid-τ⁻ (τ-valid-pre run-Δ sub-τ τ⋆)

    τs⁻-valid-pre : valid-preᵗ (List InitType)
    τs⁻-valid-pre run-Δ [] [] = []
    τs⁻-valid-pre run-Δ (sub-τ⁻ ∷ sub-τs⁻) (τ⁻⋆ ∷ τs⁻⋆) =
      τ⁻-valid-pre run-Δ sub-τ⁻ τ⁻⋆ ∷ τs⁻-valid-pre run-Δ sub-τs⁻ τs⁻⋆

    σ-valid-pre : valid-preᵗ StackType
    σ-valid-pre {cᵥ = inst i} {ι₂} {ρ⁼ ι₁} run-Δ
      (subst-ρ-¬inst (subst-< ι₁<ι₂)) (valid-ρ⁼ l)
      with run-split run-Δ
    ... | Δ₁ , Δ₁' , Δ₂ , Δ₂' , sub-Δ₁ , run-Δ₂ , eq₁ , eq₂ , eq₃
      rewrite eq₁ | eq₂ | eq₃
      with ↓-remove-right {xs₁ = Δ₁'} Δ₂'
             (subst (λ len → ι₁ < len) (subst-length sub-Δ₁) ι₁<ι₂) l
    ... | l' with subst-↓-pre l' sub-Δ₁
    ... | ρ , l'' , subst-ρ = valid-ρ⁼ (↓-add-right Δ₂ l'')
    σ-valid-pre {cᵥ = inst i} {ι₂} {ρ⁼ (suc ι₁)} run-Δ
                (subst-ρ-¬inst (subst-inst-> (s≤s ι₁≥ι₂))) (valid-ρ⁼ l)
      with run-split run-Δ
    ... | Δ₁ , Δ₁' , a ∷ .Δ₂' , Δ₂' , sub-Δ₁ , run-inst m , eq₁ , eq₂ , eq₃
      rewrite eq₁ | eq₂ | eq₃
      with ↓-remove-left Δ₁'
             (subst (λ len → ι₁ ≥ len) (subst-length sub-Δ₁) ι₁≥ι₂) l
    ... | l' with ↓-add-left Δ₁ (there {x = a} l')
    ... | l'' with
      begin
        length Δ₁ + suc (ι₁ ∸ length Δ₁')
      ⟨ subst-length sub-Δ₁ ∥ (λ v → length Δ₁ + suc (ι₁ ∸ v)) ⟩≡
        length Δ₁ + suc (ι₁ ∸ length Δ₁)
      ≡⟨ +-comm (length Δ₁) _ ⟩
        suc (ι₁ ∸ length Δ₁) + length Δ₁
      ≡⟨ refl ⟩
        suc (ι₁ ∸ length Δ₁ + length Δ₁)
      ≡⟨ +-comm _ (length Δ₁) ∥ (λ v → suc v) ⟩
        suc (length Δ₁ + (ι₁ ∸ length Δ₁))
      ≡⟨ NP.m+n∸m≡n ι₁≥ι₂ ∥ (λ v → suc v) ⟩
        suc ι₁
      ∎ where open Eq-Reasoning
    ... | eq rewrite eq = valid-ρ⁼ l''
    σ-valid-pre {cᵥ = inst (ρ σ)} {ι} {ρ⁼ .ι} run-Δ
      (subst-ρ-inst sub-σ) σ₂⋆ = valid-ρ⁼ (run-ρ⇒↓ run-Δ)
    σ-valid-pre {cᵥ = weaken Δ⁺} {ι₂} {ρ⁼ ι₁} run-Δ
      (subst-ρ-¬inst (subst-< ι₁<ι₂)) (valid-ρ⁼ l)
      with run-split run-Δ
    ... | Δ₁ , Δ₁' , Δ₂ , Δ₂' , sub-Δ₁ , run-Δ₂ , eq₁ , eq₂ , eq₃
      rewrite eq₁ | eq₂ | eq₃
      with ↓-remove-right {xs₁ = Δ₁'} Δ₂'
             (subst (λ len → ι₁ < len) (subst-length sub-Δ₁) ι₁<ι₂) l
    ... | l' with subst-↓-pre l' sub-Δ₁
    ... | ρ , l'' , subst-ρ = valid-ρ⁼ (↓-add-right Δ₂ l'')
    σ-valid-pre {cᵥ = weaken Δ⁺} {ι₂} {ρ⁼ ι₁} run-Δ
      (subst-ρ-¬inst (subst-weaken-≥ ι₁≥ι₂)) (valid-ρ⁼ l)
      with run-split run-Δ
    ... | Δ₁ , Δ₁' , Δ₂ , .(Δ⁺ ++ Δ₂) , sub-Δ₁ , run-weaken , eq₁ , eq₂ , eq₃
      rewrite eq₁ | eq₂ | eq₃ | subst-length sub-Δ₁
      with ↓-remove-left Δ₁' (Nat-≤-trans ι₁≥ι₂ (NP.n≤m+n (length Δ⁺) ι₁)) l
    ... | l'
      rewrite NP.+-∸-assoc (length Δ⁺) ι₁≥ι₂
      with ↓-remove-left Δ⁺ (NP.m≤m+n (length Δ⁺) _) l'
    ... | l'' with ↓-add-left Δ₁ l''
    ... | l''' with
      begin
        length Δ₁ + (length Δ⁺ + (ι₁ ∸ length Δ₁') ∸ length Δ⁺)
      ≡⟨ +-comm (length Δ⁺) _ ∥ (λ v → length Δ₁ + (v ∸ length Δ⁺)) ⟩
        length Δ₁ + (ι₁ ∸ length Δ₁' + length Δ⁺ ∸ length Δ⁺)
      ≡⟨ NP.m+n∸n≡m (ι₁ ∸ length Δ₁') (length Δ⁺) ∥ (λ v → length Δ₁ + v) ⟩
        length Δ₁ + (ι₁ ∸ length Δ₁')
      ≡⟨ subst-length sub-Δ₁ ∥ (λ v → v + (ι₁ ∸ length Δ₁')) ⟩
        length Δ₁' + (ι₁ ∸ length Δ₁')
      ≡⟨ NP.m+n∸m≡n ι₁≥ι₂ ⟩
        ι₁
      ∎ where open Eq-Reasoning
    ... | eq rewrite eq = valid-ρ⁼ l'''
    σ-valid-pre {v₁ = []} run-Δ subst-[] valid-[] = valid-[]
    σ-valid-pre {v₁ = x ∷ v} run-Δ (sub-τ ∷ sub-σ) (τ₂⋆ ∷ σ₂⋆) =
      τ-valid-pre run-Δ sub-τ τ₂⋆ ∷ σ-valid-pre run-Δ sub-σ σ₂⋆

    Γ-valid-pre : valid-preᵗ RegisterAssignment
    Γ-valid-pre run-Δ (subst-registerₐ sub-sp sub-regs)
      (valid-registerₐ sp₂⋆ regs₂⋆) =
        valid-registerₐ (σ-valid-pre run-Δ sub-sp sp₂⋆)
                        (regs-valid-pre run-Δ sub-regs regs₂⋆)

    regs-valid-pre : ∀ {m} → valid-preᵗ (Vec Type m)
    regs-valid-pre run-Δ [] [] = []
    regs-valid-pre run-Δ (sub-τ ∷ sub-τs) (τ₂⋆ ∷ τs₂⋆) =
      τ-valid-pre run-Δ sub-τ τ₂⋆ ∷ regs-valid-pre run-Δ sub-τs τs₂⋆

    Δ-valid-pre : valid-preᵗ TypeAssignment
    Δ-valid-pre {v₁ = []} run-Δ [] [] = []
    Δ-valid-pre {v₁ = a ∷ Δ} run-Δ (sub-a ∷ sub-Δ) (a₂⋆ ∷ Δ₂⋆) =
      a-valid-pre (run-combine sub-Δ run-Δ) sub-a a₂⋆ ∷
      Δ-valid-pre run-Δ sub-Δ Δ₂⋆

    a-valid-pre : valid-preᵗ TypeAssignmentValue
    a-valid-pre run-Δ subst-α valid-α = valid-α
    a-valid-pre run-Δ subst-ρ valid-ρ = valid-ρ

  mutual
    outside-ctxᵗ : ∀ A {{_ : Substitution A}}
                       {{_ : TypeLike A}} → Set
    outside-ctxᵗ A = ∀ {Δ cᵥ ι} {v : A} →
                       Δ ⊢ v Valid →
                       v ⟦ cᵥ / length Δ + ι ⟧≡ v

    τ-outside-ctx : outside-ctxᵗ Type
    τ-outside-ctx {Δ} {ι = ι} (valid-α⁼ l) = subst-α-¬inst (subst-< (Nat-≤-trans (↓-to-< l) (NP.m≤m+n (length Δ) ι)))
    τ-outside-ctx valid-int = subst-int
    τ-outside-ctx valid-ns = subst-ns
    τ-outside-ctx {Δ} {ι = ι} (valid-∀ {Δ'} Δ⋆ Γ⋆)
      with Γ-outside-ctx {ι = ι} Γ⋆
    ... | sub-Γ
      rewrite List-length-++ Δ' {Δ}
            | +-assoc (length Δ') (length Δ) ι
      = subst-∀ (Δ-outside-ctx Δ⋆) sub-Γ
    τ-outside-ctx (valid-tuple τs⁻⋆) = subst-tuple (τs⁻-outside-ctx τs⁻⋆)

    τ⁻-outside-ctx : outside-ctxᵗ InitType
    τ⁻-outside-ctx (valid-τ⁻ τ⋆) = subst-τ⁻ (τ-outside-ctx τ⋆)

    τs⁻-outside-ctx : outside-ctxᵗ (List InitType)
    τs⁻-outside-ctx [] = []
    τs⁻-outside-ctx (τ⁻⋆ ∷ τs⁻⋆) = τ⁻-outside-ctx τ⁻⋆ ∷ τs⁻-outside-ctx τs⁻⋆

    σ-outside-ctx : outside-ctxᵗ StackType
    σ-outside-ctx {Δ} {ι = ι} (valid-ρ⁼ l) = subst-ρ-¬inst (subst-< (Nat-≤-trans (↓-to-< l) (NP.m≤m+n (length Δ) ι)))
    σ-outside-ctx valid-[] = subst-[]
    σ-outside-ctx (τ⋆ ∷ σ⋆) = τ-outside-ctx τ⋆ ∷ σ-outside-ctx σ⋆

    Γ-outside-ctx : outside-ctxᵗ RegisterAssignment
    Γ-outside-ctx (valid-registerₐ sp⋆ regs⋆) =
      subst-registerₐ (σ-outside-ctx sp⋆) (regs-outside-ctx regs⋆)

    regs-outside-ctx : ∀ {m} → outside-ctxᵗ (Vec Type m)
    regs-outside-ctx [] = []
    regs-outside-ctx (τ⋆ ∷ τs⋆) = τ-outside-ctx τ⋆ ∷ regs-outside-ctx τs⋆

    Δ-outside-ctx : outside-ctxᵗ TypeAssignment
    Δ-outside-ctx [] = []
    Δ-outside-ctx {Δ} {ι = ι} {a ∷ Δ'} (a⋆ ∷ Δ⋆)
      with a-outside-ctx {ι = ι} a⋆
    ... | sub-a
      rewrite List-length-++ Δ' {Δ}
            | +-assoc (length Δ') (length Δ) ι
      = sub-a ∷ Δ-outside-ctx Δ⋆

    a-outside-ctx : outside-ctxᵗ TypeAssignmentValue
    a-outside-ctx valid-α = subst-α
    a-outside-ctx valid-ρ = subst-ρ

Vec-TypeSubstitution :
  ∀ A {S S⁺ T} {{TS : TypeSubstitution A {S} {{S⁺}} {{T}}}} m →
    TypeSubstitution (Vec A m) {{Vec-Substitution⁺ A m}} {{Vec-TypeLike A m}}
Vec-TypeSubstitution A {S} {S⁺} {T} m =
    typeSubstitution xs-valid-inst xs-valid-weaken xs-valid-pre xs-outside-ctx
  where xs-valid-inst : ∀ {m Δ₁ Δ₁' Δ₂ a i} →
                          a ∷ Δ₂ ⊢ i Valid →
                          Δ₁ ⟦ inst i / zero ⟧≡ Δ₁' →
                          {v : Vec A m} →
                          _⊢_Valid {{Vec-TypeLike A m}} (Δ₁ ++ a ∷ Δ₂) v →
                          ∃ λ v' →
                            _⟦_⟧≡_ {{Vec-Substitution A m}}
                              v (inst i / length Δ₁) v' ×
                            _⊢_Valid {{Vec-TypeLike A m}} (Δ₁' ++ Δ₂) v'
        xs-valid-inst i⋆ sub-Δ [] = [] , [] , []
        xs-valid-inst i⋆ sub-Δ (x⋆ ∷ xs⋆)
          with subst-valid-inst i⋆ sub-Δ x⋆ | xs-valid-inst i⋆ sub-Δ xs⋆
        ... | x' , sub-x , x'⋆ | xs' , sub-xs , xs'⋆ =
          x' ∷ xs' , sub-x ∷ sub-xs , x'⋆ ∷ xs'⋆

        xs-valid-weaken :
          ∀ {m} Δ⁺ {Δ₁ Δ₁' Δ₂} →
            Δ₁ ⟦ weaken (length Δ⁺) / zero ⟧≡ Δ₁' →
            {xs : Vec A m} →
            _⊢_Valid {{Vec-TypeLike A m}} (Δ₁ ++ Δ₂) xs →
            ∃ λ xs' →
              _⟦_⟧≡_ {{Vec-Substitution A m}}
                xs (weaken (length Δ⁺) / length Δ₁) xs' ×
              _⊢_Valid {{Vec-TypeLike A m}} (Δ₁' ++ Δ⁺ ++ Δ₂) xs'
        xs-valid-weaken Δ⁺ sub-Δ [] = [] , [] , []
        xs-valid-weaken Δ⁺ sub-Δ (x⋆ ∷ xs⋆)
          with subst-valid-weaken Δ⁺ sub-Δ x⋆ | xs-valid-weaken Δ⁺ sub-Δ xs⋆
        ... | x' , sub-x , x'⋆ | xs' , sub-xs , xs'⋆ =
          x' ∷ xs' , sub-x ∷ sub-xs , x'⋆ ∷ xs'⋆

        xs-valid-pre :
          ∀ {m Δ₁ Δ₂ cᵥ ι} {xs₁ xs₂ : Vec A m} →
            Run Δ₁ ⟦ cᵥ / ι ⟧≡ Δ₂ →
            _⟦_⟧≡_ {{Vec-Substitution A m}} xs₁ (Strong→Weak cᵥ / ι) xs₂ →
            _⊢_Valid {{Vec-TypeLike A m}} Δ₂ xs₂ →
            _⊢_Valid {{Vec-TypeLike A m}} Δ₁ xs₁
        xs-valid-pre run-Δ [] [] = []
        xs-valid-pre run-Δ (sub-x ∷ sub-xs) (x₂⋆ ∷ xs₂⋆) =
          subst-valid-pre run-Δ sub-x x₂⋆ ∷ xs-valid-pre run-Δ sub-xs xs₂⋆

        xs-outside-ctx :
          ∀ {Δ m cᵥ ι} {xs : Vec A m} →
            _⊢_Valid {{Vec-TypeLike A m}} Δ xs →
            _⟦_⟧≡_ {{Vec-Substitution A m}} xs (cᵥ / length Δ + ι) xs
        xs-outside-ctx [] = []
        xs-outside-ctx (x⋆ ∷ xs⋆) = subst-outside-ctx x⋆ ∷ xs-outside-ctx xs⋆

List-TypeSubstitution :
  ∀ A {S S⁺ T} {{TS : TypeSubstitution A {S} {{S⁺}} {{T}}}} →
    TypeSubstitution (List A) {{List-Substitution⁺ A}} {{List-TypeLike A}}
List-TypeSubstitution A {S} {S⁺} {T} =
    typeSubstitution xs-valid-inst xs-valid-weaken xs-valid-pre xs-outside-ctx
  where xs-valid-inst : ∀ {Δ₁ Δ₁' Δ₂ a i} →
                          a ∷ Δ₂ ⊢ i Valid →
                          Δ₁ ⟦ inst i / zero ⟧≡ Δ₁' →
                          {v : List A} →
                          _⊢_Valid {{List-TypeLike A}} (Δ₁ ++ a ∷ Δ₂) v →
                          ∃ λ v' →
                            _⟦_⟧≡_ {{List-Substitution A}}
                              v (inst i / length Δ₁) v' ×
                            _⊢_Valid {{List-TypeLike A}} (Δ₁' ++ Δ₂) v'
        xs-valid-inst i⋆ sub-Δ [] = [] , [] , []
        xs-valid-inst i⋆ sub-Δ (x⋆ ∷ xs⋆)
          with subst-valid-inst i⋆ sub-Δ x⋆ | xs-valid-inst i⋆ sub-Δ xs⋆
        ... | x' , sub-x , x'⋆ | xs' , sub-xs , xs'⋆ =
          x' ∷ xs' , sub-x ∷ sub-xs , x'⋆ ∷ xs'⋆

        xs-valid-weaken :
          ∀ Δ⁺ {Δ₁ Δ₁' Δ₂} →
            Δ₁ ⟦ weaken (length Δ⁺) / zero ⟧≡ Δ₁' →
            {xs : List A} →
            _⊢_Valid {{List-TypeLike A}} (Δ₁ ++ Δ₂) xs →
            ∃ λ xs' →
              _⟦_⟧≡_ {{List-Substitution A}}
                xs (weaken (length Δ⁺) / length Δ₁) xs' ×
              _⊢_Valid {{List-TypeLike A}} (Δ₁' ++ Δ⁺ ++ Δ₂) xs'
        xs-valid-weaken Δ⁺ sub-Δ [] = [] , [] , []
        xs-valid-weaken Δ⁺ sub-Δ (x⋆ ∷ xs⋆)
          with subst-valid-weaken Δ⁺ sub-Δ x⋆ | xs-valid-weaken Δ⁺ sub-Δ xs⋆
        ... | x' , sub-x , x'⋆ | xs' , sub-xs , xs'⋆ =
          x' ∷ xs' , sub-x ∷ sub-xs , x'⋆ ∷ xs'⋆

        xs-valid-pre :
          ∀ {Δ₁ Δ₂ cᵥ ι} {xs₁ xs₂ : List A} →
            Run Δ₁ ⟦ cᵥ / ι ⟧≡ Δ₂ →
            _⟦_⟧≡_ {{List-Substitution A}} xs₁ (Strong→Weak cᵥ / ι) xs₂ →
            _⊢_Valid {{List-TypeLike A}} Δ₂ xs₂ →
            _⊢_Valid {{List-TypeLike A}} Δ₁ xs₁
        xs-valid-pre run-Δ [] [] = []
        xs-valid-pre run-Δ (sub-x ∷ sub-xs) (x₂⋆ ∷ xs₂⋆) =
          subst-valid-pre run-Δ sub-x x₂⋆ ∷ xs-valid-pre run-Δ sub-xs xs₂⋆

        xs-outside-ctx :
          ∀ {Δ cᵥ ι} {xs : List A} →
            _⊢_Valid {{List-TypeLike A}} Δ xs →
            _⟦_⟧≡_ {{List-Substitution A}} xs (cᵥ / length Δ + ι) xs
        xs-outside-ctx [] = []
        xs-outside-ctx (x⋆ ∷ xs⋆) = subst-outside-ctx x⋆ ∷ xs-outside-ctx xs⋆

instance
  Type-TypeSubstitution : TypeSubstitution Type
  Type-TypeSubstitution =
    typeSubstitution τ-valid-inst τ-valid-weaken τ-valid-pre τ-outside-ctx

  TypeVec-TypeSubstitution : ∀ {m} → TypeSubstitution (Vec Type m)
  TypeVec-TypeSubstitution = Vec-TypeSubstitution Type _

  TypeList-TypeSubstitution : TypeSubstitution (List Type)
  TypeList-TypeSubstitution = List-TypeSubstitution Type

  InitType-TypeSubstitution : TypeSubstitution InitType
  InitType-TypeSubstitution = typeSubstitution
    τ⁻-valid-inst τ⁻-valid-weaken τ⁻-valid-pre τ⁻-outside-ctx

  InitTypeVec-TypeSubstitution : ∀ {m} → TypeSubstitution (Vec InitType m)
  InitTypeVec-TypeSubstitution = Vec-TypeSubstitution InitType _

  InitTypeList-TypeSubstitution : TypeSubstitution (List InitType)
  InitTypeList-TypeSubstitution = List-TypeSubstitution InitType

  StackType-TypeSubstitution : TypeSubstitution StackType
  StackType-TypeSubstitution = typeSubstitution
    σ-valid-inst σ-valid-weaken σ-valid-pre σ-outside-ctx

  TypeAssignment-TypeSubstitution : TypeSubstitution TypeAssignment
  TypeAssignment-TypeSubstitution = typeSubstitution
    Δ-valid-inst Δ-valid-weaken Δ-valid-pre Δ-outside-ctx

  TypeAssignmentValue-TypeSubstitution : TypeSubstitution TypeAssignmentValue
  TypeAssignmentValue-TypeSubstitution = typeSubstitution
    a-valid-inst a-valid-weaken a-valid-pre a-outside-ctx

  RegisterAssignment-TypeSubstitution : TypeSubstitution RegisterAssignment
  RegisterAssignment-TypeSubstitution = typeSubstitution
    Γ-valid-inst Γ-valid-weaken Γ-valid-pre Γ-outside-ctx
