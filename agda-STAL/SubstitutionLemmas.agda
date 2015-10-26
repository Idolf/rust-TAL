module SubstitutionLemmas where

open import Substitution
open import Grammar
open import TypeJudgments
open import Util
import Data.Nat as N
import Data.Nat.Properties as NP
import Data.List as L
import Algebra as A
open A.CommutativeSemiring NP.commutativeSemiring using (+-comm ; +-assoc)
open NP.SemiringSolver
  using (prove; solve; _:=_; con; var; _:+_; _:*_; :-_; _:-_)


ι-subst : ∀ {A} {{_ : Substitution A ℕ}}
            {x x' : A} {cᵥ : WeakCastValue} {ι₁ ι₂} →
            ι₁ ≡ ι₂ →
            x ⟦ cᵥ / ι₁ ⟧≡ x' →
            x ⟦ cᵥ / ι₂ ⟧≡ x'
ι-subst {x = x} {x'} {cᵥ} eq sub-x = subst (λ ι → x ⟦ cᵥ / ι ⟧≡ x') eq sub-x

run-combine : ∀ {Δ₁ Δ₁' Δ₂ Δ₂' cᵥ} →
                Δ₁ ⟦ Strong→WeakCastValue cᵥ / 0 ⟧≡ Δ₁' →
                Run Δ₂ ⟦ cᵥ / 0 ⟧≡ Δ₂' →
                Run Δ₁ ++ Δ₂ ⟦ cᵥ / length Δ₁ ⟧≡ Δ₁' ++ Δ₂'
run-combine {[]} [] run-Δ₂ = run-Δ₂
run-combine {a ∷ Δ₁} (sub-a ∷ sub-Δ₁) run-Δ₂ =
  run-suc (ι-subst (+-comm (length Δ₁) 0) sub-a) (run-combine sub-Δ₁ run-Δ₂)

run-split : ∀ {Δ Δ' cᵥ ι} →
              Run Δ ⟦ cᵥ / ι ⟧≡ Δ' →
              ∃₂ λ Δ₁ Δ₁' → ∃₂ λ Δ₂ Δ₂' →
                Δ₁ ⟦ cᵥ / zero ⟧≡ Δ₁' ×
                Run Δ₂ ⟦ cᵥ / zero ⟧≡ Δ₂' ×
                Δ  ≡ Δ₁  ++ Δ₂ ×
                Δ' ≡ Δ₁' ++ Δ₂' ×
                ι ≡ length Δ₁
run-split {a ∷ Δ} .{Δ} run-inst =
  [] , [] , a ∷ Δ , Δ , [] , run-inst , refl , refl , refl
run-split {Δ} .{Δ⁺ ++ Δ} (run-weaken {Δ⁺ = Δ⁺}) =
  [] , [] , Δ , Δ⁺ ++ Δ , [] , run-weaken , refl , refl , refl
run-split {a ∷ Δ} {a' ∷ Δ'} (run-suc sub-a run-Δ) with run-split run-Δ
... | Δ₁ , Δ₁' , Δ₂ , Δ₂' , sub-Δ₁ , run-Δ₂ , eq₁ , eq₂ , eq₃ =
  a ∷ Δ₁ , a' ∷ Δ₁' , Δ₂ , Δ₂' ,
  (ι-subst (trans eq₃ (+-comm 0 (length Δ₁))) sub-a) ∷ sub-Δ₁ ,
  run-Δ₂ ,
  cong (_∷_ a) eq₁ ,
  cong (_∷_ a') eq₂ ,
  cong suc eq₃

subst-↓ : ∀ {Δ Δ' : TypeAssignment} {ι₁ ι₂ a} {cᵥ : WeakCastValue} →
            Δ ↓ ι₁ ⇒ a →
            Δ ⟦ cᵥ / ι₂ ⟧≡ Δ' →
            ∃ λ a' →
              Δ' ↓ ι₁ ⇒ a' ×
              a ⟦ cᵥ / (length Δ ∸ suc ι₁) + ι₂ ⟧≡ a'
subst-↓ here (sub-a ∷ sub-Δ) = _ , here , sub-a
subst-↓ (there l) (sub-a ∷ sub-Δ) with subst-↓ l sub-Δ
... | a' , l' , sub-a' = a' , there l' , sub-a'

subst-length : ∀ {Δ Δ' : TypeAssignment} {c : WeakCast} →
                  Δ ⟦ c ⟧≡ Δ' →
                  length Δ ≡ length Δ'
subst-length [] = refl
subst-length (sub-a ∷ sub-Δ) = cong suc (subst-length sub-Δ)

subst-combine : ∀ {Δ₁ Δ₁' Δ₂ Δ₂' : TypeAssignment} {cᵥ : WeakCastValue} →
                  Δ₁ ⟦ cᵥ / length Δ₂ ⟧≡ Δ₁' →
                  Δ₂ ⟦ cᵥ / zero ⟧≡ Δ₂' →
                  Δ₁ ++ Δ₂ ⟦ cᵥ / zero ⟧≡ Δ₁' ++ Δ₂'
subst-combine [] sub-Δ₂ = sub-Δ₂
subst-combine {a ∷ Δ₁} {a' ∷ Δ₁'} {Δ₂} (sub-a ∷ sub-Δ₁) sub-Δ₂
  = (ι-subst (trans (sym (List-length-++ Δ₁))
                         (+-comm 0 (length (Δ₁ ++ Δ₂)))) sub-a)
    ∷ subst-combine sub-Δ₁ sub-Δ₂

subst-↓-replace : ∀ {Δ₁ Δ₁' Δ₂ : TypeAssignment} {ι a} {c : WeakCast} →
                    Δ₁ ⟦ c ⟧≡ Δ₁' →
                    ι ≥ length Δ₁ →
                    Δ₁  ++ Δ₂ ↓ ι ⇒ a →
                    Δ₁' ++ Δ₂ ↓ ι ⇒ a
subst-↓-replace {Δ₁} {Δ₁'} sub-Δ ι≥len l =
  ↓-replace-left Δ₁ Δ₁' (subst-length sub-Δ) ι≥len l

valid-i-split : ∀ Δ₁ {Δ₂} {cᵥ : WeakCastValue} →
                  Δ₁ ++ Δ₂ ⊢ cᵥ / length Δ₁ Valid →
                  Δ₂ ⊢ cᵥ Valid
valid-i-split [] (valid-zero cᵥ⋆) = cᵥ⋆
valid-i-split (a ∷ Δ₁) (valid-suc c⋆) = valid-i-split Δ₁ c⋆

private
  mutual
    τ-valid-++ : ∀ {Δ Δ'} {τ : Type} →
                   Δ ⊢ τ Valid →
                   Δ ++ Δ' ⊢ τ Valid
    τ-valid-++ (valid-α⁼ l) = valid-α⁼ (↓-add-right _ l)
    τ-valid-++ valid-int = valid-int
    τ-valid-++ valid-ns = valid-ns
    τ-valid-++ {Δ = Δ} {Δ'} (valid-∀ {Δᵥ} {Γ} Δ⋆ Γ⋆) =
      valid-∀ (Δ-valid-++ Δ⋆)
              (subst (λ Δ → Δ ⊢ Γ RegisterAssignment)
              (List-++-assoc Δᵥ Δ Δ') (Γ-valid-++ Γ⋆))
    τ-valid-++ (valid-tuple τs⋆) = valid-tuple (τs⁻-valid-++ τs⋆)

    τ⁻-valid-++ : ∀ {Δ Δ'} {τ⁻ : InitType} →
                    Δ ⊢ τ⁻ Valid →
                    Δ ++ Δ' ⊢ τ⁻ Valid
    τ⁻-valid-++ (valid-τ⁻ τ⋆) = valid-τ⁻ (τ-valid-++ τ⋆)

    τs⁻-valid-++ : ∀ {Δ Δ'} {τs⁻ : List InitType} →
                     Δ ⊢ τs⁻ Valid →
                     Δ ++ Δ' ⊢ τs⁻ Valid
    τs⁻-valid-++ [] = []
    τs⁻-valid-++ (τ⁻⋆ ∷ τs⁻⋆) = τ⁻-valid-++ τ⁻⋆ ∷ τs⁻-valid-++ τs⁻⋆

    σ-valid-++ : ∀ {Δ Δ'} {σ : StackType} →
                     Δ ⊢ σ Valid →
                     Δ ++ Δ' ⊢ σ Valid
    σ-valid-++ (valid-ρ⁼ l) = valid-ρ⁼ (↓-add-right _ l)
    σ-valid-++ valid-nil = valid-nil
    σ-valid-++ (τ⋆ ∷ σ⋆) = τ-valid-++ τ⋆ ∷ σ-valid-++ σ⋆

    Δ-valid-++ : ∀ {Δ Δ'} {Δᵥ : TypeAssignment} →
                   Δ ⊢ Δᵥ Valid →
                   Δ ++ Δ' ⊢ Δᵥ Valid
    Δ-valid-++ [] = []
    Δ-valid-++ {Δ} {Δ'} {a ∷ Δᵥ} (a⋆ ∷ Δᵥ⋆) =
      subst (λ Δ → Δ ⊢ a TypeAssignmentValue)
            (List-++-assoc Δᵥ Δ Δ') (a-valid-++ a⋆)
      ∷ Δ-valid-++ Δᵥ⋆

    a-valid-++ : ∀ {Δ Δ'} {a : TypeAssignmentValue} →
                   Δ ⊢ a Valid →
                   Δ ++ Δ' ⊢ a Valid
    a-valid-++ valid-α = valid-α
    a-valid-++ valid-ρ = valid-ρ

    Γ-valid-++ : ∀ {Δ Δ'} {Γ : RegisterAssignment} →
                   Δ ⊢ Γ Valid →
                   Δ ++ Δ' ⊢ Γ Valid
    Γ-valid-++ (valid-registerₐ sp⋆ regs⋆) =
      valid-registerₐ (σ-valid-++ sp⋆) (regs-valid-++ regs⋆)

    regs-valid-++ : ∀ {Δ Δ'} {m} {τs : Vec Type m} →
                      Δ ⊢ τs Valid →
                      Δ ++ Δ' ⊢ τs Valid
    regs-valid-++ [] = []
    regs-valid-++ (τ⋆ ∷ τs⋆) = τ-valid-++ τ⋆ ∷ regs-valid-++ τs⋆

  mutual
    valid-weakenᵗ : ∀ A {{_ : Substitution A ℕ}}
                      {{_ : TypeLike A TypeAssignment}} → Set
    valid-weakenᵗ T = ∀ Δ⁺ {Δ₁ Δ₁' Δ₂} →
                        Δ₁ ⟦ weaken Δ⁺ / zero ⟧≡ Δ₁' →
                        {v : T} →
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
    σ-valid-weaken Δ⁺ sub-Δ valid-nil = nil , subst-nil , valid-nil
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
    valid-instᵗ : ∀ A {{_ : Substitution A ℕ}}
                    {{_ : TypeLike A TypeAssignment}} → Set
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
    σ-valid-inst i⋆ sub-Δ valid-nil = nil , subst-nil , valid-nil
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

can-run : ∀ {Δ} → [] ⊢ Δ Valid →
          ∀ {c} → Δ  ⊢ c Valid →
            ∃ λ Δ' →
              Run Δ ⟦ c ⟧≡ Δ'
can-run [] {inst i / zero} (valid-zero (valid-inst ()))
can-run {a ∷ Δ} (a⋆ ∷ Δ⋆) {inst i / zero} (valid-zero (valid-inst i⋆)) =
  Δ , run-inst
can-run {Δ} Δ⋆ {weaken Δ⁺ / zero} (valid-zero valid-weaken) =
  Δ⁺ ++ Δ , run-weaken
can-run [] {cᵥ / suc ι} ()
can-run {a₁ ∷ Δ} (a₁⋆ ∷ Δ⋆) {inst i / suc ι} (valid-suc c⋆)
  with can-run Δ⋆ c⋆
... | Δ' , run-Δ with run-split run-Δ
... | Δ₁ , Δ₁' , (a₂ ∷ Δ₂) , .Δ₂ , sub-Δ₁ , run-inst , eq₁ , eq₂ , eq₃
  rewrite eq₁ | eq₂ | eq₃ with valid-i-split Δ₁ c⋆
... | valid-inst i⋆ with a-valid-inst i⋆ sub-Δ₁
                           (subst₂ _⊢_Valid
                                   (List-++-right-identity (Δ₁ ++ a₂ ∷ Δ₂))
                                   refl
                                   a₁⋆)
... | a₁' , sub-a₁ , a₁'⋆ =
      a₁' ∷ Δ₁' ++ Δ₂ ,
      run-combine (ι-subst (+-comm 0 (length Δ₁)) sub-a₁ ∷ sub-Δ₁)
                  (run-inst {a₂} {Δ₂} {i})
can-run {a₁ ∷ Δ} (a⋆ ∷ Δ⋆) {weaken Δ⁺ / suc ι} (valid-suc c⋆)
  with can-run Δ⋆ {weaken Δ⁺ / ι} c⋆
... | Δ' , run-Δ with run-split run-Δ
... | Δ₁ , Δ₁' , Δ₂ , .(Δ⁺ ++ Δ₂) , sub-Δ₁ , run-weaken , eq₁ , eq₂ , eq₃
  rewrite eq₁ | eq₂ | eq₃ with a-valid-weaken Δ⁺ sub-Δ₁
                                 (subst₂ _⊢_Valid
                                         (List-++-right-identity (Δ₁ ++ Δ₂))
                                         refl
                                         a⋆)
... | a₁' , sub-a₁ , a₁'⋆ =
      a₁' ∷ Δ₁' ++ Δ⁺ ++ Δ₂ ,
      run-combine (ι-subst (+-comm 0 (length Δ₁)) sub-a₁ ∷ sub-Δ₁)
                  (run-weaken {Δ₂} {Δ⁺})

record Substitution⁺ (A : Set) (_ : Substitution A TypeAssignment)
                               (_ : TypeLike A TypeAssignment) : Set where
  constructor substitution⁺
  field
    subst-valid-++ :
      ∀ {Δ₁ Δ₂} {v : A} →
        Δ₁ ⊢ v Valid →
        Δ₁ ++ Δ₂ ⊢ v Valid
    subst-valid-inst :
      ∀ {Δ₁ Δ₁' Δ₂ a i} →
        a ∷ Δ₂ ⊢ i Valid →
        Δ₁ ⟦ inst {W = ℕ} i / zero ⟧≡ Δ₁' →
        {v : A} →
        Δ₁ ++ a ∷ Δ₂ ⊢ v Valid →
        ∃ λ v' →
          v ⟦ inst {W = TypeAssignment} i / length Δ₁ ⟧≡ v' ×
          Δ₁' ++ Δ₂ ⊢ v' Valid
    subst-valid-weaken :
      ∀ Δ⁺ {Δ₁ Δ₁' Δ₂} →
        Δ₁ ⟦ weaken Δ⁺ / zero ⟧≡ Δ₁' →
        {v : A} →
        Δ₁ ++ Δ₂ ⊢ v Valid →
        ∃ λ v' →
          v ⟦ weaken Δ⁺ / length Δ₁ ⟧≡ v' ×
          Δ₁' ++ Δ⁺ ++ Δ₂ ⊢ v' Valid
  can-subst : ∀ {Δ Δ'} {c : StrongCast} {v : A} →
                Δ ⊢ c Valid →
                Run Δ ⟦ c ⟧≡ Δ' →
                Δ ⊢ v Valid →
                ∃ λ v' →
                  v ⟦ c ⟧≡ v' ×
                  Δ' ⊢ v' Valid
  can-subst {c = inst i / ι} c⋆ run-Δ v⋆ with run-split run-Δ
  ... | Δ₁ , Δ₁' , (a ∷ Δ₂) , .Δ₂ , sub-Δ₁ , run-inst , eq₁ , eq₂ , eq₃
    rewrite eq₁ | eq₂ | eq₃ with valid-i-split Δ₁ c⋆
  ... | valid-inst i⋆ = subst-valid-inst i⋆ sub-Δ₁ v⋆
  can-subst {c = weaken Δ⁺ / ι} c⋆ run-Δ v⋆ with run-split run-Δ
  ... | Δ₁ , Δ₁' , Δ₂ , .(Δ⁺ ++ Δ₂) , sub-Δ₁ , run-weaken , eq₁ , eq₂ , eq₃
    rewrite eq₁ | eq₂ | eq₃ =
      subst-valid-weaken Δ⁺ sub-Δ₁ v⋆

open Substitution⁺ {{...}} public

Vec-Substitution⁺ : ∀ {A S T m} {{_ : Substitution⁺ A S T}} →
                      Substitution⁺ (Vec A m) Vec-Substitution Vec-typeLike
Vec-Substitution⁺ {A} =
    substitution⁺ xs-valid-++  xs-valid-inst xs-valid-weaken
  where xs-valid-++ : ∀ {m Δ₁ Δ₂} {xs : Vec A m} →
                        _⊢_Valid {{Vec-typeLike}} Δ₁ xs →
                        _⊢_Valid {{Vec-typeLike}} (Δ₁ ++ Δ₂) xs
        xs-valid-++ [] = []
        xs-valid-++ (x⋆ ∷ xs⋆) = subst-valid-++ x⋆ ∷ xs-valid-++ xs⋆

        xs-valid-inst : ∀ {m Δ₁ Δ₁' Δ₂ a i} →
                          a ∷ Δ₂ ⊢ i Valid →
                          Δ₁ ⟦ inst {W = ℕ} i / zero ⟧≡ Δ₁' →
                          {v : Vec A m} →
                          _⊢_Valid {{Vec-typeLike}} (Δ₁ ++ a ∷ Δ₂) v →
                          ∃ λ v' →
                            _⟦_⟧≡_ {{Vec-Substitution}}
                              v (inst {W = TypeAssignment} i / length Δ₁) v' ×
                            _⊢_Valid {{Vec-typeLike}} (Δ₁' ++ Δ₂) v'
        xs-valid-inst i⋆ sub-Δ [] = [] , [] , []
        xs-valid-inst i⋆ sub-Δ (x⋆ ∷ xs⋆)
          with subst-valid-inst i⋆ sub-Δ x⋆ | xs-valid-inst i⋆ sub-Δ xs⋆
        ... | x' , sub-x , x'⋆ | xs' , sub-xs , xs'⋆ =
          x' ∷ xs' , sub-x ∷ sub-xs , x'⋆ ∷ xs'⋆

        xs-valid-weaken : ∀ {m} Δ⁺ {Δ₁ Δ₁' Δ₂} →
                            Δ₁ ⟦ weaken Δ⁺ / zero ⟧≡ Δ₁' →
                            {xs : Vec A m} →
                            _⊢_Valid {{Vec-typeLike}} (Δ₁ ++ Δ₂) xs →
                            ∃ λ xs' →
                              _⟦_⟧≡_ {{Vec-Substitution}}
                                xs (weaken Δ⁺ / length Δ₁) xs' ×
                              _⊢_Valid {{Vec-typeLike}} (Δ₁' ++ Δ⁺ ++ Δ₂) xs'
        xs-valid-weaken Δ⁺ sub-Δ [] = [] , [] , []
        xs-valid-weaken Δ⁺ sub-Δ (x⋆ ∷ xs⋆)
          with subst-valid-weaken Δ⁺ sub-Δ x⋆ | xs-valid-weaken Δ⁺ sub-Δ xs⋆
        ... | x' , sub-x , x'⋆ | xs' , sub-xs , xs'⋆ =
          x' ∷ xs' , sub-x ∷ sub-xs , x'⋆ ∷ xs'⋆

List-Substitution⁺ : ∀ {A S T} {{_ : Substitution⁺ A S T}} →
                       Substitution⁺ (List A) List-Substitution List-typeLike
List-Substitution⁺ {A} =
    substitution⁺ xs-valid-++ xs-valid-inst xs-valid-weaken
  where xs-valid-++ : ∀ {Δ₁ Δ₂} {xs : List A} →
                        _⊢_Valid {{List-typeLike}} Δ₁ xs →
                        _⊢_Valid {{List-typeLike}} (Δ₁ ++ Δ₂) xs
        xs-valid-++ [] = []
        xs-valid-++ (x⋆ ∷ xs⋆) = subst-valid-++ x⋆ ∷ xs-valid-++ xs⋆

        xs-valid-inst : ∀ {Δ₁ Δ₁' Δ₂ a i} →
                          a ∷ Δ₂ ⊢ i Valid →
                          Δ₁ ⟦ inst {W = ℕ} i / zero ⟧≡ Δ₁' →
                          {v : List A} →
                          _⊢_Valid {{List-typeLike}} (Δ₁ ++ a ∷ Δ₂) v →
                          ∃ λ v' →
                            _⟦_⟧≡_ {{List-Substitution}}
                              v (inst {W = TypeAssignment} i / length Δ₁) v' ×
                            _⊢_Valid {{List-typeLike}} (Δ₁' ++ Δ₂) v'
        xs-valid-inst i⋆ sub-Δ [] = [] , [] , []
        xs-valid-inst i⋆ sub-Δ (x⋆ ∷ xs⋆)
          with subst-valid-inst i⋆ sub-Δ x⋆ | xs-valid-inst i⋆ sub-Δ xs⋆
        ... | x' , sub-x , x'⋆ | xs' , sub-xs , xs'⋆ =
          x' ∷ xs' , sub-x ∷ sub-xs , x'⋆ ∷ xs'⋆

        xs-valid-weaken : ∀ Δ⁺ {Δ₁ Δ₁' Δ₂} →
                            Δ₁ ⟦ weaken Δ⁺ / zero ⟧≡ Δ₁' →
                            {xs : List A} →
                            _⊢_Valid {{List-typeLike}} (Δ₁ ++ Δ₂) xs →
                            ∃ λ xs' →
                              _⟦_⟧≡_ {{List-Substitution}}
                                xs (weaken Δ⁺ / length Δ₁) xs' ×
                              _⊢_Valid {{List-typeLike}} (Δ₁' ++ Δ⁺ ++ Δ₂) xs'
        xs-valid-weaken Δ⁺ sub-Δ [] = [] , [] , []
        xs-valid-weaken Δ⁺ sub-Δ (x⋆ ∷ xs⋆)
          with subst-valid-weaken Δ⁺ sub-Δ x⋆ | xs-valid-weaken Δ⁺ sub-Δ xs⋆
        ... | x' , sub-x , x'⋆ | xs' , sub-xs , xs'⋆ =
          x' ∷ xs' , sub-x ∷ sub-xs , x'⋆ ∷ xs'⋆

instance
  Type-Substitution⁺ : Substitution⁺ Type Weak→StrongSubstitution
                                          Type-typeLike
  Type-Substitution⁺ = substitution⁺
    τ-valid-++ τ-valid-inst τ-valid-weaken

  TypeVec-Substitution⁺ : ∀ {m} → Substitution⁺ (Vec Type m) Vec-Substitution
                                                             Vec-typeLike
  TypeVec-Substitution⁺ = Vec-Substitution⁺

  TypeList-Substitution⁺ : Substitution⁺ (List Type) List-Substitution
                                                     List-typeLike
  TypeList-Substitution⁺ = List-Substitution⁺

  InitType-Substitution⁺ : Substitution⁺ InitType Weak→StrongSubstitution
                                                  InitType-typeLike
  InitType-Substitution⁺ = substitution⁺
    τ⁻-valid-++ τ⁻-valid-inst τ⁻-valid-weaken

  InitTypeVec-Substitution⁺ : ∀ {m} → Substitution⁺ (Vec InitType m)
                                                    Vec-Substitution
                                                    Vec-typeLike
  InitTypeVec-Substitution⁺ = Vec-Substitution⁺

  InitTypeList-Substitution⁺ : Substitution⁺ (List InitType) List-Substitution
                                                             List-typeLike
  InitTypeList-Substitution⁺ = List-Substitution⁺

  StackType-Substitution⁺ : Substitution⁺ StackType Weak→StrongSubstitution
                                                    StackType-typeLike
  StackType-Substitution⁺ = substitution⁺
    σ-valid-++ σ-valid-inst σ-valid-weaken

  TypeAssignment-Substitution⁺ : Substitution⁺ TypeAssignment
                                               Weak→StrongSubstitution
                                               TypeAssignment-typeLike
  TypeAssignment-Substitution⁺ = substitution⁺
    Δ-valid-++ Δ-valid-inst Δ-valid-weaken

  TypeAssignmentValue-Substitution⁺ : Substitution⁺
                                        TypeAssignmentValue
                                        Weak→StrongSubstitution
                                        TypeAssignmentValue-typeLike
  TypeAssignmentValue-Substitution⁺ = substitution⁺
    a-valid-++ a-valid-inst a-valid-weaken
