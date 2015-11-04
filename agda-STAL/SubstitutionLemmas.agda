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

run-combine : ∀ {Δ₁ Δ₁' Δ₂ Δ₂' cᵥ ι} →
                Δ₁ ⟦ Strong→WeakCastValue cᵥ / ι ⟧≡ Δ₁' →
                Run Δ₂ ⟦ cᵥ / ι ⟧≡ Δ₂' →
                Run Δ₁ ++ Δ₂ ⟦ cᵥ / length Δ₁ + ι ⟧≡ Δ₁' ++ Δ₂'
run-combine {[]} [] run-Δ₂ = run-Δ₂
run-combine {a ∷ Δ₁} (sub-a ∷ sub-Δ₁) run-Δ₂ =
  run-suc sub-a (run-combine sub-Δ₁ run-Δ₂)

run-combine' : ∀ {Δ₁ Δ₁' Δ₂ Δ₂' cᵥ} →
                 Δ₁ ⟦ Strong→WeakCastValue cᵥ / 0 ⟧≡ Δ₁' →
                 Run Δ₂ ⟦ cᵥ / 0 ⟧≡ Δ₂' →
                 Run Δ₁ ++ Δ₂ ⟦ cᵥ / length Δ₁ ⟧≡ Δ₁' ++ Δ₂'
run-combine' {Δ₁} sub-Δ₁ run-Δ₂ with run-combine sub-Δ₁ run-Δ₂
... | run-Δ rewrite +-comm (length Δ₁) 0 = run-Δ

run-split : ∀ {Δ Δ' cᵥ ι} →
              Run Δ ⟦ cᵥ / ι ⟧≡ Δ' →
              ∃₂ λ Δ₁ Δ₁' → ∃₂ λ Δ₂ Δ₂' →
                Δ₁ ⟦ cᵥ / zero ⟧≡ Δ₁' ×
                Run Δ₂ ⟦ cᵥ / zero ⟧≡ Δ₂' ×
                Δ  ≡ Δ₁  ++ Δ₂ ×
                Δ' ≡ Δ₁' ++ Δ₂' ×
                ι ≡ length Δ₁
run-split {a ∷ Δ} .{Δ} (run-inst m) =
  [] , [] , a ∷ Δ , Δ , [] , (run-inst m) , refl , refl , refl
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

run-append : ∀ {Δ₁ Δ₁' Δ₂ c} →
               Run Δ₁ ⟦ c ⟧≡ Δ₁' →
               Run Δ₁ ++ Δ₂ ⟦ c ⟧≡ Δ₁' ++ Δ₂
run-append (run-inst m) = run-inst m
run-append {Δ₁} .{Δ⁺ ++ Δ₁} {Δ₂} (run-weaken {Δ⁺ = Δ⁺})
  rewrite List-++-assoc Δ⁺ Δ₁ Δ₂ = run-weaken {Δ₁ ++ Δ₂} {Δ⁺}
run-append (run-suc sub-a run-Δ) = run-suc sub-a (run-append run-Δ)

subst-↓ : ∀ {Δ Δ' : TypeAssignment} {ι₁ ι₂ a} {cᵥ : WeakCastValue} →
            Δ ↓ ι₁ ⇒ a →
            Δ ⟦ cᵥ / ι₂ ⟧≡ Δ' →
            ∃ λ a' →
              Δ' ↓ ι₁ ⇒ a' ×
              a ⟦ cᵥ / (length Δ ∸ suc ι₁) + ι₂ ⟧≡ a'
subst-↓ here (sub-a ∷ sub-Δ) = _ , here , sub-a
subst-↓ (there l) (sub-a ∷ sub-Δ) with subst-↓ l sub-Δ
... | a' , l' , sub-a' = a' , there l' , sub-a'

subst-↓-pre : ∀ {Δ Δ' : TypeAssignment} {ι₁ ι₂ a'} {cᵥ : WeakCastValue} →
                Δ' ↓ ι₁ ⇒ a' →
                Δ ⟦ cᵥ / ι₂ ⟧≡ Δ' →
                ∃ λ a →
                  Δ ↓ ι₁ ⇒ a ×
                  a ⟦ cᵥ / (length Δ ∸ suc ι₁) + ι₂ ⟧≡ a'
subst-↓-pre here (sub-a ∷ sub-Δ) = _ , here , sub-a
subst-↓-pre (there l) (sub-a ∷ sub-Δ) with subst-↓-pre l sub-Δ
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

valid-i-split : ∀ Δ₁ {Δ₂} {cᵥ : StrongCastValue} →
                  Δ₁ ++ Δ₂ ⊢ cᵥ / length Δ₁ Valid →
                  Δ₂ ⊢ cᵥ Valid
valid-i-split [] (valid-zero cᵥ⋆) = cᵥ⋆
valid-i-split (a ∷ Δ₁) (valid-suc c⋆) = valid-i-split Δ₁ c⋆

run-α⇒↓ : ∀ {Δ₁ Δ₂ ι τ} →
            Run Δ₁ ⟦ inst (α τ) / ι ⟧≡ Δ₂ →
            Δ₁ ↓ ι ⇒ α
run-α⇒↓ (run-inst match-α) = here
run-α⇒↓ (run-suc sub-a run-Δ) = there (run-α⇒↓ run-Δ)

run-ρ⇒↓ : ∀ {Δ₁ Δ₂ ι σ} →
            Run Δ₁ ⟦ inst (ρ σ) / ι ⟧≡ Δ₂ →
            Δ₁ ↓ ι ⇒ ρ
run-ρ⇒↓ (run-inst match-ρ) = here
run-ρ⇒↓ (run-suc sub-a run-Δ) = there (run-ρ⇒↓ run-Δ)

private
  mutual
    valid-preᵗ : ∀ A {{_ : Substitution A ℕ}}
                     {{_ : TypeLike A}} → Set
    valid-preᵗ A = ∀ {Δ₁ Δ₂ c} {v₁ v₂ : A} →
                     Run Δ₁ ⟦ c ⟧≡ Δ₂ →
                     v₁ ⟦ Strong→WeakCast c ⟧≡ v₂ →
                     Δ₂ ⊢ v₂ Valid →
                     Δ₁ ⊢ v₁ Valid

    τ-valid-pre : valid-preᵗ Type
    τ-valid-pre {c = inst i / ι₂} {α⁼ ι₁} run-Δ (subst-α-¬inst (subst-< ι₁<ι₂)) (valid-α⁼ l)
      with run-split run-Δ
    ... | Δ₁ , Δ₁' , Δ₂ , Δ₂' , sub-Δ₁ , run-Δ₂ , eq₁ , eq₂ , eq₃
      rewrite eq₁ | eq₂ | eq₃
      with ↓-remove-right {xs₁ = Δ₁'} Δ₂' (subst (λ len → ι₁ < len) (subst-length sub-Δ₁) ι₁<ι₂) l
    ... | l' with subst-↓-pre l' sub-Δ₁
    ... | α , l'' , subst-α = valid-α⁼ (↓-add-right Δ₂ l'')
    τ-valid-pre {c = inst i / ι₂} {α⁼ (suc ι₁)} run-Δ (subst-α-¬inst (subst-inst-> (s≤s ι₁≥ι₂))) (valid-α⁼ l)
      with run-split run-Δ
    ... | Δ₁ , Δ₁' , a ∷ .Δ₂' , Δ₂' , sub-Δ₁ , run-inst m , eq₁ , eq₂ , eq₃
      rewrite eq₁ | eq₂ | eq₃
      with ↓-remove-left Δ₁' (subst (λ len → ι₁ ≥ len) (subst-length sub-Δ₁) ι₁≥ι₂) l
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
    τ-valid-pre {c = inst (α τ) / ι} {α⁼ .ι} run-Δ (subst-α-inst sub-τ) τ₂⋆ = valid-α⁼ (run-α⇒↓ run-Δ)
    τ-valid-pre {c = weaken Δ⁺ / ι₂} {α⁼ ι₁} run-Δ (subst-α-¬inst (subst-< ι₁<ι₂)) (valid-α⁼ l)
      with run-split run-Δ
    ... | Δ₁ , Δ₁' , Δ₂ , Δ₂' , sub-Δ₁ , run-Δ₂ , eq₁ , eq₂ , eq₃
      rewrite eq₁ | eq₂ | eq₃
      with ↓-remove-right {xs₁ = Δ₁'} Δ₂' (subst (λ len → ι₁ < len) (subst-length sub-Δ₁) ι₁<ι₂) l
    ... | l' with subst-↓-pre l' sub-Δ₁
    ... | α , l'' , subst-α = valid-α⁼ (↓-add-right Δ₂ l'')
    τ-valid-pre {c = weaken Δ⁺ / ι₂} {α⁼ ι₁} run-Δ (subst-α-¬inst (subst-weaken-≥ ι₁≥ι₂)) (valid-α⁼ l)
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
    τ-valid-pre {c = cᵥ / ι} {∀[ Δ ] Γ} run-Δ (subst-∀ sub-Δ sub-Γ) (valid-∀ Δ₂⋆ Γ₂⋆) =
      valid-∀ (Δ-valid-pre run-Δ sub-Δ Δ₂⋆) (Γ-valid-pre (run-combine sub-Δ run-Δ) sub-Γ Γ₂⋆)
    τ-valid-pre {v₁ = tuple τs⁻} run-Δ (subst-tuple sub-τs⁻) (valid-tuple τs⁻₂⋆) = valid-tuple (τs⁻-valid-pre run-Δ sub-τs⁻ τs⁻₂⋆)

    τ⁻-valid-pre : valid-preᵗ InitType
    τ⁻-valid-pre run-Δ (subst-τ⁻ sub-τ) (valid-τ⁻ τ⋆) = valid-τ⁻ (τ-valid-pre run-Δ sub-τ τ⋆)

    τs⁻-valid-pre : valid-preᵗ (List InitType)
    τs⁻-valid-pre run-Δ [] [] = []
    τs⁻-valid-pre run-Δ (sub-τ⁻ ∷ sub-τs⁻) (τ⁻⋆ ∷ τs⁻⋆) = τ⁻-valid-pre run-Δ sub-τ⁻ τ⁻⋆ ∷ τs⁻-valid-pre run-Δ sub-τs⁻ τs⁻⋆

    σ-valid-pre : valid-preᵗ StackType
    σ-valid-pre {c = inst i / ι₂} {ρ⁼ ι₁} run-Δ (subst-ρ-¬inst (subst-< ι₁<ι₂)) (valid-ρ⁼ l)
      with run-split run-Δ
    ... | Δ₁ , Δ₁' , Δ₂ , Δ₂' , sub-Δ₁ , run-Δ₂ , eq₁ , eq₂ , eq₃
      rewrite eq₁ | eq₂ | eq₃
      with ↓-remove-right {xs₁ = Δ₁'} Δ₂' (subst (λ len → ι₁ < len) (subst-length sub-Δ₁) ι₁<ι₂) l
    ... | l' with subst-↓-pre l' sub-Δ₁
    ... | ρ , l'' , subst-ρ = valid-ρ⁼ (↓-add-right Δ₂ l'')
    σ-valid-pre {c = inst i / ι₂} {ρ⁼ (suc ι₁)} run-Δ (subst-ρ-¬inst (subst-inst-> (s≤s ι₁≥ι₂))) (valid-ρ⁼ l)
      with run-split run-Δ
    ... | Δ₁ , Δ₁' , a ∷ .Δ₂' , Δ₂' , sub-Δ₁ , run-inst m , eq₁ , eq₂ , eq₃
      rewrite eq₁ | eq₂ | eq₃
      with ↓-remove-left Δ₁' (subst (λ len → ι₁ ≥ len) (subst-length sub-Δ₁) ι₁≥ι₂) l
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
    σ-valid-pre {c = inst (ρ σ) / ι} {ρ⁼ .ι} run-Δ (subst-ρ-inst sub-σ) σ₂⋆ = valid-ρ⁼ (run-ρ⇒↓ run-Δ)
    σ-valid-pre {c = weaken Δ⁺ / ι₂} {ρ⁼ ι₁} run-Δ (subst-ρ-¬inst (subst-< ι₁<ι₂)) (valid-ρ⁼ l)
      with run-split run-Δ
    ... | Δ₁ , Δ₁' , Δ₂ , Δ₂' , sub-Δ₁ , run-Δ₂ , eq₁ , eq₂ , eq₃
      rewrite eq₁ | eq₂ | eq₃
      with ↓-remove-right {xs₁ = Δ₁'} Δ₂' (subst (λ len → ι₁ < len) (subst-length sub-Δ₁) ι₁<ι₂) l
    ... | l' with subst-↓-pre l' sub-Δ₁
    ... | ρ , l'' , subst-ρ = valid-ρ⁼ (↓-add-right Δ₂ l'')
    σ-valid-pre {c = weaken Δ⁺ / ι₂} {ρ⁼ ι₁} run-Δ (subst-ρ-¬inst (subst-weaken-≥ ι₁≥ι₂)) (valid-ρ⁼ l)
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
    σ-valid-pre {v₁ = x ∷ v} run-Δ (sub-τ ∷ sub-σ) (τ₂⋆ ∷ σ₂⋆) = τ-valid-pre run-Δ sub-τ τ₂⋆ ∷ σ-valid-pre run-Δ sub-σ σ₂⋆

    Γ-valid-pre : valid-preᵗ RegisterAssignment
    Γ-valid-pre run-Δ (subst-registerₐ sub-sp sub-regs) (valid-registerₐ sp₂⋆ regs₂⋆) = valid-registerₐ (σ-valid-pre run-Δ sub-sp sp₂⋆) (regs-valid-pre run-Δ sub-regs regs₂⋆)

    regs-valid-pre : ∀ {m} → valid-preᵗ (Vec Type m)
    regs-valid-pre run-Δ [] [] = []
    regs-valid-pre run-Δ (sub-τ ∷ sub-τs) (τ₂⋆ ∷ τs₂⋆) = τ-valid-pre run-Δ sub-τ τ₂⋆ ∷ regs-valid-pre run-Δ sub-τs τs₂⋆

    Δ-valid-pre : valid-preᵗ TypeAssignment
    Δ-valid-pre {v₁ = []} run-Δ [] [] = []
    Δ-valid-pre {c = cᵥ / ι} {a ∷ Δ} run-Δ (sub-a ∷ sub-Δ) (a₂⋆ ∷ Δ₂⋆) = a-valid-pre (run-combine sub-Δ run-Δ) sub-a a₂⋆ ∷ Δ-valid-pre run-Δ sub-Δ Δ₂⋆

    a-valid-pre : valid-preᵗ TypeAssignmentValue
    a-valid-pre run-Δ subst-α valid-α = valid-α
    a-valid-pre run-Δ subst-ρ valid-ρ = valid-ρ

  mutual
    valid-weakenᵗ : ∀ A {{_ : Substitution A ℕ}}
                        {{_ : TypeLike A}} → Set
    valid-weakenᵗ A = ∀ Δ⁺ {Δ₁ Δ₁' Δ₂} →
                        Δ₁ ⟦ weaken Δ⁺ / zero ⟧≡ Δ₁' →
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
    valid-instᵗ : ∀ A {{_ : Substitution A ℕ}}
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
    outside-ctxᵗ : ∀ A {{_ : Substitution A ℕ}}
                       {{_ : TypeLike A}} → Set
    outside-ctxᵗ A = ∀ {Δ ι} {cᵥ : WeakCastValue} {v₁ v₂ : A} →
                       Δ ⊢ v₁ Valid →
                       v₁ ⟦ cᵥ / length Δ + ι ⟧≡ v₂ →
                       v₁ ≡ v₂

    τ-outside-ctx : outside-ctxᵗ Type
    τ-outside-ctx (valid-α⁼ l) (subst-α-¬inst (subst-< ι<len+ι')) = refl
    τ-outside-ctx {Δ} {ι} (valid-α⁼ l) (subst-α-¬inst (subst-inst-> len+ι<ι'))
      with NP.1+n≰n (NP.<-trans (↓-to-< l) (Nat-≤-trans (NP.m≤m+n (suc (length Δ)) ι) len+ι<ι'))
    ... | ()
    τ-outside-ctx {Δ} {ι} (valid-α⁼ l) (subst-α-¬inst (subst-weaken-≥ len+ι<ι'))
      with NP.1+n≰n (Nat-≤-trans (↓-to-< l) (Nat-≤-trans (NP.m≤m+n (length Δ) ι) len+ι<ι'))
    ... | ()
    τ-outside-ctx {Δ} {ι} (valid-α⁼ l) (subst-α-inst sub-τ)
      with NP.1+n≰n (Nat-≤-trans (NP.m≤m+n (suc (length Δ)) ι ) (↓-to-< l))
    ... | ()
    τ-outside-ctx valid-int subst-int = refl
    τ-outside-ctx valid-ns subst-ns = refl
    τ-outside-ctx {Δ} {ι} (valid-∀ Δ⋆ Γ⋆) (subst-∀ {Δ' = Δ'} sub-Δ sub-Γ)
      rewrite Δ-outside-ctx Δ⋆ sub-Δ
            | sym (+-assoc (length Δ') (length Δ) ι)
            | sym (List-length-++ Δ' {Δ})
            | Γ-outside-ctx Γ⋆ sub-Γ = refl
    τ-outside-ctx (valid-tuple τs⁻⋆) (subst-tuple sub-τs⁻)
      rewrite τs⁻-outside-ctx τs⁻⋆ sub-τs⁻ = refl

    τ⁻-outside-ctx : outside-ctxᵗ InitType
    τ⁻-outside-ctx (valid-τ⁻ τ⋆) (subst-τ⁻ sub-τ)
      rewrite τ-outside-ctx τ⋆ sub-τ = refl

    τs⁻-outside-ctx : outside-ctxᵗ (List InitType)
    τs⁻-outside-ctx [] [] = refl
    τs⁻-outside-ctx (τ⁻⋆ ∷ τs⁻⋆) (sub-τ⁻ ∷ sub-τs⁻)
      rewrite τ⁻-outside-ctx τ⁻⋆ sub-τ⁻
            | τs⁻-outside-ctx τs⁻⋆ sub-τs⁻ = refl

    σ-outside-ctx : outside-ctxᵗ StackType
    σ-outside-ctx (valid-ρ⁼ l) (subst-ρ-¬inst (subst-< ι<len+ι')) = refl
    σ-outside-ctx {Δ} {ι} (valid-ρ⁼ l) (subst-ρ-¬inst (subst-inst-> len+ι<ι'))
      with NP.1+n≰n (NP.<-trans (↓-to-< l) (Nat-≤-trans (NP.m≤m+n (suc (length Δ)) ι) len+ι<ι'))
    ... | ()
    σ-outside-ctx {Δ} {ι} (valid-ρ⁼ l) (subst-ρ-¬inst (subst-weaken-≥ len+ι<ι'))
      with NP.1+n≰n (Nat-≤-trans (↓-to-< l) (Nat-≤-trans (NP.m≤m+n (length Δ) ι) len+ι<ι'))
    ... | ()
    σ-outside-ctx {Δ} {ι} (valid-ρ⁼ l) (subst-ρ-inst sub-σ)
      with NP.1+n≰n (Nat-≤-trans (NP.m≤m+n (suc (length Δ)) ι ) (↓-to-< l))
    ... | ()
    σ-outside-ctx valid-[] subst-[] = refl
    σ-outside-ctx (τ⋆ ∷ σ⋆) (sub-τ ∷ sub-σ)
      rewrite τ-outside-ctx τ⋆ sub-τ
            | σ-outside-ctx σ⋆ sub-σ = refl

    Γ-outside-ctx : outside-ctxᵗ RegisterAssignment
    Γ-outside-ctx (valid-registerₐ sp⋆ regs⋆) (subst-registerₐ sub-sp sub-regs)
      rewrite σ-outside-ctx sp⋆ sub-sp
            | regs-outside-ctx regs⋆ sub-regs = refl

    regs-outside-ctx : ∀ {m} → outside-ctxᵗ (Vec Type m)
    regs-outside-ctx [] [] = refl
    regs-outside-ctx (τ⋆ ∷ τs⋆) (sub-τ ∷ sub-τs)
      rewrite τ-outside-ctx τ⋆ sub-τ
            | regs-outside-ctx τs⋆ sub-τs = refl

    Δ-outside-ctx : outside-ctxᵗ TypeAssignment
    Δ-outside-ctx [] [] = refl
    Δ-outside-ctx {Δ} {ι} {v₁ = a₁ ∷ Δ₁} {v₂ = a₂ ∷ Δ₂} (a⋆ ∷ Δ⋆) (sub-a ∷ sub-Δ)
      rewrite Δ-outside-ctx Δ⋆ sub-Δ
            | sym (+-assoc (length Δ₂) (length Δ) ι)
            | sym (List-length-++ Δ₂ {Δ})
            | a-outside-ctx a⋆ sub-a = refl

    a-outside-ctx : outside-ctxᵗ TypeAssignmentValue
    a-outside-ctx valid-α subst-α = refl
    a-outside-ctx valid-ρ subst-ρ = refl

valid-i⇒match : ∀ {a i Δ} →
                  a ∷ Δ ⊢ i Valid →
                  ReferenceMatch a i
valid-i⇒match (valid-α τ⋆) = match-α
valid-i⇒match (valid-ρ σ⋆) = match-ρ

can-run : ∀ {Δ} → [] ⊢ Δ Valid →
          ∀ {c} → Δ  ⊢ c Valid →
            ∃ λ Δ' →
              Run Δ ⟦ c ⟧≡ Δ'
can-run [] {inst i / zero} (valid-zero (valid-inst ()))
can-run {a ∷ Δ} (a⋆ ∷ Δ⋆) {inst i / zero} (valid-zero (valid-inst i⋆)) =
  Δ , run-inst (valid-i⇒match i⋆)
can-run {Δ} Δ⋆ {weaken Δ⁺ / zero} (valid-zero (valid-weaken Δ⁺⋆)) =
  Δ⁺ ++ Δ , run-weaken
can-run [] {cᵥ / suc ι} ()
can-run {a₁ ∷ Δ} (a₁⋆ ∷ Δ⋆) {inst i / suc ι} (valid-suc c⋆)
  with can-run Δ⋆ c⋆
... | Δ' , run-Δ with run-split run-Δ
... | Δ₁ , Δ₁' , (a₂ ∷ Δ₂) , .Δ₂ , sub-Δ₁ , run-inst m , eq₁ , eq₂ , eq₃
  rewrite eq₁ | eq₂ | eq₃ with valid-i-split Δ₁ c⋆
... | valid-inst i⋆ with a-valid-inst i⋆ sub-Δ₁
                           (subst₂ _⊢_Valid
                                   (List-++-right-identity (Δ₁ ++ a₂ ∷ Δ₂))
                                   refl
                                   a₁⋆)
... | a₁' , sub-a₁ , a₁'⋆ =
      a₁' ∷ Δ₁' ++ Δ₂ ,
      run-combine' (ι-subst (+-comm 0 (length Δ₁)) sub-a₁ ∷ sub-Δ₁)
                   (run-inst (valid-i⇒match i⋆))
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
      run-combine' (ι-subst (+-comm 0 (length Δ₁)) sub-a₁ ∷ sub-Δ₁)
                   (run-weaken {Δ₂} {Δ⁺})

record Substitution⁺ (A : Set) (s : Substitution A TypeAssignment)
                               (_ : TypeLike A) : Set where
  constructor substitution⁺
  field
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
    subst-valid-pre :
      ∀ {Δ₁ Δ₂ c} {v v' : A} →
        Run Δ₁ ⟦ c ⟧≡ Δ₂ →
        v ⟦ c ⟧≡ v' →
        Δ₂ ⊢ v' Valid →
        Δ₁ ⊢ v Valid
    subst-outside-ctx :
      ∀ {cᵥ : StrongCastValue} {ι Δ} {v₁ v₂ : A} →
        Δ ⊢ v₁ Valid →
        v₁ ⟦ cᵥ / length Δ + ι ⟧≡ v₂ →
        v₁ ≡ v₂
  can-subst : ∀ {Δ Δ'} {c : StrongCast} {v : A} →
                Δ ⊢ c Valid →
                Run Δ ⟦ c ⟧≡ Δ' →
                Δ ⊢ v Valid →
                ∃ λ v' →
                  v ⟦ c ⟧≡ v' ×
                  Δ' ⊢ v' Valid
  can-subst {c = inst i / ι} c⋆ run-Δ v⋆ with run-split run-Δ
  ... | Δ₁ , Δ₁' , (a ∷ Δ₂) , .Δ₂ , sub-Δ₁ , run-inst m , eq₁ , eq₂ , eq₃
    rewrite eq₁ | eq₂ | eq₃ with valid-i-split Δ₁ c⋆
  ... | valid-inst i⋆ = subst-valid-inst i⋆ sub-Δ₁ v⋆
  can-subst {c = weaken Δ⁺ / ι} c⋆ run-Δ v⋆ with run-split run-Δ
  ... | Δ₁ , Δ₁' , Δ₂ , .(Δ⁺ ++ Δ₂) , sub-Δ₁ , run-weaken , eq₁ , eq₂ , eq₃
    rewrite eq₁ | eq₂ | eq₃ =
      subst-valid-weaken Δ⁺ sub-Δ₁ v⋆

  subst-valid : ∀ {Δ Δ'} {c : StrongCast} {v v' : A} →
                  Δ ⊢ c Valid →
                  Run Δ ⟦ c ⟧≡ Δ' →
                  Δ ⊢ v Valid →
                  v ⟦ c ⟧≡ v' →
                  Δ' ⊢ v' Valid
  subst-valid c⋆ run-Δ v⋆ sub-v
    with can-subst c⋆ run-Δ v⋆
  ... | v'' , sub-v'' , v''⋆ with subst-unique {{s}} sub-v sub-v''
  ... | eq rewrite eq = v''⋆

  subst-empty-ctx : ∀ {v₁ v₂ : A} {c : StrongCast} →
                      [] ⊢ v₁ Valid →
                      v₁ ⟦ c ⟧≡ v₂ →
                      v₁ ≡ v₂
  subst-empty-ctx {c = cᵥ / ι} v⋆ sub-v = subst-outside-ctx v⋆ sub-v

open Substitution⁺ {{...}} public

Vec-Substitution⁺ : ∀ {A S T m} {{_ : Substitution⁺ A S T}} →
                      Substitution⁺ (Vec A m) Vec-Substitution Vec-typeLike
Vec-Substitution⁺ {A} =
    substitution⁺ xs-valid-inst xs-valid-weaken xs-valid-pre xs-outside-ctx
  where xs-valid-inst : ∀ {m Δ₁ Δ₁' Δ₂ a i} →
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

        xs-valid-pre : ∀ {m Δ₁ Δ₂ c} {xs₁ xs₂ : Vec A m} →
                         Run Δ₁ ⟦ c ⟧≡ Δ₂ →
                         _⟦_⟧≡_ {{Vec-Substitution}} xs₁ c xs₂ →
                         _⊢_Valid {{Vec-typeLike}} Δ₂ xs₂ →
                         _⊢_Valid {{Vec-typeLike}} Δ₁ xs₁
        xs-valid-pre run-Δ [] [] = []
        xs-valid-pre run-Δ (sub-x ∷ sub-xs) (x₂⋆ ∷ xs₂⋆) = subst-valid-pre run-Δ sub-x x₂⋆ ∷ xs-valid-pre run-Δ sub-xs xs₂⋆

        xs-outside-ctx : ∀ {Δ ι m} {cᵥ : StrongCastValue} {xs₁ xs₂ : Vec A m} →
                           _⊢_Valid {{Vec-typeLike}} Δ xs₁ →
                           _⟦_⟧≡_ {{Vec-Substitution}} xs₁ (cᵥ / length Δ + ι) xs₂ →
                           xs₁ ≡ xs₂
        xs-outside-ctx [] [] = refl
        xs-outside-ctx (x⋆ ∷ xs⋆) (sub-x ∷ sub-xs)
          rewrite subst-outside-ctx x⋆ sub-x
                | xs-outside-ctx xs⋆ sub-xs = refl

List-Substitution⁺ : ∀ {A S T} {{_ : Substitution⁺ A S T}} →
                       Substitution⁺ (List A) List-Substitution List-typeLike
List-Substitution⁺ {A} =
    substitution⁺ xs-valid-inst xs-valid-weaken xs-valid-pre xs-outside-ctx
  where xs-valid-inst : ∀ {Δ₁ Δ₁' Δ₂ a i} →
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

        xs-valid-pre : ∀ {Δ₁ Δ₂ c} {xs₁ xs₂ : List A} →
                         Run Δ₁ ⟦ c ⟧≡ Δ₂ →
                         _⟦_⟧≡_ {{List-Substitution}} xs₁ c xs₂ →
                         _⊢_Valid {{List-typeLike}} Δ₂ xs₂ →
                         _⊢_Valid {{List-typeLike}} Δ₁ xs₁
        xs-valid-pre run-Δ [] [] = []
        xs-valid-pre run-Δ (sub-x ∷ sub-xs) (x₂⋆ ∷ xs₂⋆) = subst-valid-pre run-Δ sub-x x₂⋆ ∷ xs-valid-pre run-Δ sub-xs xs₂⋆

        xs-outside-ctx : ∀ {Δ ι} {cᵥ : StrongCastValue} {xs₁ xs₂ : List A} →
                           _⊢_Valid {{List-typeLike}} Δ xs₁ →
                           _⟦_⟧≡_ {{List-Substitution}} xs₁ (cᵥ / length Δ + ι) xs₂ →
                           xs₁ ≡ xs₂
        xs-outside-ctx [] [] = refl
        xs-outside-ctx (x⋆ ∷ xs⋆) (sub-x ∷ sub-xs)
          rewrite subst-outside-ctx x⋆ sub-x
                | xs-outside-ctx xs⋆ sub-xs = refl

instance
  Type-Substitution⁺ : Substitution⁺ Type Weak→StrongSubstitution
                                          Type-typeLike
  Type-Substitution⁺ = substitution⁺
    τ-valid-inst τ-valid-weaken τ-valid-pre τ-outside-ctx

  TypeVec-Substitution⁺ : ∀ {m} → Substitution⁺ (Vec Type m) Vec-Substitution
                                                             Vec-typeLike
  TypeVec-Substitution⁺ = Vec-Substitution⁺

  TypeList-Substitution⁺ : Substitution⁺ (List Type) List-Substitution
                                                     List-typeLike
  TypeList-Substitution⁺ = List-Substitution⁺

  InitType-Substitution⁺ : Substitution⁺ InitType Weak→StrongSubstitution
                                                  InitType-typeLike
  InitType-Substitution⁺ = substitution⁺
    τ⁻-valid-inst τ⁻-valid-weaken τ⁻-valid-pre τ⁻-outside-ctx

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
    σ-valid-inst σ-valid-weaken σ-valid-pre σ-outside-ctx

  TypeAssignment-Substitution⁺ : Substitution⁺ TypeAssignment
                                               Weak→StrongSubstitution
                                               TypeAssignment-typeLike
  TypeAssignment-Substitution⁺ = substitution⁺
    Δ-valid-inst Δ-valid-weaken Δ-valid-pre Δ-outside-ctx

  TypeAssignmentValue-Substitution⁺ : Substitution⁺
                                        TypeAssignmentValue
                                        Weak→StrongSubstitution
                                        TypeAssignmentValue-typeLike
  TypeAssignmentValue-Substitution⁺ = substitution⁺
    a-valid-inst a-valid-weaken a-valid-pre a-outside-ctx

  RegisterAssignment-Substitution⁺ : Substitution⁺ RegisterAssignment Weak→StrongSubstitution
                                                   RegisterAssignment-typeLike
  RegisterAssignment-Substitution⁺ = substitution⁺
    Γ-valid-inst Γ-valid-weaken Γ-valid-pre Γ-outside-ctx
