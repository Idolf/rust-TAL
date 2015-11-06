module Lemmas.Misc where

open import Util
open import Judgments

-- The purpose of this file is to provide
-- various small helper functions that I have
-- not found a better place to put

ι-subst : ∀ {A} {{_ : Substitution A}}
            {x x' : A} {cᵥ ι₁ ι₂} →
            ι₁ ≡ ι₂ →
            x ⟦ cᵥ / ι₁ ⟧≡ x' →
            x ⟦ cᵥ / ι₂ ⟧≡ x'
ι-subst {x = x} {x'} {cᵥ} eq sub-x = subst (λ ι → x ⟦ cᵥ / ι ⟧≡ x') eq sub-x

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

subst-combine : ∀ {Δ₁ Δ₁' Δ₂ Δ₂' : TypeAssignment} {cᵥ} →
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

valid-i⇒match : ∀ {a i Δ} →
                  a ∷ Δ ⊢ i Valid →
                  ReferenceMatch a i
valid-i⇒match (valid-α τ⋆) = match-α
valid-i⇒match (valid-ρ σ⋆) = match-ρ

c-valid-add-left : ∀ Δ₁ {Δ₂ ι} {cᵥ : StrongCastValue} →
                     Δ₂ ⊢ cᵥ / ι Valid →
                     Δ₁ ++ Δ₂ ⊢ cᵥ / length Δ₁ + ι Valid
c-valid-add-left [] c⋆ = c⋆
c-valid-add-left (a ∷ Δ₁) c⋆ = valid-suc (c-valid-add-left Δ₁ c⋆)

c-valid-remove-left : ∀ Δ₁ {Δ₂ ι} {cᵥ : StrongCastValue} →
                        Δ₁ ++ Δ₂ ⊢ cᵥ / length Δ₁ + ι Valid →
                        Δ₂ ⊢ cᵥ / ι Valid
c-valid-remove-left [] c⋆ = c⋆
c-valid-remove-left (a ∷ Δ₁) (valid-suc c⋆) = c-valid-remove-left Δ₁ c⋆

run-combine : ∀ {Δ₁ Δ₁' Δ₂ Δ₂' cᵥ ι} →
                Δ₁ ⟦ Strong→Weak cᵥ / ι ⟧≡ Δ₁' →
                Run Δ₂ ⟦ cᵥ / ι ⟧≡ Δ₂' →
                Run Δ₁ ++ Δ₂ ⟦ cᵥ / length Δ₁ + ι ⟧≡ Δ₁' ++ Δ₂'
run-combine {[]} [] run-Δ₂ = run-Δ₂
run-combine {a ∷ Δ₁} (sub-a ∷ sub-Δ₁) run-Δ₂ =
  run-suc sub-a (run-combine sub-Δ₁ run-Δ₂)

run-combine' : ∀ {Δ₁ Δ₁' Δ₂ Δ₂' cᵥ} →
                 Δ₁ ⟦ Strong→Weak cᵥ / 0 ⟧≡ Δ₁' →
                 Run Δ₂ ⟦ cᵥ / 0 ⟧≡ Δ₂' →
                 Run Δ₁ ++ Δ₂ ⟦ cᵥ / length Δ₁ ⟧≡ Δ₁' ++ Δ₂'
run-combine' {Δ₁} sub-Δ₁ run-Δ₂ with run-combine sub-Δ₁ run-Δ₂
... | run-Δ rewrite +-comm (length Δ₁) 0 = run-Δ

run-split : ∀ {Δ Δ' cᵥ ι} →
              Run Δ ⟦ cᵥ / ι ⟧≡ Δ' →
              ∃₂ λ Δ₁ Δ₁' → ∃₂ λ Δ₂ Δ₂' →
                Δ₁ ⟦ Strong→Weak cᵥ / zero ⟧≡ Δ₁' ×
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
