module Lemmas.Run where

open import Util
open import Judgments
open import Lemmas.Misc
open import Lemmas.Substitution
open import Lemmas.TypeSubstitution

-- The purpose of this of this file is two show,
-- uniqueness, decidibility and effectiveness of
-- updating TypeAssignment's using substitutions.

run-unique : ∀ {Δ Δ₁ Δ₂ c} →
               Run Δ ⟦ c ⟧≡ Δ₁ →
               Run Δ ⟦ c ⟧≡ Δ₂ →
               Δ₁ ≡ Δ₂
run-unique (run-inst m₁) (run-inst m₂) = refl
run-unique run-weaken run-weaken = refl
run-unique (run-suc sub-a₁ run-Δ₁) (run-suc sub-a₂ run-Δ₂) =
  cong₂ _∷_ (subst-unique sub-a₁ sub-a₂)
            (run-unique run-Δ₁ run-Δ₂)

infix 3 Run_⟦_⟧?
Run_⟦_⟧? : ∀ Δ c → Dec (∃ λ Δ' → Run Δ ⟦ c ⟧≡ Δ')
Run [] ⟦ inst i / ι ⟧? = no (λ { (_ , ()) })
Run [] ⟦ weaken Δ⁺ / zero ⟧? = yes (Δ⁺ ++ [] , run-weaken)
Run [] ⟦ weaken Δ⁺ / suc ι ⟧? = no (λ { (_ , ()) })
Run α ∷ Δ ⟦ inst (α τ) / zero ⟧? = yes (Δ , run-inst match-α)
Run α ∷ Δ ⟦ inst (ρ σ) / zero ⟧? = no (λ { (_ , run-inst ()) })
Run ρ ∷ Δ ⟦ inst (α τ) / zero ⟧? = no (λ { (_ , run-inst ()) })
Run ρ ∷ Δ ⟦ inst (ρ σ) / zero ⟧? = yes (Δ , run-inst match-ρ)
Run a ∷ Δ ⟦ weaken Δ⁺ / zero ⟧? = yes (Δ⁺ ++ a ∷ Δ , run-weaken)
Run a ∷ Δ ⟦ cᵥ / suc ι ⟧? with a ⟦ Strong→Weak cᵥ / ι ⟧? | Run Δ ⟦ cᵥ / ι ⟧?
... | yes (a' , sub-a) |
  yes (Δ' , run-Δ) = yes (a' ∷ Δ' , run-suc sub-a run-Δ)
... | no ¬sub-a | _ =
  no (λ { (a' ∷ Δ' , run-suc sub-a run-Δ) → ¬sub-a (a' , sub-a)})
... | _ | no ¬run-Δ =
  no (λ { (a' ∷ Δ' , run-suc sub-a run-Δ) → ¬run-Δ (Δ' , run-Δ)})

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
... | valid-inst i⋆ with subst-valid-inst i⋆ sub-Δ₁
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
  rewrite eq₁ | eq₂ | eq₃ with subst-valid-weaken Δ⁺ sub-Δ₁
                                 (subst₂ _⊢_Valid
                                         (List-++-right-identity (Δ₁ ++ Δ₂))
                                         refl
                                         a⋆)
... | a₁' , sub-a₁ , a₁'⋆ =
      a₁' ∷ Δ₁' ++ Δ⁺ ++ Δ₂ ,
      run-combine' (ι-subst (+-comm 0 (length Δ₁)) sub-a₁ ∷ sub-Δ₁)
                   (run-weaken {Δ₂} {Δ⁺})
