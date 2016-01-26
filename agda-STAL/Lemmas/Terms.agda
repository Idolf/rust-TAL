module Lemmas.Terms where

open import Util
open import Judgments
open import Lemmas.Equality
open import Lemmas.Types
open import Lemmas.TypeSubstitution

private
  lookup-helper : ∀ {n} i pos inc (τs : Vec Type n) →
                    weaken pos inc (lookup i τs) ≡ lookup i (weaken pos inc τs)
  lookup-helper zero pos inc (τ ∷ τs) = refl
  lookup-helper (suc i) pos inc (τ ∷ τs) = lookup-helper i pos inc τs

  register-helper : ∀ ♯r pos inc Γ →
                      weaken pos inc (lookup-regs ♯r Γ) ≡ lookup-regs ♯r (weaken pos inc Γ)
  register-helper ♯r pos inc (registerₐ sp regs) = lookup-helper ♯r pos inc regs



vval-valid-type : ∀ {ψ₁ Δ Γ τ} →
                    [] ⊢ ψ₁ Valid →
                    Δ ⊢ Γ Valid →
                    {v : SmallValue} →
                    ψ₁ , Δ , Γ ⊢ v of τ vval →
                    Δ ⊢ τ Valid
vval-valid-type ψ₁⋆ (valid-registerₐ sp⋆ regs⋆) {reg ♯r} of-reg = Allᵥ-lookup ♯r regs⋆
vval-valid-type ψ₁⋆ Γ⋆ (of-globval l) = valid-++ (All-lookup l ψ₁⋆)
vval-valid-type ψ₁⋆ Γ⋆ of-int = valid-int
vval-valid-type ψ₁⋆ Γ⋆ of-ns = valid-ns
vval-valid-type ψ₁⋆ Γ⋆ (of-Λ {Δ = Δ} {Δ₁ = Δ₁} {Δ₂} v⋆ is⋆ subs-Γ)
  with vval-valid-type ψ₁⋆ Γ⋆ v⋆
... | valid-∀ Γ⋆'
  with valid-weaken Δ₁ Δ₂ Δ Γ⋆'
... | Γ⋆''
  rewrite List-++-right-identity Δ
  with valid-subst-many [] {Δ₁} {Δ₂ ++ Δ} is⋆ Γ⋆'' subs-Γ
... | Γ⋆'''
  = valid-∀ Γ⋆'''

i-weaken : ∀ Δ₁ Δ₂ Δ₃ {i a} →
             Δ₁ ++ Δ₃ ⊢ i of a instantiation →
             Δ₁ ++ Δ₂ ++ Δ₃ ⊢ weaken (length Δ₁) (length Δ₂) i of a instantiation
i-weaken Δ₁ Δ₂ Δ₃ (of-α τ⋆) = of-α (valid-weaken Δ₁ Δ₂ Δ₃ τ⋆)
i-weaken Δ₁ Δ₂ Δ₃ (of-ρ σ⋆) = of-ρ (valid-weaken Δ₁ Δ₂ Δ₃ σ⋆)

is-weaken : ∀ Δ₁ Δ₂ Δ₃ {is Δ} →
              Δ₁ ++ Δ₃ ⊢ is of Δ instantiations →
              Δ₁ ++ Δ₂ ++ Δ₃ ⊢ weaken (length Δ₁) (length Δ₂) is of Δ instantiations
is-weaken Δ₁ Δ₂ Δ₃ [] = []
is-weaken Δ₁ Δ₂ Δ₃ (i⋆ ∷ is⋆) = i-weaken Δ₁ Δ₂ Δ₃ i⋆ ∷ is-weaken Δ₁ Δ₂ Δ₃ is⋆

vval-weaken : ∀ Δ₁ Δ₂ Δ₃ {ψ₁} →
                [] ⊢ ψ₁ Valid →
                ∀ {Γ} →
                Δ₁ ++ Δ₃ ⊢ Γ Valid →
                ∀ {v τ} →
                ψ₁ , Δ₁ ++ Δ₃ , Γ ⊢ v of τ vval →
                ψ₁ , Δ₁ ++ Δ₂ ++ Δ₃ , weaken (length Δ₁) (length Δ₂) Γ ⊢ weaken (length Δ₁) (length Δ₂) v of weaken (length Δ₁) (length Δ₂) τ vval
vval-weaken Δ₁ Δ₂ Δ₃ ψ₁⋆ {Γ} Γ⋆ {reg ♯r} of-reg
  rewrite register-helper ♯r (length Δ₁) (length Δ₂) Γ = of-reg
vval-weaken Δ₁ Δ₂ Δ₃ {ψ₁} ψ₁⋆ Γ⋆ {globval lab} (of-globval l)
  with weaken-empty-ctx (length Δ₁) (length Δ₂) (All-lookup l ψ₁⋆)
... | eq = of-globval (subst (λ τ → ψ₁ ↓ lab ⇒ τ) (sym eq) l)
vval-weaken Δ₁ Δ₂ Δ₃ ψ₁⋆ Γ⋆ of-int = of-int
vval-weaken Δ₁ Δ₂ Δ₃ ψ₁⋆ Γ⋆ of-ns = of-ns
vval-weaken Δ₁ Δ₂ Δ₃ ψ₁⋆ {Γ} Γ⋆ {Λ Δₒ ∙ v ⟦ is ⟧} (of-Λ {Δ₁ = Δᵢ} .{Δ₂ = Δₒ} {Γᵢ} {Γₒ} v⋆ is⋆ subs-Γ)
  rewrite sym (List-++-assoc Δₒ Δ₁ Δ₃)
  with is-weaken (Δₒ ++ Δ₁) Δ₂ Δ₃ is⋆
... | is⋆'
  rewrite List-length-++ Δₒ {Δ₁}
        | List-++-assoc Δₒ Δ₁ (Δ₂ ++ Δ₃)
  with vval-valid-type ψ₁⋆ Γ⋆ v⋆
... | valid-∀ Γᵢ⋆
  rewrite sym (List-++-assoc Δᵢ Δ₁ Δ₃)
  with valid-weaken (Δᵢ ++ Δ₁) Δ₂ Δ₃ Γᵢ⋆
... | Γᵢ⋆w
        = of-Λ (vval-weaken Δ₁ Δ₂ Δ₃ ψ₁⋆ Γ⋆ v⋆) is⋆' {!Γᵢ⋆w!}
