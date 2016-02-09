module Lemmas.TermValidType where

open import Util
open import Judgments
open import Lemmas.Types using (≤-valid₁ ; ≤-valid₂)
open import Lemmas.TypeSubstitution using (valid-++)

-- The purpose of this file is to prove that if a term
-- has a specific type, then that type is also valid.

private
  gval-valid-type : ∀ {ψ₁ g τ} →
                      ψ₁ ⊢ g of τ gval →
                      [] ⊢ τ Valid
  gval-valid-type (of-gval {Δ = Δ} Γ⋆ I⋆) = valid-∀ (subst₂ _⊢_Valid (sym (List-++-right-identity Δ)) refl Γ⋆)

globals-valid-type : ∀ {ψ₁ G} →
                       ⊢ G of ψ₁ globals →
                       [] ⊢ ψ₁ Valid
globals-valid-type (of-globals gs⋆) = AllZip-extract→ gval-valid-type gs⋆

wval-valid-type : ∀ {ψ₁ ψ₂ w τ} →
                    ψ₁ , ψ₂ ⊢ w of τ wval →
                    [] ⊢ τ Valid
wval-valid-type (of-globval l lookup≤τ) = ≤-valid₂ lookup≤τ
wval-valid-type (of-heapval l lookup≤τ) = ≤-valid₂ lookup≤τ
wval-valid-type of-int = valid-int
wval-valid-type of-ns = valid-ns
wval-valid-type (of-Λ {Δ₁ = Δ₁} {Δ₂} w⋆ θs⋆ subs-Γ Γ₃≤Γ₂) = valid-∀ (valid-++ (≤-valid₁ Γ₃≤Γ₂))

wval⁰-valid-type : ∀ {ψ₁ ψ₂ w τ⁻} →
                     ψ₁ , ψ₂ ⊢ w of τ⁻ wval⁰ →
                     [] ⊢ τ⁻ Valid
wval⁰-valid-type (of-uninit τ⋆) = valid-τ⁻ τ⋆
wval⁰-valid-type (of-init w⋆) = valid-τ⁻ (wval-valid-type w⋆)

hval-valid-type : ∀ {ψ₁ ψ₂ h τ} →
                    ψ₁ , ψ₂ ⊢ h of τ hval →
                    [] ⊢ τ Valid
hval-valid-type (of-tuple ws⋆) = valid-tuple (AllZip-extract→ wval⁰-valid-type ws⋆)
