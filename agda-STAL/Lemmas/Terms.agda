module Lemmas.Terms where

open import Util
open import Judgments
open import Lemmas.Equality
open import Lemmas.Types
open import Lemmas.Substitution
open import Lemmas.TypeSubstitution
open import Lemmas.Subtypes
import Data.Nat.Properties as NP

private
  lookup-helper : ∀ {n} i pos inc (τs : Vec Type n) →
                    weaken pos inc (lookup i τs) ≡ lookup i (weaken pos inc τs)
  lookup-helper zero pos inc (τ ∷ τs) = refl
  lookup-helper (suc i) pos inc (τ ∷ τs) = lookup-helper i pos inc τs

  register-helper : ∀ ♯r pos inc Γ →
                      weaken pos inc (lookup-regs ♯r Γ) ≡ lookup-regs ♯r (weaken pos inc Γ)
  register-helper ♯r pos inc (registerₐ sp regs) = lookup-helper ♯r pos inc regs

mutual
  gval-valid-type : ∀ {ψ₁ g τ} →
                      ψ₁ ⊢ g of τ gval →
                      [] ⊢ τ Valid
  gval-valid-type (of-gval {Δ = Δ} Γ⋆ I⋆) = valid-∀ (subst₂ _⊢_Valid (sym (List-++-right-identity Δ)) refl Γ⋆)

  gvals-valid-type : ∀ {ψ₁ gs τs} →
                       AllZip (λ g τ → ψ₁ ⊢ g of τ gval) gs τs →
                       [] ⊢ τs Valid
  gvals-valid-type [] = []
  gvals-valid-type (g⋆ ∷ gs⋆) = gval-valid-type g⋆ ∷ gvals-valid-type gs⋆

  globals-valid-type : ∀ {ψ₁ G} →
                         ⊢ G of ψ₁ globals →
                         [] ⊢ ψ₁ Valid
  globals-valid-type (of-globals gs⋆) = gvals-valid-type gs⋆

mutual
  hval-valid-type : ∀ {ψ₁ ψ₂ h τ} →
                      ψ₁ , ψ₂ ⊢ h of τ hval →
                      [] ⊢ τ Valid
  hval-valid-type (of-tuple ws⋆) = valid-tuple (wvals⁰-valid-type ws⋆)

  hvals-valid-type : ∀ {ψ₁ ψ₂ hs τs} →
                       AllZip (λ h τ → ψ₁ , ψ₂ ⊢ h of τ hval) hs τs →
                       [] ⊢ τs Valid
  hvals-valid-type [] = []
  hvals-valid-type (h⋆ ∷ hs⋆) = hval-valid-type h⋆ ∷ hvals-valid-type hs⋆

  heap-valid-type : ∀ {ψ₁ H ψ₂} →
                      ψ₁ ⊢ H of ψ₂ heap →
                      [] ⊢ ψ₂ Valid
  heap-valid-type (of-heap hs⋆) = hvals-valid-type hs⋆

  wval-valid-type : ∀ {ψ₁ ψ₂ w τ} →
                      ψ₁ , ψ₂ ⊢ w of τ wval →
                      [] ⊢ τ Valid
  wval-valid-type (of-globval l lookup≤τ) = proj₂ (≤-valid lookup≤τ)
  wval-valid-type (of-heapval l lookup≤τ) = proj₂ (≤-valid lookup≤τ)
  wval-valid-type of-int = valid-int
  wval-valid-type of-ns = valid-ns
  wval-valid-type (of-Λ {Δ₁ = Δ₁} {Δ₂} w⋆ is⋆ subs-Γ Γ₃≤Γ₂) = valid-∀ (proj₁ (≤-valid (≤-++ Γ₃≤Γ₂)))

  wval⁰-valid-type : ∀ {ψ₁ ψ₂ w τ⁻} →
                       ψ₁ , ψ₂ ⊢ w of τ⁻ wval⁰ →
                       [] ⊢ τ⁻ Valid
  wval⁰-valid-type (of-uninit τ⋆) = valid-τ⁻ τ⋆
  wval⁰-valid-type (of-init w⋆) = valid-τ⁻ (wval-valid-type w⋆)

  wvals⁰-valid-type : ∀ {ψ₁ ψ₂ ws τs⁻} →
                        AllZip (λ w τ⁻ → ψ₁ , ψ₂ ⊢ w of τ⁻ wval⁰) ws τs⁻ →
                        [] ⊢ τs⁻ Valid
  wvals⁰-valid-type [] = []
  wvals⁰-valid-type (w⋆ ∷ ws⋆) = wval⁰-valid-type w⋆ ∷ wvals⁰-valid-type ws⋆

stack-valid-type : ∀ {ψ₁ ψ₂ sp σ} →
                     ψ₁ , ψ₂ ⊢ sp of σ stack →
                     [] ⊢ σ Valid
stack-valid-type [] = []
stack-valid-type (w⋆ ∷ sp⋆) = wval-valid-type w⋆ ∷ stack-valid-type sp⋆

regs-valid-type : ∀ {ψ₁ ψ₂ n} {regs : Vec WordValue n} {τs} →
                    AllZipᵥ (λ w τ → ψ₁ , ψ₂ ⊢ w of τ wval) regs τs →
                    [] ⊢ τs Valid
regs-valid-type [] = []
regs-valid-type (w⋆ ∷ regs⋆) = wval-valid-type w⋆ ∷ regs-valid-type regs⋆

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

Γ-weaken-inner : ∀ pos inc {Γ₁ Γ₂ : RegisterAssignment} {is} →
                   Γ₁ ⟦ is / 0 ⟧many≡ Γ₂ →
                   weaken (length is + pos) inc Γ₁ ⟦ weaken pos inc is / 0 ⟧many≡ weaken pos inc Γ₂
Γ-weaken-inner = {!!}

is-length : ∀ {Δ₁ Δ₂ is} →
              Δ₁ ⊢ is of Δ₂ instantiations →
              length is ≡ length Δ₂
is-length [] = refl
is-length (i⋆ ∷ is⋆) = cong suc (is-length is⋆)

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
  with Γ-weaken-inner (length Δₒ + length Δ₁) (length Δ₂) subs-Γ
... | subs-Γ'
  rewrite is-length is⋆
  with begin
    length Δᵢ + (length Δₒ + length Δ₁)
  ⟨ +-assoc (length Δᵢ) (length Δₒ) (length Δ₁) ⟩≡
    (length Δᵢ + length Δₒ) + length Δ₁
  ≡⟨ +-comm (length Δᵢ) (length Δₒ) ∥ (λ v → v + length Δ₁) ⟩
    (length Δₒ + length Δᵢ) + length Δ₁
  ≡⟨ +-assoc (length Δₒ) (length Δᵢ) (length Δ₁) ⟩
    length Δₒ + (length Δᵢ + length Δ₁)
  ∎ where open Eq-Reasoning
... | eq
  rewrite eq
  = of-Λ (vval-weaken Δ₁ Δ₂ Δ₃ ψ₁⋆ Γ⋆ v⋆) is⋆' (subst (λ lhs → lhs ⟦ weaken (length Δₒ + length Δ₁) (length Δ₂) is / 0 ⟧many≡ weaken (length Δₒ + length Δ₁) (length Δ₂) Γₒ) (sym (weaken-exchange (length Δ₂) (length Δₒ) (NP.m≤m+n (length Δᵢ) (length Δ₁)) Γᵢ)) subs-Γ' )
