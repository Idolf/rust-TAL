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
  weaken-lookup-helper : ∀ {n} ♯r pos inc (τs : Vec Type n) →
                    weaken pos inc (lookup ♯r τs) ≡ lookup ♯r (weaken pos inc τs)
  weaken-lookup-helper zero pos inc (τ ∷ τs) = refl
  weaken-lookup-helper (suc ♯r) pos inc (τ ∷ τs) = weaken-lookup-helper ♯r pos inc τs

  weaken-register-helper : ∀ ♯r pos inc Γ →
                             weaken pos inc (lookup-regs ♯r Γ) ≡ lookup-regs ♯r (weaken pos inc Γ)
  weaken-register-helper ♯r pos inc (registerₐ sp regs) = weaken-lookup-helper ♯r pos inc regs

  subst-lookup-helper : ∀ {n} ♯r {pos i} {τs₁ τs₂ : Vec Type n} →
                          τs₁ ⟦ i / pos ⟧≡ τs₂ →
                          lookup ♯r τs₁ ⟦ i / pos ⟧≡ lookup ♯r τs₂
  subst-lookup-helper zero (sub-τ ∷ sub-τs) = sub-τ
  subst-lookup-helper (suc ♯r) (sub-τ ∷ sub-τs) = subst-lookup-helper ♯r sub-τs

  subst-register-helper : ∀ ♯r {pos i Γ₁ Γ₂} →
                            Γ₁ ⟦ i / pos ⟧≡ Γ₂ →
                            lookup-regs ♯r Γ₁ ⟦ i / pos ⟧≡ lookup-regs ♯r Γ₂
  subst-register-helper ♯r (subst-registerₐ sub-sp sub-regs) = subst-lookup-helper ♯r sub-regs

  subst-lookup-helper-many : ∀ {n} ♯r {pos is} {τs₁ τs₂ : Vec Type n} →
                               τs₁ ⟦ is / pos ⟧many≡ τs₂ →
                               lookup ♯r τs₁ ⟦ is / pos ⟧many≡ lookup ♯r τs₂
  subst-lookup-helper-many ♯r [] = []
  subst-lookup-helper-many ♯r (sub-τs ∷ subs-τs) = subst-lookup-helper ♯r sub-τs ∷ subst-lookup-helper-many ♯r subs-τs

  subst-register-helper-many : ∀ ♯r {pos is Γ₁ Γ₂} →
                                 Γ₁ ⟦ is / pos ⟧many≡ Γ₂ →
                                 lookup-regs ♯r Γ₁ ⟦ is / pos ⟧many≡ lookup-regs ♯r Γ₂
  subst-register-helper-many ♯r [] = []
  subst-register-helper-many ♯r (subst-registerₐ sub-sp sub-regs ∷ subs-Γ) = subst-lookup-helper ♯r sub-regs ∷ subst-register-helper-many ♯r subs-Γ

  is-length : ∀ {Δ₁ Δ₂ is} →
                Δ₁ ⊢ is of Δ₂ instantiations →
                length is ≡ length Δ₂
  is-length [] = refl
  is-length (i⋆ ∷ is⋆) = cong suc (is-length is⋆)

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

mutual
  subst-weaken-insideᵗ : ∀ A {{S : Substitution A}} → Set
  subst-weaken-insideᵗ A =
    ∀ pos₁ pos₂ inc {v₁ v₂ : A} {i} →
      v₁ ⟦ i / pos₁ ⟧≡ v₂ →
      weaken (suc (pos₁ + pos₂)) inc v₁ ⟦ weaken pos₂ inc i / pos₁ ⟧≡ weaken (pos₁ + pos₂) inc v₂

  τ-subst-weaken-inside : subst-weaken-insideᵗ Type
  τ-subst-weaken-inside pos₁ pos₂ inc {α⁼ zero} (subst-α-> ())
  τ-subst-weaken-inside pos₁ pos₂ inc {α⁼ (suc ι)} .{α⁼ ι} (subst-α-> (s≤s ι>pos₁))
    with suc (pos₁ + pos₂) ≤? suc ι | pos₁ + pos₂ ≤? ι
  ... | yes 1+pos₁+pos₂≤1+ι | yes pos₁+pos₂≤ι
    rewrite +-comm inc (suc ι)
          | +-comm ι inc = subst-α-> (s≤s (NP.≤-steps inc ι>pos₁))
  τ-subst-weaken-inside pos₁ pos₂ inc {α⁼ (suc ι)} .{α⁼ ι} (subst-α-> (s≤s ι>pos₁))
      | yes (s≤s pos₁+pos₂≤ι) | no pos₁+pos₂≰ι
    with pos₁+pos₂≰ι pos₁+pos₂≤ι
  ... | ()
  τ-subst-weaken-inside pos₁ pos₂ inc {α⁼ (suc ι)} .{α⁼ ι} (subst-α-> (s≤s ι>pos₁))
      | no 1+pos₁+pos₂≰1+ι | yes pos₁+pos₂≤ι
    with 1+pos₁+pos₂≰1+ι (s≤s pos₁+pos₂≤ι)
  ... | ()
  τ-subst-weaken-inside pos₁ pos₂ inc {α⁼ (suc ι)} .{α⁼ ι} (subst-α-> (s≤s ι>pos₁))
      | no 1+pos₁+pos₂≰1+ι | no pos₁+pos₂≰ι = subst-α-> (s≤s ι>pos₁)
  τ-subst-weaken-inside pos₁ pos₂ inc {i = α τ} subst-α-≡
    with suc (pos₁ + pos₂) ≤? pos₁
  ... | yes 1+pos₁+pos₂≤pos₁
    with NP.1+n≰n (Nat-≤-trans (s≤s (NP.m≤m+n pos₁ pos₂)) 1+pos₁+pos₂≤pos₁)
  ... | ()
  τ-subst-weaken-inside pos₁ pos₂ inc {i = α τ} subst-α-≡
      | no 1+pos₁+pos₂≤?pos₁
      rewrite sym (weaken-exchange {pos₁ = pos₂} inc pos₁ z≤n τ)
      = subst-α-≡
  τ-subst-weaken-inside pos₁ pos₂ inc {α⁼ ι} .{α⁼ ι} (subst-α-< ι<pos₁)
    with suc (pos₁ + pos₂) ≤? ι | pos₁ + pos₂ ≤? ι
  τ-subst-weaken-inside pos₁ pos₂ inc {α⁼ ι} .{α⁼ ι} (subst-α-< ι<pos₁)
      | yes 1+pos₁+pos₂≤ι | _
    with NP.1+n≰n (Nat-≤-trans ι<pos₁ (Nat-≤-trans (NP.≤-step (NP.m≤m+n pos₁ pos₂)) 1+pos₁+pos₂≤ι))
  ... | ()
  τ-subst-weaken-inside pos₁ pos₂ inc {α⁼ ι} .{α⁼ ι} (subst-α-< ι<pos₁)
      | _ | yes pos₁+pos₂≤ι
    with NP.1+n≰n (Nat-≤-trans ι<pos₁ (Nat-≤-trans (NP.m≤m+n pos₁ pos₂) pos₁+pos₂≤ι))
  ... | ()
  τ-subst-weaken-inside pos₁ pos₂ inc {α⁼ ι} .{α⁼ ι} (subst-α-< ι<pos₁)
      | no 1+pos₁+pos₂≰ι | no pos₁+pos₂≰ι = subst-α-< ι<pos₁
  τ-subst-weaken-inside pos₁ pos₂ inc subst-int = subst-int
  τ-subst-weaken-inside pos₁ pos₂ inc subst-ns = subst-ns
  τ-subst-weaken-inside pos₁ pos₂ inc {∀[ Δ ] Γ} (subst-∀ sub-Γ)
    with Γ-subst-weaken-inside (length Δ + pos₁) pos₂ inc sub-Γ
  ... | sub-Γ'
    with begin
      suc (length Δ + (pos₁ + pos₂))
    ≡⟨ +-comm 1 (length Δ) ∥ (λ v → v + (pos₁ + pos₂)) ⟩
      (length Δ + 1) + (pos₁ + pos₂)
    ≡⟨ +-assoc (length Δ) 1 (pos₁ + pos₂) ⟩
      length Δ + suc (pos₁ + pos₂)
    ∎ where open Eq-Reasoning
  ... | eq
    rewrite +-assoc (length Δ) pos₁ pos₂ | eq
    = subst-∀ sub-Γ'
  τ-subst-weaken-inside pos₁ pos₂ inc (subst-tuple sub-τs⁻)
    = subst-tuple (τs⁻-subst-weaken-inside pos₁ pos₂ inc sub-τs⁻)

  τ⁻-subst-weaken-inside : subst-weaken-insideᵗ InitType
  τ⁻-subst-weaken-inside pos₁ pos₂ inc (subst-τ⁻ sub-τ)
    = subst-τ⁻ (τ-subst-weaken-inside pos₁ pos₂ inc sub-τ)

  τs⁻-subst-weaken-inside : subst-weaken-insideᵗ (List InitType)
  τs⁻-subst-weaken-inside pos₁ pos₂ inc [] = []
  τs⁻-subst-weaken-inside pos₁ pos₂ inc (sub-τ⁻ ∷ sub-τs⁻)
    = τ⁻-subst-weaken-inside pos₁ pos₂ inc sub-τ⁻ ∷
      τs⁻-subst-weaken-inside pos₁ pos₂ inc sub-τs⁻

  σ-subst-weaken-inside : subst-weaken-insideᵗ StackType
  σ-subst-weaken-inside pos₁ pos₂ inc {ρ⁼ zero} (subst-ρ-> ())
  σ-subst-weaken-inside pos₁ pos₂ inc {ρ⁼ (suc ι)} .{ρ⁼ ι} (subst-ρ-> (s≤s ι>pos₁))
    with suc (pos₁ + pos₂) ≤? suc ι | pos₁ + pos₂ ≤? ι
  ... | yes 1+pos₁+pos₂≤1+ι | yes pos₁+pos₂≤ι
    rewrite +-comm inc (suc ι)
          | +-comm ι inc = subst-ρ-> (s≤s (NP.≤-steps inc ι>pos₁))
  σ-subst-weaken-inside pos₁ pos₂ inc {ρ⁼ (suc ι)} .{ρ⁼ ι} (subst-ρ-> (s≤s ι>pos₁))
      | yes (s≤s pos₁+pos₂≤ι) | no pos₁+pos₂≰ι
    with pos₁+pos₂≰ι pos₁+pos₂≤ι
  ... | ()
  σ-subst-weaken-inside pos₁ pos₂ inc {ρ⁼ (suc ι)} .{ρ⁼ ι} (subst-ρ-> (s≤s ι>pos₁))
      | no 1+pos₁+pos₂≰1+ι | yes pos₁+pos₂≤ι
    with 1+pos₁+pos₂≰1+ι (s≤s pos₁+pos₂≤ι)
  ... | ()
  σ-subst-weaken-inside pos₁ pos₂ inc {ρ⁼ (suc ι)} .{ρ⁼ ι} (subst-ρ-> (s≤s ι>pos₁))
      | no 1+pos₁+pos₂≰1+ι | no pos₁+pos₂≰ι = subst-ρ-> (s≤s ι>pos₁)
  σ-subst-weaken-inside pos₁ pos₂ inc {i = ρ σ} subst-ρ-≡
    with suc (pos₁ + pos₂) ≤? pos₁
  ... | yes 1+pos₁+pos₂≤pos₁
    with NP.1+n≰n (Nat-≤-trans (s≤s (NP.m≤m+n pos₁ pos₂)) 1+pos₁+pos₂≤pos₁)
  ... | ()
  σ-subst-weaken-inside pos₁ pos₂ inc {i = ρ σ} subst-ρ-≡
      | no 1+pos₁+pos₂≤?pos₁
      rewrite sym (weaken-exchange {pos₁ = pos₂} inc pos₁ z≤n σ)
      = subst-ρ-≡
  σ-subst-weaken-inside pos₁ pos₂ inc {ρ⁼ ι} .{ρ⁼ ι} (subst-ρ-< ι<pos₁)
    with suc (pos₁ + pos₂) ≤? ι | pos₁ + pos₂ ≤? ι
  σ-subst-weaken-inside pos₁ pos₂ inc {ρ⁼ ι} .{ρ⁼ ι} (subst-ρ-< ι<pos₁)
      | yes 1+pos₁+pos₂≤ι | _
    with NP.1+n≰n (Nat-≤-trans ι<pos₁ (Nat-≤-trans (NP.≤-step (NP.m≤m+n pos₁ pos₂)) 1+pos₁+pos₂≤ι))
  ... | ()
  σ-subst-weaken-inside pos₁ pos₂ inc {ρ⁼ ι} .{ρ⁼ ι} (subst-ρ-< ι<pos₁)
      | _ | yes pos₁+pos₂≤ι
    with NP.1+n≰n (Nat-≤-trans ι<pos₁ (Nat-≤-trans (NP.m≤m+n pos₁ pos₂) pos₁+pos₂≤ι))
  ... | ()
  σ-subst-weaken-inside pos₁ pos₂ inc {ρ⁼ ι} .{ρ⁼ ι} (subst-ρ-< ι<pos₁)
      | no 1+pos₁+pos₂≰ι | no pos₁+pos₂≰ι = subst-ρ-< ι<pos₁
  σ-subst-weaken-inside pos₁ pos₂ inc [] = []
  σ-subst-weaken-inside pos₁ pos₂ inc (sub-τ ∷ sub-τs)
    = τ-subst-weaken-inside pos₁ pos₂ inc sub-τ ∷
      σ-subst-weaken-inside pos₁ pos₂ inc sub-τs

  Γ-subst-weaken-inside : subst-weaken-insideᵗ RegisterAssignment
  Γ-subst-weaken-inside pos₁ pos₂ inc (subst-registerₐ sub-sp sub-regs)
    = subst-registerₐ (σ-subst-weaken-inside pos₁ pos₂ inc sub-sp)
                      (regs-subst-weaken-inside pos₁ pos₂ inc sub-regs)

  regs-subst-weaken-inside : ∀ {n} → subst-weaken-insideᵗ (Vec Type n)
  regs-subst-weaken-inside pos₁ pos₂ inc [] = []
  regs-subst-weaken-inside pos₁ pos₂ inc (sub-τ ∷ sub-τs)
    = τ-subst-weaken-inside pos₁ pos₂ inc sub-τ ∷
      regs-subst-weaken-inside pos₁ pos₂ inc sub-τs

Γ-subst-weaken-inside-many : ∀ pos₁ pos₂ inc {Γ₁ Γ₂ : RegisterAssignment} {is} →
                               Γ₁ ⟦ is / pos₁ ⟧many≡ Γ₂ →
                               weaken (length is + pos₁ + pos₂) inc Γ₁ ⟦ weaken pos₂ inc is / pos₁ ⟧many≡ weaken (pos₁ + pos₂) inc Γ₂
Γ-subst-weaken-inside-many pos₁ pos₂ inc [] = []
Γ-subst-weaken-inside-many pos₁ pos₂ inc {is = i ∷ is} (sub-Γ ∷ subs-Γ)
  with Γ-subst-weaken-inside pos₁ (length is + pos₂) inc sub-Γ
... | sub-Γ'
  with begin
    pos₁ + (length is + pos₂)
  ⟨ +-assoc pos₁ (length is) pos₂ ⟩≡
    (pos₁ + length is) + pos₂
  ≡⟨ +-comm pos₁ (length is) ∥ (λ v → v + pos₂) ⟩
    (length is + pos₁) + pos₂
  ∎ where open Eq-Reasoning
... | eq
  rewrite eq
  = sub-Γ' ∷ Γ-subst-weaken-inside-many pos₁ pos₂ inc subs-Γ

i-weaken : ∀ Δ₁ Δ₂ Δ₃ {i a} →
             Δ₁ ++ Δ₃ ⊢ i of a instantiation →
             Δ₁ ++ Δ₂ ++ Δ₃ ⊢ weaken (length Δ₁) (length Δ₂) i of a instantiation
i-weaken Δ₁ Δ₂ Δ₃ (of-α τ⋆) = of-α (valid-weaken Δ₁ Δ₂ Δ₃ τ⋆)
i-weaken Δ₁ Δ₂ Δ₃ (of-ρ σ⋆) = of-ρ (valid-weaken Δ₁ Δ₂ Δ₃ σ⋆)

is-weaken : ∀ Δ₁ Δ₂ Δ₃ {is Δ} →
              Δ₁ ++ Δ₃ ⊢ is of Δ instantiations →
              Δ₁ ++ Δ₂ ++ Δ₃ ⊢ weaken (length Δ₁) (length Δ₂) is of Δ instantiations
is-weaken Δ₁ Δ₂ Δ₃ [] = []
is-weaken Δ₁ Δ₂ Δ₃ {Δ = a ∷ Δ} (i⋆ ∷ is⋆)
  rewrite sym (List-++-assoc Δ Δ₁ Δ₃)
  with i-weaken (Δ ++ Δ₁) Δ₂ Δ₃ i⋆
... | i⋆'
  rewrite List-++-assoc Δ Δ₁ (Δ₂ ++ Δ₃)
        | is-length is⋆
        | List-length-++ Δ {Δ₁}
  = i⋆' ∷ is-weaken Δ₁ Δ₂ Δ₃ is⋆

vval-weaken : ∀ {ψ₁} →
                [] ⊢ ψ₁ Valid →
                ∀ Δ₁ Δ₂ Δ₃ →
                ∀ {Γ v τ} →
                ψ₁ , Δ₁ ++ Δ₃ , Γ ⊢ v of τ vval →
                ψ₁ , Δ₁ ++ Δ₂ ++ Δ₃ , weaken (length Δ₁) (length Δ₂) Γ ⊢ weaken (length Δ₁) (length Δ₂) v of weaken (length Δ₁) (length Δ₂) τ vval
vval-weaken ψ₁⋆ Δ₁ Δ₂ Δ₃ {Γ} {reg ♯r} of-reg
  rewrite weaken-register-helper ♯r (length Δ₁) (length Δ₂) Γ = of-reg
vval-weaken {ψ₁} ψ₁⋆  Δ₁ Δ₂ Δ₃ {v = globval lab} (of-globval l)
  with weaken-empty-ctx (length Δ₁) (length Δ₂) (All-lookup l ψ₁⋆)
... | eq = of-globval (subst (λ τ → ψ₁ ↓ lab ⇒ τ) (sym eq) l)
vval-weaken ψ₁⋆ Δ₁ Δ₂ Δ₃ of-int = of-int
vval-weaken ψ₁⋆ Δ₁ Δ₂ Δ₃ of-ns = of-ns
vval-weaken ψ₁⋆ Δ₁ Δ₂ Δ₃ (of-Λ {Δ₁ = Δᵢ} {Δ₂ = Δₒ} {Γ₁ = Γᵢ} v⋆ is⋆ subs-Γ)
  rewrite sym (List-++-assoc Δₒ Δ₁ Δ₃)
  with is-weaken (Δₒ ++ Δ₁) Δ₂ Δ₃ is⋆
... | is⋆'
  rewrite List-length-++ Δₒ {Δ₁}
        | List-++-assoc Δₒ Δ₁ (Δ₂ ++ Δ₃)
  with Γ-subst-weaken-inside-many 0 (length Δₒ + length Δ₁) (length Δ₂) subs-Γ
... | subs-Γ'
  rewrite is-length is⋆
  with
    begin
      length Δᵢ + (length Δₒ + length Δ₁)
    ⟨ +-assoc (length Δᵢ) (length Δₒ) (length Δ₁) ⟩≡
      (length Δᵢ + length Δₒ) + length Δ₁
    ≡⟨ +-comm (length Δᵢ) (length Δₒ) ∥ (λ v → v + length Δ₁) ⟩
      (length Δₒ + length Δᵢ) + length Δ₁
    ≡⟨ +-assoc (length Δₒ) (length Δᵢ) (length Δ₁) ⟩
      length Δₒ + (length Δᵢ + length Δ₁)
    ∎ where open Eq-Reasoning
... | eq
  rewrite +-comm (length Δᵢ) 0
        | eq
        | sym (weaken-exchange (length Δ₂) (length Δₒ) (NP.m≤m+n (length Δᵢ) (length Δ₁)) Γᵢ)
  = of-Λ (vval-weaken ψ₁⋆ Δ₁ Δ₂ Δ₃ v⋆) is⋆' subs-Γ'

i-subst : ∀ Δ₁ Δ₂ →
            ∀ {i a} →
            Δ₂ ⊢ i of a instantiation →
            ∀ {i₁ aᵥ} →
            Δ₁ ++ a ∷ Δ₂ ⊢ i₁ of aᵥ instantiation →
            ∃ λ i₂ →
              i₁ ⟦ i / length Δ₁ ⟧≡ i₂ ×
              Δ₁ ++ Δ₂ ⊢ i₂ of aᵥ instantiation
i-subst Δ₁ Δ₂ i⋆ (of-α τ⋆)
  with valid-subst-exists Δ₁ {Δ₂} i⋆ τ⋆
... | τ' , sub-τ , τ'⋆
  = α τ' , subst-α sub-τ , of-α τ'⋆
i-subst Δ₁ Δ₂ i⋆ (of-ρ σ⋆)
  with valid-subst-exists Δ₁ {Δ₂} i⋆ σ⋆
... | σ' , sub-σ , σ'⋆
  = ρ σ' , subst-ρ sub-σ , of-ρ σ'⋆

is-subst : ∀ Δ₁ Δ₂ →
             ∀ {i a} →
             Δ₂ ⊢ i of a instantiation →
             ∀ {is₁ Δ} →
             Δ₁ ++ a ∷ Δ₂ ⊢ is₁ of Δ instantiations →
             ∃ λ is₂ →
               is₁ ⟦ i / length Δ₁ ⟧≡ is₂ ×
               Δ₁ ++ Δ₂ ⊢ is₂ of Δ instantiations
is-subst Δ₁ Δ₂ i⋆ [] = [] , [] , []
is-subst Δ₁ Δ₂ {a = aᵥ} i⋆ {Δ = a ∷ Δ} (i₁⋆ ∷ is₁⋆)
  rewrite sym (List-++-assoc Δ Δ₁ (aᵥ ∷ Δ₂))
  with i-subst (Δ ++ Δ₁) Δ₂ i⋆ i₁⋆
... | i₂ , sub-i , i₂⋆
  with is-subst Δ₁ Δ₂ i⋆ is₁⋆
... | is₂ , sub-is , is₂⋆
  rewrite List-length-++ Δ {Δ₁}
        | sym (is-length is₁⋆)
        | List-++-assoc Δ Δ₁ Δ₂
  = i₂ ∷ is₂ , sub-i ∷ sub-is , i₂⋆ ∷ is₂⋆

vval-subst : ∀ {ψ₁} Δ₁ Δ₂ {i a Γ₁ Γ₂ v₁ τ₁} →
               [] ⊢ ψ₁ Valid →
               Δ₂ ⊢ i of a instantiation →
               Γ₁ ⟦ i / length Δ₁ ⟧≡ Γ₂ →
               ψ₁ , Δ₁ ++ a ∷ Δ₂ , Γ₁ ⊢ v₁ of τ₁ vval →
               ∃₂ λ v₂ τ₂ →
                 v₁ ⟦ i / length Δ₁ ⟧≡ v₂ ×
                 τ₁ ⟦ i / length Δ₁ ⟧≡ τ₂ ×
                 ψ₁ , Δ₁ ++ Δ₂ , Γ₂ ⊢ v₂ of τ₂ vval
vval-subst Δ₁ Δ₂ {v₁ = reg ♯r}  ψ₁⋆ i⋆ sub-Γ of-reg
  = _ , _ , subst-reg , subst-register-helper ♯r sub-Γ , of-reg
vval-subst Δ₁ Δ₂ ψ₁⋆ i⋆ sub-Γ (of-globval l)
  = _ , _ , subst-globval , subst-outside-ctx (All-lookup l ψ₁⋆)  , of-globval l
vval-subst Δ₁ Δ₂ ψ₁⋆ i⋆ sub-Γ of-int
  = _ , _ , subst-int , subst-int , of-int
vval-subst Δ₁ Δ₂ ψ₁⋆ i⋆ sub-Γ of-ns
  = _ , _ , subst-ns , subst-ns , of-ns
vval-subst Δ₁ Δ₂ {a = a} {v₁ = Λ Δₒ ∙ v₁ ⟦ is₁ ⟧}  ψ₁⋆ i⋆ sub-Γ (of-Λ {Δ₁ = Δᵢ} .{Δ₂ = Δₒ} {Γ₁ = Γᵢ₁} {Γ₂ = Γₒ₁} v₁⋆ is₁⋆ subs₁-Γ)
  rewrite sym (List-++-assoc Δₒ Δ₁ (a ∷ Δ₂))
  with is-subst (Δₒ ++ Δ₁) Δ₂ i⋆ {is₁} {Δᵢ} is₁⋆
... | is₂ , sub-is , is₂⋆
  rewrite List-length-++ Δₒ {Δ₁}
        | List-++-assoc Δₒ Δ₁ Δ₂
  with vval-subst Δ₁ Δ₂ ψ₁⋆ i⋆ sub-Γ v₁⋆
... | v₂ , ∀[ .Δᵢ ] Γᵢ₂ , sub-v , subst-∀ sub-Γᵢ , v₂⋆
  with weaken-subst (length Δₒ) (NP.m≤m+n (length Δᵢ) (length Δ₁)) sub-Γᵢ
... | sub-Γₘ
  with begin
    (length Δᵢ + length Δ₁) + length Δₒ
  ≡⟨ +-assoc (length Δᵢ) (length Δ₁) (length Δₒ) ⟩
    length Δᵢ + (length Δ₁ + length Δₒ)
  ≡⟨ +-comm (length Δ₁) (length Δₒ) ∥ (λ v → length Δᵢ + v) ⟩
    length Δᵢ + (length Δₒ + length Δ₁)
  ⟨ is-length is₁⋆ ∥ (λ v → v + (length Δₒ + length Δ₁)) ⟩≡
    length is₁ + (length Δₒ + length Δ₁)
  ∎ where open Eq-Reasoning
... | eq
  rewrite eq
  with subst-subst-many sub-is sub-Γₘ subs₁-Γ
... | Γₒ₂ , sub-Γₒ , subs₂-Γ
  = Λ Δₒ ∙ v₂ ⟦ is₂ ⟧ , ∀[ Δₒ ] Γₒ₂ , subst-Λ sub-v sub-is , subst-∀ sub-Γₒ , of-Λ v₂⋆ is₂⋆ subs₂-Γ
