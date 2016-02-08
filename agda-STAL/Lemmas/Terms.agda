module Lemmas.Terms where

open import Util
open import Judgments
open import Lemmas.Equality
open import Lemmas.Types
open import Lemmas.Substitution
open import Lemmas.TypeSubstitution
import Data.Nat.Properties as NP
open HighGrammar

private
  weaken-lookup : ∀ {n} ♯r pos inc (τs : Vec Type n) →
                        weaken pos inc (lookup ♯r τs) ≡ lookup ♯r (weaken pos inc τs)
  weaken-lookup zero pos inc (τ ∷ τs) = refl
  weaken-lookup (suc ♯r) pos inc (τ ∷ τs) = weaken-lookup ♯r pos inc τs

  weaken-lookup-regs : ∀ ♯r pos inc Γ →
                         weaken pos inc (lookup-regs ♯r Γ) ≡ lookup-regs ♯r (weaken pos inc Γ)
  weaken-lookup-regs ♯r pos inc (registerₐ sp regs) = weaken-lookup ♯r pos inc regs

  weaken-update : ∀ {n} ♯r pos inc τ (τs : Vec Type n) →
                    weaken pos inc (update ♯r τ τs) ≡ update ♯r (weaken pos inc τ) (weaken pos inc τs)
  weaken-update zero pos inc τ (τ' ∷ τs) = refl
  weaken-update (suc ♯r) pos inc τ (τ' ∷ τs) = cong₂ _∷_ refl (weaken-update ♯r pos inc τ τs)

  weaken-update-regs : ∀ ♯r pos inc τ Γ →
                         weaken pos inc (update-regs ♯r τ Γ) ≡ update-regs ♯r (weaken pos inc τ) (weaken pos inc Γ)
  weaken-update-regs ♯r pos inc τ (registerₐ sp regs) = cong₂ registerₐ refl (weaken-update ♯r pos inc τ regs)

  weaken-stack-append-ns : ∀ n pos inc σ →
                             weaken pos inc (stack-append (replicate n ns) σ) ≡ stack-append (replicate n ns) (weaken pos inc σ)
  weaken-stack-append-ns zero pos inc σ = refl
  weaken-stack-append-ns (suc n) pos inc σ = cong (_∷_ ns) (weaken-stack-append-ns n pos inc σ)

  weaken-stack-drop : ∀ {n} pos inc {σ₁ σ₂} →
                         stack-drop n σ₁ σ₂ →
                         stack-drop n (weaken pos inc σ₁) (weaken pos inc σ₂)
  weaken-stack-drop pos inc here = here
  weaken-stack-drop pos inc (there drop) = there (weaken-stack-drop pos inc drop)

  weaken-stack-lookup : ∀ {n} pos inc {σ τ} →
                          stack-lookup n σ τ →
                          stack-lookup n (weaken pos inc σ) (weaken pos inc τ)
  weaken-stack-lookup pos inc here = here
  weaken-stack-lookup pos inc (there drop) = there (weaken-stack-lookup pos inc drop)

  weaken-stack-update : ∀ {n} pos inc {τ σ σ'} →
                          stack-update n τ σ σ' →
                          stack-update n (weaken pos inc τ) (weaken pos inc σ) (weaken pos inc σ')
  weaken-stack-update pos inc here = here
  weaken-stack-update pos inc (there drop) = there (weaken-stack-update pos inc drop)

  weaken-maps-uninit : ∀ pos inc τs →
                         weaken pos inc (map (λ τ → τ , uninit) τs) ≡
                         map (λ τ → τ , uninit) (weaken pos inc τs)
  weaken-maps-uninit pos inc [] = refl
  weaken-maps-uninit pos inc (τ ∷ τs) = cong₂ _∷_ refl (weaken-maps-uninit pos inc τs)

  weaken-↓ : ∀ {i} pos inc {τs⁻ : List InitType} {τ⁻} →
               τs⁻ ↓ i ⇒ τ⁻ →
               weaken pos inc τs⁻ ↓ i ⇒ weaken pos inc τ⁻
  weaken-↓ pos inc here = here
  weaken-↓ pos inc (there l) = there (weaken-↓ pos inc l)

  weaken-← : ∀ {i} pos inc {τs⁻ τs⁻' : List InitType} {τ⁻} →
               τs⁻ ⟦ i ⟧← τ⁻ ⇒ τs⁻' →
               weaken pos inc τs⁻ ⟦ i ⟧← weaken pos inc τ⁻ ⇒ weaken pos inc τs⁻'
  weaken-← pos inc here = here
  weaken-← pos inc (there l) = there (weaken-← pos inc l)

  subst-lookup : ∀ {n} ♯r {pos θ} {τs₁ τs₂ : Vec Type n} →
                       τs₁ ⟦ θ / pos ⟧≡ τs₂ →
                       lookup ♯r τs₁ ⟦ θ / pos ⟧≡ lookup ♯r τs₂
  subst-lookup zero (sub-τ ∷ sub-τs) = sub-τ
  subst-lookup (suc ♯r) (sub-τ ∷ sub-τs) = subst-lookup ♯r sub-τs

  subst-lookup-regs : ∀ ♯r {pos θ Γ₁ Γ₂} →
                        Γ₁ ⟦ θ / pos ⟧≡ Γ₂ →
                        lookup-regs ♯r Γ₁ ⟦ θ / pos ⟧≡ lookup-regs ♯r Γ₂
  subst-lookup-regs ♯r (subst-registerₐ sub-sp sub-regs) = subst-lookup ♯r sub-regs

  subst-lookup-regs-helper : ∀ {♯r pos θ Γ₁ Γ₂ τ₁ τ₂} →
                        Γ₁ ⟦ θ / pos ⟧≡ Γ₂ →
                        τ₁ ⟦ θ / pos ⟧≡ τ₂ →
                        lookup-regs ♯r Γ₁ ≡ τ₁ →
                        lookup-regs ♯r Γ₂ ≡ τ₂
  subst-lookup-regs-helper {♯r} sub-Γ sub-τ refl
    = subst-unique (subst-lookup-regs ♯r sub-Γ) sub-τ

  subst-lookup-many : ∀ {n} ♯r {pos θs} {τs₁ τs₂ : Vec Type n} →
                            τs₁ ⟦ θs / pos ⟧many≡ τs₂ →
                            lookup ♯r τs₁ ⟦ θs / pos ⟧many≡ lookup ♯r τs₂
  subst-lookup-many ♯r [] = []
  subst-lookup-many ♯r (sub-τs ∷ subs-τs) = subst-lookup ♯r sub-τs ∷ subst-lookup-many ♯r subs-τs

  subst-lookup-regs-many : ∀ ♯r {pos θs Γ₁ Γ₂} →
                             Γ₁ ⟦ θs / pos ⟧many≡ Γ₂ →
                             lookup-regs ♯r Γ₁ ⟦ θs / pos ⟧many≡ lookup-regs ♯r Γ₂
  subst-lookup-regs-many ♯r [] = []
  subst-lookup-regs-many ♯r (subst-registerₐ sub-sp sub-regs ∷ subs-Γ) = subst-lookup ♯r sub-regs ∷ subst-lookup-regs-many ♯r subs-Γ

  subst-update : ∀ {n} ♯r {pos θ τ₁ τ₂} {τs₁ τs₂ : Vec Type n} →
                       τ₁ ⟦ θ / pos ⟧≡ τ₂ →
                       τs₁ ⟦ θ / pos ⟧≡ τs₂ →
                       update ♯r τ₁ τs₁ ⟦ θ / pos ⟧≡ update ♯r τ₂ τs₂
  subst-update zero sub-τ (sub-τ' ∷ sub-τs) = sub-τ ∷ sub-τs
  subst-update (suc ♯r) sub-τ (sub-τ' ∷ sub-τs) = sub-τ' ∷ subst-update ♯r sub-τ sub-τs

  subst-update-regs : ∀ ♯r {pos θ τ₁ τ₂ Γ₁ Γ₂} →
                        τ₁ ⟦ θ / pos ⟧≡ τ₂ →
                        Γ₁ ⟦ θ / pos ⟧≡ Γ₂ →
                        update-regs ♯r τ₁ Γ₁ ⟦ θ / pos ⟧≡ update-regs ♯r τ₂ Γ₂
  subst-update-regs ♯r sub-τ (subst-registerₐ sub-sp sub-regs) = subst-registerₐ sub-sp (subst-update ♯r sub-τ sub-regs)

  subst-map-uninit : ∀ {θ pos} {τs τs' : List Type} →
                       τs ⟦ θ / pos ⟧≡ τs' →
                       map (λ τ → τ , uninit) τs ⟦ θ / pos ⟧≡ map (λ τ → τ , uninit) τs'
  subst-map-uninit [] = []
  subst-map-uninit (sub-τ ∷ sub-τs) = subst-τ⁻ sub-τ ∷ subst-map-uninit sub-τs

  subst-stack-append-ns : ∀ n {pos θ σ σ'} →
                            σ ⟦ θ / pos ⟧≡ σ' →
                            stack-append (replicate n ns) σ ⟦ θ / pos ⟧≡ stack-append (replicate n ns) σ'
  subst-stack-append-ns zero sub-σ = sub-σ
  subst-stack-append-ns (suc n) sub-σ = subst-ns ∷ subst-stack-append-ns n sub-σ

  subst-stack-drop : ∀ {n pos θ σ₁ σ₁' σ₂} →
                       stack-drop n σ₁ σ₁' →
                       σ₁ ⟦ θ / pos ⟧≡ σ₂ →
                       ∃ λ σ₂' →
                         stack-drop n σ₂ σ₂' ×
                         σ₁' ⟦ θ / pos ⟧≡ σ₂'
  subst-stack-drop here sub-σ = _ , here , sub-σ
  subst-stack-drop (there drop) (sub-τ ∷ sub-σ)
    with subst-stack-drop drop sub-σ
  ... | _ , drop' , sub-σ'
    = _ , there drop' , sub-σ'

  subst-stack-lookup : ∀ {n θ pos σ σ' τ} →
                          stack-lookup n σ τ →
                          σ ⟦ θ / pos ⟧≡ σ' →
                          ∃ λ τ' →
                            stack-lookup n σ' τ' ×
                            τ ⟦ θ / pos ⟧≡ τ'
  subst-stack-lookup here (sub-τ ∷ sub-σ) = _ , here , sub-τ
  subst-stack-lookup (there l) (sub-τ ∷ sub-σ)
    with subst-stack-lookup l sub-σ
  ... | τ' , l' , sub-τ'
    = τ' , there l' , sub-τ'

  subst-stack-update : ∀ {n θ pos σ₁ σ₁' σ₂ τ₁ τ₂} →
                          stack-update n τ₁ σ₁ σ₁' →
                          τ₁ ⟦ θ / pos ⟧≡ τ₂ →
                          σ₁ ⟦ θ / pos ⟧≡ σ₂ →
                          ∃ λ σ₂' →
                            stack-update n τ₂ σ₂ σ₂' ×
                            σ₁' ⟦ θ / pos ⟧≡ σ₂'
  subst-stack-update here sub-τ (sub-τ' ∷ sub-σ) = _ , here , sub-τ ∷ sub-σ
  subst-stack-update (there up) sub-τ (sub-τ' ∷ sub-σ)
    with subst-stack-update up sub-τ sub-σ
  ... | σ₂' , up' , sub-σ'
    = _ , there up' , sub-τ' ∷ sub-σ'

  subst-↓ : ∀ {n θ pos τ⁻} {τs⁻ τs⁻' : List InitType} →
              τs⁻ ↓ n ⇒ τ⁻ →
              τs⁻ ⟦ θ / pos ⟧≡ τs⁻' →
              ∃ λ τ⁻' →
                τs⁻' ↓ n ⇒ τ⁻' ×
                τ⁻ ⟦ θ / pos ⟧≡ τ⁻'
  subst-↓ here (sub-τ ∷ sub-τs) = _ , here , sub-τ
  subst-↓ (there l) (sub-τ ∷ sub-τs)
    with subst-↓ l sub-τs
  ... | τ⁻' , l' , sub-τ'
    = _ , there l' , sub-τ'

  subst-← : ∀ {n θ pos τ⁻₁ τ⁻₂} {τs⁻₁ τs⁻₁' τs⁻₂ : List InitType} →
              τs⁻₁ ⟦ n ⟧← τ⁻₁ ⇒ τs⁻₁' →
              τ⁻₁ ⟦ θ / pos ⟧≡ τ⁻₂ →
              τs⁻₁ ⟦ θ / pos ⟧≡ τs⁻₂ →
              ∃ λ τs⁻₂' →
                τs⁻₂ ⟦ n ⟧← τ⁻₂ ⇒ τs⁻₂' ×
                τs⁻₁' ⟦ θ / pos ⟧≡ τs⁻₂'
  subst-← here sub-τ⁻ (sub-τ⁻' ∷ sub-τs⁻) = _ , here , sub-τ⁻ ∷ sub-τs⁻
  subst-← (there up) sub-τ⁻ (sub-τ⁻' ∷ sub-τs⁻)
    with subst-← up sub-τ⁻ sub-τs⁻
  ... | τ⁻' , up' , sub-τs⁻'
    = _ , there up' , sub-τ⁻' ∷ sub-τs⁻'

  subst-tuple-helper : ∀ {θ pos τs⁻} {τ : Type} →
                         tuple τs⁻ ⟦ θ / pos ⟧≡ τ →
                         ∃ λ τs⁻' →
                           τ ≡ tuple τs⁻' ×
                           τs⁻ ⟦ θ / pos ⟧≡ τs⁻'
  subst-tuple-helper (subst-tuple sub-τs⁻) = _ , refl , sub-τs⁻

  θs-length : ∀ {Δ₁ Δ₂ θs} →
                Δ₁ ⊢ θs of Δ₂ instantiations →
                length θs ≡ length Δ₂
  θs-length [] = refl
  θs-length (θ⋆ ∷ θs⋆) = cong suc (θs-length θs⋆)

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

wvals⁰-valid-type : ∀ {ψ₁ ψ₂ ws τs⁻} →
                      AllZip (λ w τ⁻ → ψ₁ , ψ₂ ⊢ w of τ⁻ wval⁰) ws τs⁻ →
                      [] ⊢ τs⁻ Valid
wvals⁰-valid-type [] = []
wvals⁰-valid-type (w⋆ ∷ ws⋆) = wval⁰-valid-type w⋆ ∷ wvals⁰-valid-type ws⋆

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
                    ψ₁ , Δ ⊢ v of Γ ⇒ τ vval →
                    Δ ⊢ τ Valid
vval-valid-type ψ₁⋆ (valid-registerₐ sp⋆ regs⋆) {reg ♯r} of-reg = Allᵥ-lookup ♯r regs⋆
vval-valid-type ψ₁⋆ Γ⋆ (of-globval l) = valid-++ (All-lookup l ψ₁⋆)
vval-valid-type ψ₁⋆ Γ⋆ of-int = valid-int
vval-valid-type ψ₁⋆ Γ⋆ (of-Λ {Δ = Δ} {Δ₁ = Δ₁} {Δ₂} v⋆ θs⋆ subs-Γ)
  with vval-valid-type ψ₁⋆ Γ⋆ v⋆
... | valid-∀ Γ⋆'
  with valid-weaken Δ₁ Δ₂ Δ Γ⋆'
... | Γ⋆''
  rewrite List-++-right-identity Δ
  with valid-subst-many [] {Δ₁} {Δ₂ ++ Δ} θs⋆ Γ⋆'' subs-Γ
... | Γ⋆'''
  = valid-∀ Γ⋆'''

θ-subst : ∀ Δ₁ Δ₂ →
            ∀ {θ a} →
            Δ₂ ⊢ θ of a instantiation →
            ∀ {θ₁ aᵥ} →
            Δ₁ ++ a ∷ Δ₂ ⊢ θ₁ of aᵥ instantiation →
            ∃ λ θ₂ →
              θ₁ ⟦ θ / length Δ₁ ⟧≡ θ₂ ×
              Δ₁ ++ Δ₂ ⊢ θ₂ of aᵥ instantiation
θ-subst Δ₁ Δ₂ θ⋆ (of-α τ⋆)
  with valid-subst-exists Δ₁ {Δ₂} θ⋆ τ⋆
... | τ' , sub-τ , τ'⋆
  = α τ' , subst-α sub-τ , of-α τ'⋆
θ-subst Δ₁ Δ₂ θ⋆ (of-ρ σ⋆)
  with valid-subst-exists Δ₁ {Δ₂} θ⋆ σ⋆
... | σ' , sub-σ , σ'⋆
  = ρ σ' , subst-ρ sub-σ , of-ρ σ'⋆

θs-subst : ∀ Δ₁ Δ₂ →
             ∀ {θ a} →
             Δ₂ ⊢ θ of a instantiation →
             ∀ {θs₁ Δ} →
             Δ₁ ++ a ∷ Δ₂ ⊢ θs₁ of Δ instantiations →
             ∃ λ θs₂ →
               θs₁ ⟦ θ / length Δ₁ ⟧≡ θs₂ ×
               Δ₁ ++ Δ₂ ⊢ θs₂ of Δ instantiations
θs-subst Δ₁ Δ₂ θ⋆ [] = [] , [] , []
θs-subst Δ₁ Δ₂ {a = aᵥ} θ⋆ {Δ = a ∷ Δ} (θ₁⋆ ∷ θs₁⋆)
  rewrite sym (List-++-assoc Δ Δ₁ (aᵥ ∷ Δ₂))
  with θ-subst (Δ ++ Δ₁) Δ₂ θ⋆ θ₁⋆
... | θ₂ , sub-θ , θ₂⋆
  with θs-subst Δ₁ Δ₂ θ⋆ θs₁⋆
... | θs₂ , sub-θs , θs₂⋆
  rewrite List-length-++ Δ {Δ₁}
        | sym (θs-length θs₁⋆)
        | List-++-assoc Δ Δ₁ Δ₂
  = θ₂ ∷ θs₂ , sub-θ ∷ sub-θs , θ₂⋆ ∷ θs₂⋆

vval-subst : ∀ {ψ₁} Δ₁ Δ₂ {θ a Γ₁ Γ₂ v₁ τ₁} →
               [] ⊢ ψ₁ Valid →
               Δ₂ ⊢ θ of a instantiation →
               Γ₁ ⟦ θ / length Δ₁ ⟧≡ Γ₂ →
               ψ₁ , Δ₁ ++ a ∷ Δ₂ ⊢ v₁ of Γ₁ ⇒ τ₁ vval →
               ∃₂ λ v₂ τ₂ →
                 v₁ ⟦ θ / length Δ₁ ⟧≡ v₂ ×
                 τ₁ ⟦ θ / length Δ₁ ⟧≡ τ₂ ×
                 ψ₁ , Δ₁ ++ Δ₂ ⊢ v₂ of Γ₂ ⇒ τ₂ vval
vval-subst Δ₁ Δ₂ {v₁ = reg ♯r} ψ₁⋆ θ⋆ sub-Γ of-reg
  = _ , _ , subst-reg , subst-lookup-regs ♯r sub-Γ , of-reg
vval-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-Γ (of-globval l)
  = _ , _ , subst-globval , subst-outside-ctx (All-lookup l ψ₁⋆) , of-globval l
vval-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-Γ of-int
  = _ , _ , subst-int , subst-int , of-int
vval-subst Δ₁ Δ₂ {a = a} {v₁ = Λ Δₒ ∙ v₁ ⟦ θs₁ ⟧} ψ₁⋆ θ⋆ sub-Γ (of-Λ {Δ₁ = Δᵢ} .{Δ₂ = Δₒ} {Γ₁ = Γᵢ₁} {Γ₂ = Γₒ₁} v₁⋆ θs₁⋆ subs₁-Γ)
  rewrite sym (List-++-assoc Δₒ Δ₁ (a ∷ Δ₂))
  with θs-subst (Δₒ ++ Δ₁) Δ₂ θ⋆ {θs₁} {Δᵢ} θs₁⋆
... | θs₂ , sub-θs , θs₂⋆
  rewrite List-length-++ Δₒ {Δ₁}
        | List-++-assoc Δₒ Δ₁ Δ₂
  with vval-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-Γ v₁⋆
... | v₂ , ∀[ .Δᵢ ] Γᵢ₂ , sub-v , subst-∀ sub-Γᵢ , v₂⋆
  with weaken-subst (length Δₒ) (NP.m≤m+n (length Δᵢ) (length Δ₁)) sub-Γᵢ
... | sub-Γₘ
  with begin
    (length Δᵢ + length Δ₁) + length Δₒ
  ≡⟨ +-assoc (length Δᵢ) (length Δ₁) (length Δₒ) ⟩
    length Δᵢ + (length Δ₁ + length Δₒ)
  ≡⟨ +-comm (length Δ₁) (length Δₒ) ∥ (λ v → length Δᵢ + v) ⟩
    length Δᵢ + (length Δₒ + length Δ₁)
  ⟨ θs-length θs₁⋆ ∥ (λ v → v + (length Δₒ + length Δ₁)) ⟩≡
    length θs₁ + (length Δₒ + length Δ₁)
  ∎ where open Eq-Reasoning
... | eq
  rewrite eq
  with subst-subst-many sub-θs sub-Γₘ subs₁-Γ
... | Γₒ₂ , sub-Γₒ , subs₂-Γ
  = Λ Δₒ ∙ v₂ ⟦ θs₂ ⟧ , ∀[ Δₒ ] Γₒ₂ , subst-Λ sub-v sub-θs , subst-∀ sub-Γₒ , of-Λ v₂⋆ θs₂⋆ subs₂-Γ

instruction-subst : ∀ {ψ₁} Δ₁ Δ₂ {θ a Γ₁ Γ₂} →
                      [] ⊢ ψ₁ Valid →
                      Δ₂ ⊢ θ of a instantiation →
                      Γ₁ ⟦ θ / length Δ₁ ⟧≡ Γ₂ →
                      ∀ {ι₁ Γᵣ₁} →
                      ψ₁ , Δ₁ ++ a ∷ Δ₂ ⊢ ι₁ of Γ₁ ⇒ Γᵣ₁ instruction →
                      ∃₂ λ ι₂ Γᵣ₂ →
                           ι₁ ⟦ θ / length Δ₁ ⟧≡ ι₂ ×
                           Γᵣ₁ ⟦ θ / length Δ₁ ⟧≡ Γᵣ₂ ×
                           ψ₁ , Δ₁ ++ Δ₂ ⊢ ι₂ of Γ₂ ⇒ Γᵣ₂ instruction
instruction-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-Γ {add ♯rd ♯rs v} (of-add eq v⋆)
  with vval-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-Γ v⋆
... | v' , int , sub-v , subst-int , v'⋆
  = _ , _ , subst-add sub-v , subst-update-regs ♯rd subst-int sub-Γ , of-add (subst-lookup-regs-helper sub-Γ subst-int eq) v'⋆
instruction-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-Γ {sub ♯rd ♯rs v} (of-sub eq v⋆)
  with vval-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-Γ v⋆
... | v' , int , sub-v , subst-int , v'⋆
  = _ , _ , subst-sub sub-v , subst-update-regs ♯rd subst-int sub-Γ , of-sub (subst-lookup-regs-helper sub-Γ subst-int eq) v'⋆
instruction-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ (subst-registerₐ sub-sp sub-regs) {salloc n} of-salloc
  = _ , _ , subst-salloc , subst-registerₐ (subst-stack-append-ns n sub-sp) sub-regs , of-salloc
instruction-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ (subst-registerₐ sub-sp sub-regs) {sfree n} (of-sfree drop)
  with subst-stack-drop drop sub-sp
... | _ , drop' , sub-sp'
  = _ , _ , subst-sfree , subst-registerₐ sub-sp' sub-regs , of-sfree drop'
instruction-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ (subst-registerₐ sub-sp sub-regs) {sld ♯rd i} (of-sld l)
  with subst-stack-lookup l sub-sp
... | τ' , l' , sub-τ
  = _ , _ , subst-sld , subst-update-regs ♯rd sub-τ (subst-registerₐ sub-sp sub-regs) , of-sld l'
instruction-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ (subst-registerₐ sub-sp sub-regs) {sst i ♯rs} (of-sst up)
  with subst-stack-update up (subst-lookup ♯rs sub-regs) sub-sp
... | sp' , up' , sub-sp'
  = _ , _ , subst-sst , subst-registerₐ sub-sp' sub-regs , of-sst up'
instruction-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-Γ {ld ♯rd ♯rs i} (of-ld eq l)
  with subst-lookup-regs ♯rs sub-Γ
... | sub-tuple
  rewrite eq
  with subst-tuple-helper sub-tuple
... | τs⁻' , eq' , sub-τs⁻
  with subst-↓ l sub-τs⁻
... | (τ' , init) , l' , subst-τ⁻ sub-τ
  = _ , _ , subst-ld , subst-update-regs ♯rd sub-τ sub-Γ , of-ld eq' l'
instruction-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-Γ {st ♯rd i ♯rs} (of-st eq lookup≤τ l up)
  with subst-lookup-regs ♯rd sub-Γ
... | sub-tuple
  rewrite eq
  with subst-tuple-helper sub-tuple
... | τs⁻₂ , eq' , sub-τs⁻
  with subtype-subst-exists Δ₁ θ⋆ lookup≤τ
... | lookup' , τ' , sub-lookup , sub-τ , lookup'≤τ'
  with subst-← up (subst-τ⁻ sub-τ) sub-τs⁻
... | τs⁻₂' , up' , sub-τs⁻'
  with subst-↓ l sub-τs⁻
... | (τ'' , φ) , l' , (subst-τ⁻ sub-τ')
  rewrite subst-unique sub-lookup (subst-lookup-regs ♯rs sub-Γ)
        | subst-unique sub-τ sub-τ'
  = _ , _ , subst-st , subst-update-regs ♯rd (subst-tuple sub-τs⁻') sub-Γ , of-st eq' lookup'≤τ' l' up'
instruction-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-Γ {malloc ♯rd τs} (of-malloc τs⋆)
  with valid-subst-exists Δ₁ θ⋆ τs⋆
... | τs' , sub-τs , τs'⋆
  = _ , _ , subst-malloc sub-τs , subst-update-regs ♯rd (subst-tuple (subst-map-uninit sub-τs)) sub-Γ , of-malloc τs'⋆
instruction-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-Γ {mov ♯rd v} (of-mov v⋆)
  with vval-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-Γ v⋆
... | v' , τ' , sub-v , sub-τ , v'⋆
  = _ , _ , subst-mov sub-v , subst-update-regs ♯rd sub-τ sub-Γ , of-mov v'⋆
instruction-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-Γ (of-beq eq v⋆ Γ≤Γ')
  with vval-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-Γ v⋆
... | v' , ∀[ [] ] Γ' , sub-v , subst-∀ sub-Γᵢ , v'⋆
  = _ , _ , subst-beq sub-v , sub-Γ , of-beq (subst-lookup-regs-helper sub-Γ subst-int eq) v'⋆ (subtype-subst Δ₁ θ⋆ Γ≤Γ' sub-Γ sub-Γᵢ)

instructionsequence-subst : ∀ {ψ₁} Δ₁ Δ₂ {θ a Γ₁ Γ₂} →
                              [] ⊢ ψ₁ Valid →
                              Δ₂ ⊢ θ of a instantiation →
                              Γ₁ ⟦ θ / length Δ₁ ⟧≡ Γ₂ →
                              ∀ {I₁} →
                              ψ₁ , Δ₁ ++ a ∷ Δ₂ ⊢ I₁ of Γ₁ instructionsequence →
                              ∃ λ I₂ →
                                 I₁ ⟦ θ / length Δ₁ ⟧≡ I₂ ×
                                 ψ₁ , Δ₁ ++ Δ₂ ⊢ I₂ of Γ₂ instructionsequence
instructionsequence-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-Γ (of-~> ι₁⋆ I₁⋆)
  with instruction-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-Γ ι₁⋆
... | ι₂ , Γₘ , sub-ι , sub-Γₘ , ι₂⋆
  with instructionsequence-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-Γₘ I₁⋆
... | I₂ , sub-I , I₂⋆
  = _ , subst-~> sub-ι sub-I , of-~> ι₂⋆ I₂⋆
instructionsequence-subst Δ₁ Δ₂ {Γ₁ = Γ₁} {Γ₂} ψ₁⋆ θ⋆ sub-Γ (of-jmp .{Γ = Γ₁} {Γ₁'} v₁⋆ Γ₁≤Γ₁')
  with vval-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-Γ v₁⋆
... | v₂ , ∀[ [] ] Γ₂' , sub-v , subst-∀ sub-Γ' , v₂⋆
  = _ , subst-jmp sub-v , of-jmp v₂⋆ (subtype-subst Δ₁ θ⋆ Γ₁≤Γ₁' sub-Γ sub-Γ')
instructionsequence-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-Γ of-halt = _ , subst-halt , of-halt


instructionsequence-subst-many : ∀ {ψ₁} Δ₁ Δ₂ Δ₃ {θs Γ₁ Γ₂} →
                                   [] ⊢ ψ₁ Valid →
                                   Δ₃ ⊢ θs of Δ₂ instantiations →
                                   Γ₁ ⟦ θs / length Δ₁ ⟧many≡ Γ₂ →
                                   ∀ {I₁} →
                                   ψ₁ , Δ₁ ++ Δ₂ ++ Δ₃ ⊢ I₁ of Γ₁ instructionsequence →
                                   ∃ λ I₂ →
                                       I₁ ⟦ θs / length Δ₁ ⟧many≡ I₂ ×
                                       ψ₁ , Δ₁ ++ Δ₃ ⊢ I₂ of Γ₂ instructionsequence
instructionsequence-subst-many Δ₁ [] Δ₃ ψ₁⋆ [] [] I₁⋆ = _ , [] , I₁⋆
instructionsequence-subst-many Δ₁ (a ∷ Δ₂) Δ₃ ψ₁⋆ (θ⋆ ∷ θs⋆) (sub-Γ ∷ subs-Γ) I₁⋆
  with instructionsequence-subst Δ₁ (Δ₂ ++ Δ₃) ψ₁⋆ θ⋆ sub-Γ I₁⋆
... | Iₘ , sub-I , Iₘ⋆
  with instructionsequence-subst-many Δ₁ Δ₂ Δ₃ ψ₁⋆ θs⋆ subs-Γ Iₘ⋆
... | I₂ , subs-I , I₂⋆
  = I₂ , sub-I ∷ subs-I , I₂⋆
