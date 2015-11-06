module TermSubtyping where

open import Util
open import Judgments
open import Lemmas

uninit-of : ∀ {ψ₁ ψ₂ τs} →
              [] ⊢ τs Valid →
              ψ₁ , ψ₂ ⊢ tuple (map uninit τs) of tuple (map (λ τ → τ , uninit) τs) hval
uninit-of {ψ₁} {ψ₂} τs⋆ = of-tuple (help τs⋆)
  where help : ∀ {τs} →
                 All (λ τ → [] ⊢ τ Valid) τs →
                 AllZip (λ w τ⁻ → ψ₁ , ψ₂ , [] ⊢ w of τ⁻ wval⁰) (map uninit τs) (map (λ τ → τ , uninit) τs)
        help [] = []
        help (τ⋆ ∷ τs⋆) = of-uninit τ⋆ ∷ help τs⋆

foo : ∀ {Δ} {τs : List Type} →
        All (λ τ → Δ ⊢ τ Valid) τs →
        All (λ τ⁻ → Δ ⊢ τ⁻ Valid) (map (λ τ → τ , uninit) τs)
foo [] = []
foo (τ⋆ ∷ τs⋆) = valid-τ⁻ τ⋆ ∷ foo τs⋆

bar : ∀ {τs⁻₁ τs⁻₁' τs⁻₂ ι τ₁ φ₁} →
        [] ⊢ τs⁻₂ ≤ τs⁻₁ →
        τs⁻₁ ↓ ι ⇒ τ₁ , φ₁ →
        τs⁻₁ ⟦ ι ⟧← τ₁ , init ⇒ τs⁻₁' →
        ∃₂ λ τs⁻₂' τ₂ →
          τs⁻₂ ⟦ ι ⟧← τ₂ , init ⇒ τs⁻₂' ×
          [] ⊢ τs⁻₂' ≤ τs⁻₁'
bar ((τ⁻-≤ τ⋆ φ₁≤φ₂) ∷ τs⁻₂≤τs⁻₁) here here = _ , _ , here , τ⁻-≤ τ⋆ φ-≤-init ∷ τs⁻₂≤τs⁻₁
bar {τ⁻₁ ∷ τs⁻₁} {.τ⁻₁ ∷ τs⁻₁'} {τ⁻₂ ∷ τs⁻₂} (τ⁻₂≤τ⁻₂ ∷ τs⁻₂≤τs⁻₁) (there l) (there u)
  with bar τs⁻₂≤τs⁻₁ l u
... | τs⁻₂' , τ₂ , up , τs⁻₂'≤τs⁻₁' = τ⁻₂ ∷ τs⁻₂' , τ₂ , there up , τ⁻₂≤τ⁻₂ ∷ τs⁻₂'≤τs⁻₁'


mutual
  hvals-++ : ∀ {ψ₁ ψ₂ ψ₂⁺ hs τs} →
              AllZip (λ h τ → ψ₁ , ψ₂ ⊢ h of τ hval) hs τs →
              AllZip (λ h τ → ψ₁ , ψ₂ ++ ψ₂⁺ ⊢ h of τ hval) hs τs
  hvals-++ [] = []
  hvals-++ (h⋆ ∷ hs⋆) = hval-++ h⋆ ∷ hvals-++ hs⋆

  hval-++ : ∀ {ψ₁ ψ₂ ψ₂⁺ h τ} →
              ψ₁ , ψ₂ ⊢ h of τ hval →
              ψ₁ , ψ₂ ++ ψ₂⁺ ⊢ h of τ hval
  hval-++ (of-tuple ws⋆) = of-tuple (wvals⁰-++ ws⋆)

  wvals⁰-++ : ∀ {ψ₁ ψ₂ ψ₂⁺ ws τs⁻} →
                AllZip (λ h τ⁻ → ψ₁ , ψ₂ , [] ⊢ h of τ⁻ wval⁰) ws τs⁻ →
                AllZip (λ h τ⁻ → ψ₁ , ψ₂ ++ ψ₂⁺ , [] ⊢ h of τ⁻ wval⁰) ws τs⁻
  wvals⁰-++ [] = []
  wvals⁰-++ (w⋆ ∷ ws⋆) = wval⁰-++ w⋆ ∷ wvals⁰-++ ws⋆

  wval⁰-++ : ∀ {ψ₁ ψ₂ ψ₂⁺ Δ w τ⁻} →
               ψ₁ , ψ₂ , Δ ⊢ w of τ⁻ wval⁰ →
               ψ₁ , ψ₂ ++ ψ₂⁺ , Δ ⊢ w of τ⁻ wval⁰
  wval⁰-++ (of-uninit τs⋆) = of-uninit τs⋆
  wval⁰-++ (of-init w⋆) = of-init (wval-++ w⋆)

  wval-++ : ∀ {ψ₁ ψ₂ ψ₂⁺ Δ w τ} →
              ψ₁ , ψ₂ , Δ ⊢ w of τ wval →
              ψ₁ , ψ₂ ++ ψ₂⁺ , Δ ⊢ w of τ wval
  wval-++ (of-globval l τ₁≤τ₂ eq) = of-globval l τ₁≤τ₂ eq
  wval-++ {ψ₂⁺ = ψ₂⁺} (of-heapval l τ₁≤τ₂) = of-heapval (↓-add-right ψ₂⁺ l) τ₁≤τ₂
  wval-++ of-int = of-int
  wval-++ of-ns = of-ns
  wval-++ (of-inst w⋆ c⋆ run-Δ sub-Γ Γ₁≤Γ₂) = of-inst (wval-++ w⋆) c⋆ run-Δ sub-Γ Γ₁≤Γ₂

  stack-++ : ∀ {ψ₁ ψ₂ ψ₂⁺ sp σ} →
               ψ₁ , ψ₂ ⊢ sp of σ stack →
               ψ₁ , ψ₂ ++ ψ₂⁺ ⊢ sp of σ stack
  stack-++ [] = []
  stack-++ (w⋆ ∷ ws⋆) = wval-++ w⋆ ∷ stack-++ ws⋆

  regs-++ : ∀ {ψ₁ ψ₂ ψ₂⁺ m ws} {τs : Vec Type m} →
              AllZipᵥ (λ w τ → ψ₁ , ψ₂ , [] ⊢ w of τ wval) ws τs →
              AllZipᵥ (λ w τ → ψ₁ , ψ₂ ++ ψ₂⁺ , [] ⊢ w of τ wval) ws τs
  regs-++ [] = []
  regs-++ (w⋆ ∷ ws⋆) = wval-++ w⋆ ∷ regs-++ ws⋆

mutual
  hval-subtype : ∀ {ψ₁ ψ₂ h τ₁ τ₂} →
                   ψ₁ , ψ₂ ⊢ h of τ₁ hval →
                   [] ⊢ τ₁ ≤ τ₂ →
                   ψ₁ , ψ₂ ⊢ h of τ₂ hval
  hval-subtype (of-tuple ws⋆) (tuple-≤ τs⁻₁≤τs⁻₂) = of-tuple (wvals⁰-subtype ws⋆ τs⁻₁≤τs⁻₂)

  wval⁰-subtype : ∀ {ψ₁ ψ₂ w τ⁻₁ τ⁻₂} →
                    ψ₁ , ψ₂ ⊢ w of τ⁻₁ wval⁰ →
                    [] ⊢ τ⁻₁ ≤ τ⁻₂ →
                    ψ₁ , ψ₂ ⊢ w of τ⁻₂ wval⁰
  wval⁰-subtype (of-uninit τs⋆) (τ⁻-≤ τ⋆ φ-≤-uninit) = of-uninit τ⋆
  wval⁰-subtype (of-init w⋆) (τ⁻-≤ τ⋆ τ₁≤τ₂) = of-init w⋆

  wvals⁰-subtype : ∀ {ψ₁ ψ₂ ws τs⁻₁ τs⁻₂} →
                    AllZip (λ w τ⁻₁ → ψ₁ , ψ₂ ⊢ w of τ⁻₁ wval⁰) ws τs⁻₁ →
                    [] ⊢ τs⁻₁ ≤ τs⁻₂ →
                    AllZip (λ w τ⁻₂ → ψ₁ , ψ₂ ⊢ w of τ⁻₂ wval⁰) ws τs⁻₂
  wvals⁰-subtype [] [] = []
  wvals⁰-subtype (w⋆ ∷ ws⋆) (τ⁻₁≤τ⁻₂ ∷ τs⁻₁≤τs⁻₂) = wval⁰-subtype w⋆ τ⁻₁≤τ⁻₂ ∷ wvals⁰-subtype ws⋆ τs⁻₁≤τs⁻₂

  wval-subtype : ∀ {ψ₁ ψ₂ Δ w τ₁ τ₂} →
                   ψ₁ , ψ₂ , Δ ⊢ w of τ₁ wval →
                   Δ ⊢ τ₁ ≤ τ₂ →
                   ψ₁ , ψ₂ , Δ ⊢ w of τ₂ wval
  wval-subtype (of-globval l τ≤τ₁ eq) τ₁≤τ₂ = of-globval l (≤-trans τ≤τ₁ (≤-change₁ τ₁≤τ₂ (proj₂ (≤-valid τ≤τ₁)))) eq
  wval-subtype (of-heapval l τ≤τ₁) τ₁≤τ₂ = of-heapval l (≤-trans τ≤τ₁ (≤-change₁ τ₁≤τ₂ (proj₂ (≤-valid τ≤τ₁))))
  wval-subtype of-int int-≤ = of-int
  wval-subtype of-ns ns-≤ = of-ns
  wval-subtype (of-inst w⋆ c⋆ run-Δ sub-Γ Γ₁≤Γ₂) (∀-≤ Δ⋆ Γ₂≤Γ₃) = of-inst w⋆ c⋆ run-Δ sub-Γ (≤-trans Γ₁≤Γ₂ (≤-change₁ Γ₂≤Γ₃ (proj₂ (≤-valid Γ₁≤Γ₂))))

  vval-subtype : ∀ {ψ₁ Δ Γ v τ₁ τ₂} →
                   ψ₁ , Δ , Γ ⊢ v of τ₁ vval →
                   Δ ⊢ τ₁ ≤ τ₂ →
                   ψ₁ , Δ , Γ ⊢ v of τ₂ vval
  vval-subtype (of-reg τ≤τ₁) τ₁≤τ₂ = of-reg (≤-trans τ≤τ₁ τ₁≤τ₂)
  vval-subtype (of-word w⋆) τ₁≤τ₂ = of-word (wval-subtype w⋆ τ₁≤τ₂)
  vval-subtype (of-inst v⋆ c⋆ run-Δ sub-Γ Γ₁≤Γ₂) (∀-≤ Δ⋆ Γ₂≤Γ₃) = of-inst v⋆ c⋆ run-Δ sub-Γ (≤-trans Γ₁≤Γ₂ (≤-change₁ Γ₂≤Γ₃ (proj₂ (≤-valid Γ₁≤Γ₂))))

  vval-subtype₁ : ∀ {ψ₁ Δ Γ₁ Γ₂ v τ} →
                    ψ₁ , Δ , Γ₁ ⊢ v of τ vval →
                    Δ ⊢ Γ₂ ≤ Γ₁ →
                    ψ₁ , Δ , Γ₂ ⊢ v of τ vval
  vval-subtype₁ (of-reg {♯r = ♯r} reg≤τ) (Γ-≤ sp₂≤sp₁ regs₂≤regs₁) =
    of-reg (≤-trans (allzipᵥ-lookup ♯r regs₂≤regs₁) reg≤τ)
  vval-subtype₁ (of-word w⋆) Γ₂≤Γ₁ = of-word w⋆
  vval-subtype₁ (of-inst v⋆ c⋆ run-Δ sub-Γ Γ≤Γ₂) Γ₂≤Γ₁ = of-inst (vval-subtype₁ v⋆ Γ₂≤Γ₁) c⋆ run-Δ sub-Γ Γ≤Γ₂

Δ-valid-combine : ∀ {Δ₁ Δ₂ Δ₃} →
                    Δ₁ ⊢ Δ₂ Valid →
                    Δ₂ ++ Δ₁ ⊢ Δ₃ Valid →
                    Δ₁ ⊢ Δ₃ ++ Δ₂ Valid
Δ-valid-combine Δ₂⋆ [] = Δ₂⋆
Δ-valid-combine {Δ₁} {Δ₂} {a ∷ Δ₃} Δ₂⋆ (a⋆ ∷ Δ₃⋆) rewrite sym (List-++-assoc Δ₃ Δ₂ Δ₁) = a⋆ ∷ Δ-valid-combine Δ₂⋆ Δ₃⋆

run-valid : ∀ {Δ₁ Δ₂ Δ c} →
              Δ₁ ++ Δ ⊢ c Valid →
              Δ ⊢ Δ₁ Valid →
              Run Δ₁ ⟦ c ⟧≡ Δ₂ →
              Δ ⊢ Δ₂ Valid
run-valid (valid-zero (valid-inst i⋆)) (a⋆ ∷ Δ₁⋆) (run-inst m) = Δ₁⋆
run-valid (valid-zero (valid-weaken Δ⁺⋆)) Δ₁⋆ run-weaken = Δ-valid-combine Δ₁⋆ Δ⁺⋆
run-valid (valid-suc c⋆) (a⋆ ∷ Δ₁⋆) (run-suc sub-a run-Δ) = subst-valid c⋆ (run-append run-Δ) a⋆ sub-a ∷ run-valid c⋆ Δ₁⋆ run-Δ

wval-valid-type : ∀ {ψ₁ ψ₂ Δ w τ} →
                    ψ₁ , ψ₂ , Δ ⊢ w of τ wval →
                    Δ ⊢ τ Valid
wval-valid-type (of-globval l τ₁≤τ₂ eq) = valid-++ (proj₂ (≤-valid τ₁≤τ₂))
wval-valid-type (of-heapval l τ₁≤τ₂) = valid-++ (proj₂ (≤-valid τ₁≤τ₂))
wval-valid-type of-int = valid-int
wval-valid-type of-ns = valid-ns
wval-valid-type (of-inst w⋆ c⋆ run-Δ sub-Γ Γ₂≤Γ₃)
  with wval-valid-type w⋆
... | valid-∀ Δ₁⋆ Γ₁⋆ = valid-∀ (run-valid c⋆ Δ₁⋆ run-Δ) (proj₂ (≤-valid Γ₂≤Γ₃))

wval⁰-valid-type : ∀ {ψ₁ ψ₂ Δ w τ⁻} →
                     ψ₁ , ψ₂ , Δ ⊢ w of τ⁻ wval⁰ →
                     Δ ⊢ τ⁻ Valid
wval⁰-valid-type (of-uninit τ⋆) = valid-τ⁻ (valid-++ τ⋆)
wval⁰-valid-type (of-init w⋆) = valid-τ⁻ (wval-valid-type w⋆)

wvals⁰-valid-type : ∀ {ψ₁ ψ₂ Δ ws τs⁻} →
                      AllZip (λ w τ⁻ → ψ₁ , ψ₂ , Δ ⊢ w of τ⁻ wval⁰) ws τs⁻ →
                      Δ ⊢ τs⁻ Valid
wvals⁰-valid-type [] = []
wvals⁰-valid-type (w⋆ ∷ ws⋆) = wval⁰-valid-type w⋆ ∷ wvals⁰-valid-type ws⋆

vval-valid-type : ∀ {ψ₁ Δ Γ v τ} →
                    [] ⊢ ψ₁ Valid →
                    Δ ⊢ Γ Valid →
                    ψ₁ , Δ , Γ ⊢ v of τ vval →
                    Δ ⊢ τ Valid
vval-valid-type ψ₁⋆ Γ⋆ (of-reg r⋆) = proj₂ (≤-valid r⋆)
vval-valid-type ψ₁⋆ Γ⋆ (of-word w⋆) = wval-valid-type w⋆
vval-valid-type ψ₁⋆ Γ⋆ (of-inst v⋆ c⋆ run-Δ sub-Γ Γ₂≤Γ₃)
  with vval-valid-type ψ₁⋆ Γ⋆ v⋆
... | valid-∀ Δ₁⋆ Γ₁⋆ = valid-∀ (run-valid c⋆ Δ₁⋆ run-Δ) (proj₂ (≤-valid Γ₂≤Γ₃))


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

gval-valid-type : ∀ {ψ₁ g τ} →
                    ψ₁ ⊢ g of τ gval →
                    [] ⊢ τ Valid
gval-valid-type (of-gval {Δ = Δ} Δ⋆ Γ⋆ I⋆) = valid-∀ Δ⋆ (subst₂ _⊢_Valid (sym (List-++-right-identity Δ)) refl Γ⋆)

gvals-valid-type : ∀ {ψ₁ gs τs} →
                     AllZip (λ g τ → ψ₁ ⊢ g of τ gval) gs τs →
                     [] ⊢ τs Valid
gvals-valid-type [] = []
gvals-valid-type (g⋆ ∷ gs⋆) = gval-valid-type g⋆ ∷ gvals-valid-type gs⋆

globals-valid-type : ∀ {ψ₁ G} →
                       ⊢ G of ψ₁ globals →
                       [] ⊢ ψ₁ Valid
globals-valid-type (of-globals gs⋆) = gvals-valid-type gs⋆

≤int⇒≡int : ∀ {Δ} {τ : Type} →
          Δ ⊢ τ ≤ int →
          τ ≡ int
≤int⇒≡int int-≤ = refl

≤tuple⇒≡tuple : ∀ {Δ} {τ : Type} {τs⁻} →
                  Δ ⊢ τ ≤ tuple τs⁻ →
                  ∃ λ τs⁻' →
                    τ ≡ tuple τs⁻'
≤tuple⇒≡tuple (tuple-≤ τs⁻≤τs⁻') = _ , refl

regs-update-≤ : ∀ {Δ m τ₁ τ₂} ♯r {τs₁ τs₂ : Vec Type m} →
                  Δ ⊢ τs₁ ≤ τs₂ →
                  Δ ⊢ τ₁ ≤ τ₂ →
                  Δ ⊢ update ♯r τ₁ τs₁ ≤ update ♯r τ₂ τs₂
regs-update-≤ zero (τ₁'≤τ₂' ∷ τs₁≤τs₂) τ₁≤τ₂ = τ₁≤τ₂ ∷ τs₁≤τs₂
regs-update-≤ (suc ♯r) (τ₁'≤τ₂' ∷ τs₁≤τs₂) τ₁≤τ₂ = τ₁'≤τ₂' ∷ regs-update-≤ ♯r τs₁≤τs₂ τ₁≤τ₂

stack-lookup₁-≤ : ∀ {Δ sp₁ sp₂ i τ₁} →
                    Δ ⊢ sp₁ ≤ sp₂ →
                    stack-lookup i sp₁ τ₁ →
                    ∃ λ τ₂ →
                      Δ ⊢ τ₁ ≤ τ₂ ×
                      stack-lookup i sp₂ τ₂
stack-lookup₁-≤ (τ₁≤τ₂ ∷ sp₁≤sp₂) here = _ , τ₁≤τ₂ , here
stack-lookup₁-≤ (τ₁≤τ₂ ∷ sp₁≤sp₂) (there l)
  with stack-lookup₁-≤ sp₁≤sp₂ l
... | τ₂' , τ₁≤τ₂' , l' = τ₂' , τ₁≤τ₂' , there l'

stack-lookup₂-≤ : ∀ {Δ sp₁ sp₂ i τ₂} →
                    Δ ⊢ sp₁ ≤ sp₂ →
                    stack-lookup i sp₂ τ₂ →
                    ∃ λ τ₁ →
                      Δ ⊢ τ₁ ≤ τ₂ ×
                      stack-lookup i sp₁ τ₁
stack-lookup₂-≤ (τ₁≤τ₂ ∷ sp₁≤sp₂) here = _ , τ₁≤τ₂ , here
stack-lookup₂-≤ (τ₁≤τ₂ ∷ sp₁≤sp₂) (there l)
  with stack-lookup₂-≤ sp₁≤sp₂ l
... | τ₂' , τ₁≤τ₂' , l' = τ₂' , τ₁≤τ₂' , there l'

stack-update-≤ : ∀ {Δ sp₁ sp₂ sp₂' i τ₁ τ₂} →
                    Δ ⊢ sp₁ ≤ sp₂ →
                    Δ ⊢ τ₁ ≤ τ₂ →
                    stack-update i τ₂ sp₂ sp₂' →
                    ∃ λ sp₁' →
                      Δ ⊢ sp₁' ≤ sp₂' ×
                      stack-update i τ₁ sp₁ sp₁'
stack-update-≤ (τ₁≤τ₂' ∷ sp₁≤sp₂) τ₁≤τ₂ here = _ , τ₁≤τ₂ ∷ sp₁≤sp₂ , here
stack-update-≤ (τ₁≤τ₂' ∷ sp₁≤sp₂) τ₁≤τ₂ (there up)
  with stack-update-≤ sp₁≤sp₂ τ₁≤τ₂ up
... | sp₁' , sp₁'≤sp₂' , up' = _ , τ₁≤τ₂' ∷ sp₁'≤sp₂' , there up'

instruction-subtype : ∀ {ψ₁ Δ Γ₁ Γ₁' Γ₂ ι} →
                        [] ⊢ ψ₁ Valid →
                        Δ ⊢ Γ₂ ≤ Γ₁ →
                        ψ₁ , Δ , Γ₁ ⊢ ι ⇒ Γ₁' instruction →
                        ∃ λ Γ₂' →
                          ψ₁ , Δ , Γ₂ ⊢ ι ⇒ Γ₂' instruction ×
                          Δ ⊢ Γ₂' ≤ Γ₁'
instruction-subtype {ι = add ♯rd ♯rs v} ψ₁⋆
                    (Γ-≤ sp₂≤sp₁ regs₂≤regs₁) (of-add eq v⋆)
  with vval-subtype₁ v⋆ (Γ-≤ sp₂≤sp₁ regs₂≤regs₁) | allzipᵥ-lookup ♯rs regs₂≤regs₁
... | v⋆' | ♯rs⋆ rewrite eq =
  _ , of-add (≤int⇒≡int ♯rs⋆) v⋆' ,
      Γ-≤ sp₂≤sp₁ (regs-update-≤ ♯rd regs₂≤regs₁ int-≤)
instruction-subtype {ι = sub ♯rd ♯rs v} ψ₁⋆
                    (Γ-≤ sp₂≤sp₁ regs₂≤regs₁) (of-sub eq v⋆)
  with vval-subtype₁ v⋆ (Γ-≤ sp₂≤sp₁ regs₂≤regs₁) | allzipᵥ-lookup ♯rs regs₂≤regs₁
... | v⋆' | ♯rs⋆ rewrite eq =
  _ , of-sub (≤int⇒≡int ♯rs⋆) v⋆' ,
      Γ-≤ sp₂≤sp₁ (regs-update-≤ ♯rd regs₂≤regs₁ int-≤)
instruction-subtype {ι = push v} ψ₁⋆
                    (Γ-≤ sp₂≤sp₁ regs₂≤regs₁) (of-push v⋆)
  with vval-subtype₁ v⋆ (Γ-≤ sp₂≤sp₁ regs₂≤regs₁)
... | v⋆' = _ , of-push v⋆' , Γ-≤ (≤-refl (vval-valid-type ψ₁⋆ (proj₂ (≤-valid (Γ-≤ sp₂≤sp₁ regs₂≤regs₁))) v⋆) ∷ sp₂≤sp₁) regs₂≤regs₁
instruction-subtype {ι = pop} ψ₁⋆
                    (Γ-≤ (τ₂≤τ₁ ∷ sp₂≤sp₁) regs₂≤regs₁) of-pop = _ , of-pop , Γ-≤ sp₂≤sp₁ regs₂≤regs₁
instruction-subtype {ι = sld ♯rd i} ψ₁⋆
                    (Γ-≤ sp₂≤sp₁ regs₂≤regs₁) (of-sld l)
  with stack-lookup₂-≤ sp₂≤sp₁ l
... | τ₂ , τ₂≤τ₁ , l' = _ , of-sld l' , Γ-≤ sp₂≤sp₁ (regs-update-≤ ♯rd regs₂≤regs₁ τ₂≤τ₁)
instruction-subtype {ι = sst i ♯rs} ψ₁⋆
                    (Γ-≤ sp₂≤sp₁ regs₂≤regs₁) (of-sst up)
  with stack-update-≤ sp₂≤sp₁ (allzipᵥ-lookup ♯rs regs₂≤regs₁) up
... | sp₂' , sp₂'≤sp₁' , up' = _ , of-sst up' , Γ-≤ sp₂'≤sp₁' regs₂≤regs₁
instruction-subtype {ι = ld ♯rd ♯rs i} ψ₁⋆
                    (Γ-≤ sp₂≤sp₁ regs₂≤regs₁) (of-ld eq l)
  with allzipᵥ-lookup ♯rs regs₂≤regs₁
... | ♯rs⋆ rewrite eq with ≤tuple⇒≡tuple ♯rs⋆
... | τs⁻ , eq₁ rewrite eq₁ with ♯rs⋆
... | tuple-≤ τs₂≤τs₁ with allzip-lookup₂ l τs₂≤τs₁
... | (τ₂ , init) , l' , τ⁻-≤ τ₂⋆ φ-≤-init = _ , of-ld eq₁ l' , Γ-≤ sp₂≤sp₁ (regs-update-≤ ♯rd regs₂≤regs₁ (≤-refl τ₂⋆))
instruction-subtype {Γ₁ = registerₐ sp₁ regs₁}
                    {Γ₁' = registerₐ .sp₁ .(update ♯rd (tuple τs⁻₁') regs₁)}
                    {Γ₂ = registerₐ sp₂ regs₂}
                    {ι = st ♯rd i ♯rs} ψ₁⋆
                    (Γ-≤ sp₂≤sp₁ regs₂≤regs₁) (of-st {τs⁻ = τs⁻₁} {τs⁻₁'} {τ₁} {φ₁} eq lookup≤τ l₁ up₁)
  with allzipᵥ-lookup ♯rd regs₂≤regs₁ | allzipᵥ-lookup ♯rs regs₂≤regs₁
... | ♯rd⋆ | ♯rs⋆
  rewrite eq with ≤tuple⇒≡tuple ♯rd⋆
... | τs⁻₂ , eq₁
  rewrite eq₁ with ♯rd⋆
... | tuple-≤ τs⁻₂≤τs⁻₁
  with allzip-lookup₂ l₁ τs⁻₂≤τs⁻₁
... | (.τ₁ , φ₂) , l₂ , τ⁻-≤ τ₁⋆ φ₂≤φ₁
  with <-to-← τs⁻₂ (τ₁ , init) {i} (subst (λ len → i < len) (sym (AllZip-length τs⁻₂≤τs⁻₁)) (←-to-< up₁))
... | τs⁻₂' , up₂
  =
  registerₐ sp₂ (update ♯rd (tuple τs⁻₂') regs₂) , of-st {τs⁻ = τs⁻₂} {φ = φ₂} eq₁ (≤-trans ♯rs⋆ lookup≤τ) l₂ up₂ , Γ-≤ sp₂≤sp₁ (regs-update-≤ ♯rd regs₂≤regs₁ (tuple-≤ (allzip-update up₂ up₁ (τ⁻-≤ τ₁⋆ φ-≤-init) τs⁻₂≤τs⁻₁)))
instruction-subtype {ι = malloc ♯rd τs} ψ₁⋆
                    (Γ-≤ sp₂≤sp₁ regs₂≤regs₁) (of-malloc τs⋆) =
  _ , of-malloc τs⋆ , Γ-≤ sp₂≤sp₁ (regs-update-≤ ♯rd regs₂≤regs₁ (≤-refl (valid-tuple (help τs⋆))))
    where help : ∀ {Δ} {τs : List Type} →
                   All (λ τ → Δ ⊢ τ Valid) τs →
                   All (λ τ⁻ → Δ ⊢ τ⁻ Valid) (map (λ τ → τ , uninit) τs)
          help [] = []
          help (τ⋆ ∷ τs⋆) = valid-τ⁻ τ⋆ ∷ help τs⋆
instruction-subtype {ι = mov ♯rd v} ψ₁⋆
                    (Γ-≤ sp₂≤sp₁ regs₂≤regs₁) (of-mov v⋆)
  with vval-subtype₁ v⋆ (Γ-≤ sp₂≤sp₁ regs₂≤regs₁)
... | v⋆' = _ , of-mov v⋆' , Γ-≤ sp₂≤sp₁ (regs-update-≤ ♯rd regs₂≤regs₁ (≤-refl (vval-valid-type ψ₁⋆ (proj₁ (≤-valid (Γ-≤ sp₂≤sp₁ regs₂≤regs₁))) v⋆')))
instruction-subtype {ι = beq ♯r v} ψ₁⋆
                    (Γ-≤ sp₂≤sp₁ regs₂≤regs₁) (of-beq eq Γ₁≤Γ' v⋆)
  with allzipᵥ-lookup ♯r regs₂≤regs₁
... | ♯r⋆ rewrite eq
  = _ , of-beq (≤int⇒≡int ♯r⋆) (≤-trans (Γ-≤ sp₂≤sp₁ regs₂≤regs₁) Γ₁≤Γ') (vval-subtype₁ v⋆ (Γ-≤ sp₂≤sp₁ regs₂≤regs₁)) , Γ-≤ sp₂≤sp₁ regs₂≤regs₁

instructionsequence-subtype : ∀ {ψ₁ Δ Γ₁ Γ₂ I} →
                                [] ⊢ ψ₁ Valid →
                                Δ ⊢ Γ₂ ≤ Γ₁ →
                                ψ₁ , Δ , Γ₁ ⊢ I instructionsequence →
                                ψ₁ , Δ , Γ₂ ⊢ I instructionsequence
instructionsequence-subtype ψ₁⋆ Γ₂≤Γ₁ (of-~> ι⋆ I⋆)
  with instruction-subtype ψ₁⋆ Γ₂≤Γ₁ ι⋆
... | Γ₂' , ι⋆' , Γ₂'≤Γ₁'
  with instructionsequence-subtype ψ₁⋆ Γ₂'≤Γ₁' I⋆
... | I⋆' = of-~> ι⋆' I⋆'
instructionsequence-subtype ψ₁⋆ Γ₂≤Γ₁ (of-jmp {Γ' = registerₐ sp' regs'} Γ₁≤Γ' v⋆) = of-jmp (≤-trans Γ₂≤Γ₁ Γ₁≤Γ') (vval-subtype₁ v⋆ Γ₂≤Γ₁)
