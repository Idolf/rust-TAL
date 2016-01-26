module TermSubtyping where

open import Util
open import Judgments
open import Lemmas

≤int⇒≡int : ∀ {Δ} {τ : Type} →
          Δ ⊢ τ ≤ int →
          τ ≡ int
≤int⇒≡int int-≤ = refl

≤tuple⇒≡tuple : ∀ {Δ} {τ : Type} {τs⁻} →
                  Δ ⊢ τ ≤ tuple τs⁻ →
                  ∃ λ τs⁻' →
                    τ ≡ tuple τs⁻'
≤tuple⇒≡tuple (tuple-≤ τs⁻≤τs⁻') = _ , refl

≤τ⁻⇒≡τ⁻ : ∀ {τ⁻₁ τ⁻₂ φ₁ φ₂ Δ} →
            Δ ⊢ (τ⁻₁ , φ₁) ≤ (τ⁻₂ , φ₂) →
            τ⁻₁ ≡ τ⁻₂
≤τ⁻⇒≡τ⁻ (τ⁻-≤ τ⋆ φ₁≤φ₂) = refl

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

instruction-valid-type : ∀ {ψ₁ Δ Γ₁ Γ₂ ι} →
                           [] ⊢ ψ₁ Valid →
                           Δ ⊢ Γ₁ Valid →
                           ψ₁ , Δ , Γ₁ ⊢ ι ⇒ Γ₂ instruction →
                           Δ ⊢ Γ₂ Valid
instruction-valid-type ψ₁⋆ (valid-registerₐ sp⋆ regs⋆) (of-add {♯rd = ♯rd} eq v⋆) = valid-registerₐ sp⋆ (Allᵥ-update ♯rd valid-int regs⋆)
instruction-valid-type ψ₁⋆ (valid-registerₐ sp⋆ regs⋆) (of-sub {♯rd = ♯rd} eq v⋆) = valid-registerₐ sp⋆ (Allᵥ-update ♯rd valid-int regs⋆)
instruction-valid-type ψ₁⋆ (valid-registerₐ sp⋆ regs⋆) (of-salloc {n = n}) = valid-registerₐ (stack-append-valid (replicate-valid n) sp⋆) regs⋆
  where replicate-valid : ∀ {Δ} n → Δ ⊢ replicate n ns Valid
        replicate-valid zero = []
        replicate-valid (suc n) = valid-ns ∷ replicate-valid n
instruction-valid-type ψ₁⋆ (valid-registerₐ sp⋆ regs⋆) (of-sfree drop) = valid-registerₐ (stack-drop-valid sp⋆ drop) regs⋆
instruction-valid-type ψ₁⋆ (valid-registerₐ sp⋆ regs⋆) (of-sld {♯rd = ♯rd} l) = valid-registerₐ sp⋆ (Allᵥ-update ♯rd (stack-lookup-valid sp⋆ l) regs⋆)
instruction-valid-type ψ₁⋆ (valid-registerₐ sp⋆ regs⋆) (of-sst {♯rs = ♯rs} up) = valid-registerₐ (stack-update-valid sp⋆ (Allᵥ-lookup ♯rs regs⋆) up) regs⋆
instruction-valid-type ψ₁⋆ (valid-registerₐ sp⋆ regs⋆) (of-ld {♯rd = ♯rd} {♯rs = ♯rs} eq l)
  with Allᵥ-lookup ♯rs regs⋆
... | lookup⋆ rewrite eq with lookup⋆
... | valid-tuple τs⁻⋆ with All-lookup l τs⁻⋆
... | valid-τ⁻ τ⋆ = valid-registerₐ sp⋆ (Allᵥ-update ♯rd τ⋆ regs⋆ )
instruction-valid-type ψ₁⋆ (valid-registerₐ sp⋆ regs⋆) (of-st {♯rd = ♯rd} eq lookup≤τ l up)
  with Allᵥ-lookup ♯rd regs⋆
... | lookup⋆
  rewrite eq
  with lookup⋆
... | valid-tuple τs⁻⋆
  = valid-registerₐ sp⋆ (Allᵥ-update ♯rd (valid-tuple (All-update (valid-τ⁻ (proj₂ (≤-valid lookup≤τ))) up τs⁻⋆)) regs⋆)
instruction-valid-type ψ₁⋆ (valid-registerₐ sp⋆ regs⋆) (of-malloc {♯rd = ♯rd} τs⋆) = valid-registerₐ sp⋆ (Allᵥ-update ♯rd (valid-tuple (help τs⋆)) regs⋆)
  where help : ∀ {Δ} {τs : List Type} →
                 All (λ τ → Δ ⊢ τ Valid) τs →
                 All (λ τ⁻ → Δ ⊢ τ⁻ Valid) (map (λ τ → τ , uninit) τs)
        help [] = []
        help (τ⋆ ∷ τs⋆) = valid-τ⁻ τ⋆ ∷ help τs⋆
instruction-valid-type ψ₁⋆ (valid-registerₐ sp⋆ regs⋆) (of-mov {♯rd = ♯rd} v⋆) = valid-registerₐ sp⋆ (Allᵥ-update ♯rd (vval-valid-type ψ₁⋆ (valid-registerₐ sp⋆ regs⋆) v⋆) regs⋆)
instruction-valid-type ψ₁⋆ (valid-registerₐ sp⋆ regs⋆) (of-beq eq v⋆ Γ≤Γ') = valid-registerₐ sp⋆ regs⋆

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

wval-subtype : ∀ {ψ₁ ψ₂ w τ₁ τ₂} →
                 ψ₁ , ψ₂ ⊢ w of τ₁ wval →
                 [] ⊢ τ₁ ≤ τ₂ →
                 ψ₁ , ψ₂ ⊢ w of τ₂ wval
wval-subtype (of-globval l τ≤τ₁) τ₁≤τ₂ = of-globval l (≤-trans τ≤τ₁ τ₁≤τ₂)
wval-subtype (of-heapval l τ≤τ₁) τ₁≤τ₂ = of-heapval l (≤-trans τ≤τ₁ τ₁≤τ₂)
wval-subtype of-int int-≤ = of-int
wval-subtype of-ns ns-≤ = of-ns
wval-subtype (of-Λ {Δ₂ = Δ₂} w⋆ is⋆ subs-Γ Γ₃≤Γ₂) (∀-≤ Γ₄≤Γ₃)
  rewrite List-++-right-identity Δ₂ = of-Λ w⋆ is⋆ subs-Γ (≤-trans Γ₄≤Γ₃ Γ₃≤Γ₂)

hval-subtype : ∀ {ψ₁ ψ₂ h τ₁ τ₂} →
                 ψ₁ , ψ₂ ⊢ h of τ₁ hval →
                 [] ⊢ τ₁ ≤ τ₂ →
                 ψ₁ , ψ₂ ⊢ h of τ₂ hval
hval-subtype (of-tuple ws⋆) (tuple-≤ τs⁻₁≤τs⁻₂) = of-tuple (wvals⁰-subtype ws⋆ τs⁻₁≤τs⁻₂)

vval-subtype : ∀ {ψ₁ Δ Γ₁ Γ₂} →
                 [] ⊢ ψ₁ Valid →
                 Δ ⊢ Γ₁ ≤ Γ₂ →
                 {v : SmallValue} {τ₂ : Type} →
                 ψ₁ , Δ , Γ₂ ⊢ v of τ₂ vval →
                 ∃ λ τ₁ →
                   Δ ⊢ τ₁ ≤ τ₂ ×
                   ψ₁ , Δ , Γ₁ ⊢ v of τ₁ vval
vval-subtype ψ₁⋆ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂) {reg ♯r} of-reg
  with allzipᵥ-lookup ♯r regs₁≤regs₂
... | lookup₁≤lookup₂ = _ , lookup₁≤lookup₂ , of-reg
vval-subtype ψ₁⋆ Γ₁≤Γ₂ (of-globval l) = _ , ≤-++ (≤-refl (All-lookup l ψ₁⋆)) , of-globval l
vval-subtype ψ₁⋆ Γ₁≤Γ₂ of-int = int , int-≤ , of-int
vval-subtype ψ₁⋆ Γ₁≤Γ₂ of-ns = ns , ns-≤ , of-ns
vval-subtype {Δ = Δ} ψ₁⋆ Γ₁≤Γ₂ {Λ Δₒ ∙ v ⟦ is ⟧} {∀[ .Δₒ ] Γₒ₁} (of-Λ {Δ₁ = Δᵢ} .{Δₒ} {Γᵢ₁} .{Γₒ₁} v⋆ is⋆ subs-Γ₁)
  with vval-subtype ψ₁⋆ Γ₁≤Γ₂ v⋆
... | ∀[ .Δᵢ ] Γᵢ₂ , ∀-≤ Γᵢ₁≤Γᵢ₂ , v⋆'
  with subtype-subst-exists-many {A = RegisterAssignment} [] is⋆ (subtype-weaken Δᵢ Δₒ Δ Γᵢ₁≤Γᵢ₂)
... | Γₒ₁' , Γₒ₂ , subs-Γ₁' , subs-Γ₂ , Γₒ₁'≤Γₒ₂
  rewrite subst-unique-many subs-Γ₁ subs-Γ₁' = ∀[ Δₒ ] Γₒ₂ , ∀-≤ Γₒ₁'≤Γₒ₂ , of-Λ v⋆' is⋆ subs-Γ₂

regs-update-≤ : ∀ {Δ m τ₁ τ₂} ♯r {τs₁ τs₂ : Vec Type m} →
                  Δ ⊢ τs₁ ≤ τs₂ →
                  Δ ⊢ τ₁ ≤ τ₂ →
                  Δ ⊢ update ♯r τ₁ τs₁ ≤ update ♯r τ₂ τs₂
regs-update-≤ zero (τ₁'≤τ₂' ∷ τs₁≤τs₂) τ₁≤τ₂ = τ₁≤τ₂ ∷ τs₁≤τs₂
regs-update-≤ (suc ♯r) (τ₁'≤τ₂' ∷ τs₁≤τs₂) τ₁≤τ₂ = τ₁'≤τ₂' ∷ regs-update-≤ ♯r τs₁≤τs₂ τ₁≤τ₂

instruction-subtype : ∀ {ψ₁ Δ Γ₁ Γ₂ Γ₂'} →
                        [] ⊢ ψ₁ Valid →
                        Δ ⊢ Γ₁ ≤ Γ₂ →
                        {ι : Instruction} →
                        ψ₁ , Δ , Γ₂ ⊢ ι ⇒ Γ₂' instruction →
                        ∃ λ Γ₁' →
                          ψ₁ , Δ , Γ₁ ⊢ ι ⇒ Γ₁' instruction ×
                          Δ ⊢ Γ₁' ≤ Γ₂'
instruction-subtype ψ₁⋆ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
                    {ι = add ♯rd ♯rs v} (of-add eq v⋆)
  with vval-subtype ψ₁⋆ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂) v⋆ | allzipᵥ-lookup ♯rs regs₁≤regs₂
... | τ , int≤τ , v⋆' | int≤lookup
  rewrite eq
        | ≤int⇒≡int int≤τ =
  _ , of-add (≤int⇒≡int int≤lookup) v⋆' ,
      Γ-≤ sp₁≤sp₂ (regs-update-≤ ♯rd regs₁≤regs₂ int-≤)
instruction-subtype ψ₁⋆ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
                    {ι = sub ♯rd ♯rs v} (of-sub eq v⋆)
  with vval-subtype ψ₁⋆ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂) v⋆ | allzipᵥ-lookup ♯rs regs₁≤regs₂
... | τ , int≤τ , v⋆' | int≤lookup
  rewrite eq
        | ≤int⇒≡int int≤τ =
  _ , of-sub (≤int⇒≡int int≤lookup) v⋆' ,
      Γ-≤ sp₁≤sp₂ (regs-update-≤ ♯rd regs₁≤regs₂ int-≤)
instruction-subtype ψ₁⋆ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
                    {ι = salloc n} of-salloc = _ , of-salloc , Γ-≤ (stack-append-subtype (replicate-subtype n) sp₁≤sp₂) regs₁≤regs₂
  where replicate-subtype : ∀ {Δ} n →
                              Δ ⊢ replicate n ns ≤ replicate n ns
        replicate-subtype zero = []
        replicate-subtype (suc n) = ns-≤ ∷ replicate-subtype n
instruction-subtype ψ₁⋆ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
                    {ι = sfree n} (of-sfree drop₁)
  with stack-drop-subtype sp₁≤sp₂ drop₁
... | sp₂' , drop₂ , sp₂'≤sp₁' = _ , of-sfree drop₂ , Γ-≤ sp₂'≤sp₁' regs₁≤regs₂
instruction-subtype ψ₁⋆ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
                    {ι = sld ♯rd i} (of-sld l)
  with stack-lookup₂-≤ sp₁≤sp₂ l
... | τ₂ , τ₂≤τ₁ , l' = _ , of-sld l' , Γ-≤ sp₁≤sp₂ (regs-update-≤ ♯rd regs₁≤regs₂ τ₂≤τ₁)
instruction-subtype ψ₁⋆ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
                    {ι = sst i ♯rs} (of-sst up)
  with stack-update-≤ sp₁≤sp₂ (allzipᵥ-lookup ♯rs regs₁≤regs₂) up
... | sp₂' , up' , sp₂'≤sp₁' = _ , of-sst up' , Γ-≤ sp₂'≤sp₁' regs₁≤regs₂
instruction-subtype {Δ = Δ} ψ₁⋆ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
                    {ι = ld ♯rd ♯rs i} (of-ld eq l)
  with allzipᵥ-lookup ♯rs regs₁≤regs₂
... | lookup₁≤lookup₂
  with ≤tuple⇒≡tuple (subst₂ (_⊢_≤_ Δ) refl eq lookup₁≤lookup₂)
... | τs⁻ , eq₁
  with subst₂ (_⊢_≤_ Δ) eq₁ eq lookup₁≤lookup₂
... | tuple-≤ τs₁≤τs₂
  with allzip-lookup₂ l τs₁≤τs₂
... | (τ , init) , l' , τ⁻-≤ τ⋆ φ-≤-init
  = _ , of-ld eq₁ l' , Γ-≤ sp₁≤sp₂ (regs-update-≤ ♯rd regs₁≤regs₂ (≤-refl τ⋆))
instruction-subtype {Δ = Δ} {Γ₁ = registerₐ sp₁ regs₁} {Γ₂ = registerₐ sp₂ regs₂} ψ₁⋆ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
                    {ι = st ♯rd i ♯rs} (of-st eq lookup≤τ l₁ up₁)
  with allzipᵥ-lookup ♯rd regs₁≤regs₂ | allzipᵥ-lookup ♯rs regs₁≤regs₂
... | lookup-rd₁≤lookup-rd₂ | lookup-rs₁≤lookup-rs₁
  with ≤tuple⇒≡tuple (subst₂ (_⊢_≤_ Δ) refl eq lookup-rd₁≤lookup-rd₂)
... | τs⁻₂ , eq₁
  with subst₂ (_⊢_≤_ Δ) eq₁ eq lookup-rd₁≤lookup-rd₂
... | tuple-≤ τs⁻₁≤τs⁻₂
  with allzip-lookup₂ l₁ τs⁻₁≤τs⁻₂
... | (τ , φ) , l₂ , τ⁻-≤ τ⋆ φ₁≤φ₂
  with <-to-← τs⁻₂ (τ , init) {i} (subst (λ len → i < len) (sym (AllZip-length τs⁻₁≤τs⁻₂)) (←-to-< up₁))
... | τs⁻₂' , up₂ = registerₐ sp₁ (update ♯rd (tuple τs⁻₂') regs₁) , of-st eq₁ (≤-trans lookup-rs₁≤lookup-rs₁ lookup≤τ) l₂ up₂ , Γ-≤ sp₁≤sp₂ (regs-update-≤ ♯rd regs₁≤regs₂ (tuple-≤ (allzip-update up₂ up₁ (τ⁻-≤ τ⋆ φ-≤-init) τs⁻₁≤τs⁻₂)))
instruction-subtype ψ₁⋆ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
                    {ι = malloc ♯rd τs} (of-malloc τs⋆) =
  _ , of-malloc τs⋆ , Γ-≤ sp₁≤sp₂ (regs-update-≤ ♯rd regs₁≤regs₂ (≤-refl (valid-tuple (help τs⋆))))
    where help : ∀ {Δ} {τs : List Type} →
                   All (λ τ → Δ ⊢ τ Valid) τs →
                   All (λ τ⁻ → Δ ⊢ τ⁻ Valid) (map (λ τ → τ , uninit) τs)
          help [] = []
          help (τ⋆ ∷ τs⋆) = valid-τ⁻ τ⋆ ∷ help τs⋆
instruction-subtype ψ₁⋆ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
                    {ι = mov ♯rd v} (of-mov v⋆)
  with vval-subtype ψ₁⋆ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂) v⋆
... | τ' , τ≤τ' , v⋆' =
  _ , of-mov v⋆' , Γ-≤ sp₁≤sp₂ (regs-update-≤ ♯rd regs₁≤regs₂ τ≤τ')
instruction-subtype ψ₁⋆ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
                    {ι = beq ♯r v} (of-beq eq v⋆ Γ₁≤Γ')
  with allzipᵥ-lookup ♯r regs₁≤regs₂
     | vval-subtype ψ₁⋆ (Γ-≤ sp₁≤sp₂ regs₁≤regs₂) v⋆
... | ♯r⋆ | ∀[ [] ] Γ'' , ∀-≤ Γ'≤Γ'' , v⋆'
  rewrite eq
  = _ , of-beq (≤int⇒≡int ♯r⋆) v⋆' (≤-trans (Γ-≤ sp₁≤sp₂ regs₁≤regs₂) (≤-trans Γ₁≤Γ' Γ'≤Γ'')) , Γ-≤ sp₁≤sp₂ regs₁≤regs₂

instructionsequence-subtype : ∀ {ψ₁ Δ Γ₁ Γ₂ I} →
                                [] ⊢ ψ₁ Valid →
                                Δ ⊢ Γ₁ ≤ Γ₂ →
                                ψ₁ , Δ , Γ₂ ⊢ I instructionsequence →
                                ψ₁ , Δ , Γ₁ ⊢ I instructionsequence
instructionsequence-subtype ψ₁⋆ Γ₁≤Γ₂ (of-~> ι⋆ I⋆)
  with instruction-subtype ψ₁⋆ Γ₁≤Γ₂ ι⋆
... | Γ₂' , ι⋆' , Γ₂'≤Γ₁'
  with instructionsequence-subtype ψ₁⋆ Γ₂'≤Γ₁' I⋆
... | I⋆' = of-~> ι⋆' I⋆'
instructionsequence-subtype ψ₁⋆ Γ₁≤Γ₂ (of-jmp v⋆ Γ₁≤Γ')
  with vval-subtype ψ₁⋆ Γ₁≤Γ₂ v⋆
... | ∀[ [] ] Γ'' , ∀-≤ Γ'≤Γ'' , v⋆' = of-jmp v⋆' (≤-trans Γ₁≤Γ₂ (≤-trans Γ₁≤Γ' Γ'≤Γ''))
