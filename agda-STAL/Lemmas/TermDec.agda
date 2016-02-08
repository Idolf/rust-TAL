module Lemmas.TermDec where

open import Util
open import Judgments
open import Lemmas.Substitution
open import Lemmas.Types
open import Lemmas.TypeSubstitution
open import Lemmas.Equality
open HighGrammar

instantiation-dec : ∀ {Δ} θ a →
                      Dec (Δ ⊢ θ of a instantiation)
instantiation-dec {Δ} (α τ) α
  = dec-inj of-α (λ { (of-α τ⋆) → τ⋆ }) (Δ ⊢? τ Valid)
instantiation-dec (α τ) ρ = no (λ ())
instantiation-dec (ρ σ) α = no (λ ())
instantiation-dec {Δ} (ρ σ) ρ
  = dec-inj of-ρ (λ { (of-ρ σ⋆) → σ⋆ }) (Δ ⊢? σ Valid)

instantiations-dec : ∀ {Δ₁} θs Δ₂ →
                       Dec (Δ₁ ⊢ θs of Δ₂ instantiations)
instantiations-dec [] [] = yes []
instantiations-dec [] (a ∷ Δ₂) = no (λ ())
instantiations-dec (θ ∷ θs) [] = no (λ ())
instantiations-dec (θ ∷ θs) (a ∷ Δ₂)
  with instantiation-dec θ a | instantiations-dec θs Δ₂
... | yes θ⋆ | yes θs⋆ = yes (θ⋆ ∷ θs⋆)
... | no ¬θ⋆ | _ = no (λ { (θ⋆ ∷ θs⋆) → ¬θ⋆ θ⋆})
... | _ | no ¬θs⋆ = no (λ { (θ⋆ ∷ θs⋆) → ¬θs⋆ θs⋆})

vval-unique : ∀ {ψ₁ Δ Γ v τ₁ τ₂} →
                ψ₁ , Δ , Γ ⊢ v of τ₁ vval →
                ψ₁ , Δ , Γ ⊢ v of τ₂ vval →
                τ₁ ≡ τ₂
vval-unique of-reg of-reg = refl
vval-unique (of-globval l₁) (of-globval l₂) = ↓-unique l₁ l₂
vval-unique of-int of-int = refl
vval-unique (of-Λ v⋆₁ θs⋆₁ subs-Γ₁) (of-Λ v⋆₂ θs⋆₂ subs-Γ₂)
  with vval-unique v⋆₁ v⋆₂
vval-unique (of-Λ v⋆₁ θs⋆₁ subs-Γ₁) (of-Λ v⋆₂ θs⋆₂ subs-Γ₂)
    | refl with subst-unique-many subs-Γ₁ subs-Γ₂
vval-unique (of-Λ v⋆₁ θs⋆₁ subs-Γ₁) (of-Λ v⋆₂ θs⋆₂ subs-Γ₂)
    | refl | refl
    = refl

vval-helper : ∀ {ψ₁ Δ Γ v τ₁ τ₂} →
                ψ₁ , Δ , Γ ⊢ v of τ₁ vval →
                ψ₁ , Δ , Γ ⊢ v of τ₂ vval →
                τ₁ ≢ τ₂ →
                ⊥
vval-helper v⋆₁ v⋆₂ τ₁≢τ₂
  with τ₁≢τ₂ (vval-unique v⋆₁ v⋆₂)
... | ()

vval-dec : ∀ {ψ₁ Δ Γ} v →
             Dec (∃ λ τ → ψ₁ , Δ , Γ ⊢ v of τ vval)
vval-dec (reg ♯r) = yes (_ , of-reg)
vval-dec {ψ₁} (globval lab)
  with ↓-dec ψ₁ lab
... | yes (τ , l) = yes (τ , of-globval l)
... | no ¬l = no (λ { (_ , of-globval l) → ¬l (_ , l)})
vval-dec (int n) = yes (int , of-int)
vval-dec {ψ₁} {Δ} {Γ} (Λ Δₒ ∙ v ⟦ θs ⟧)
  with vval-dec {ψ₁} {Δ} {Γ} v
... | no ¬v⋆ = no (λ { (_ , of-Λ v⋆ θs⋆ subs-Γ) → ¬v⋆ (_ , v⋆) })
... | yes (α⁼ ι , v⋆) = no (λ { (_ , of-Λ v⋆' θs⋆ subs-Γ) → vval-helper v⋆ v⋆' (λ ())})
... | yes (int , v⋆) = no (λ { (_ , of-Λ v⋆' θs⋆ subs-Γ) → vval-helper v⋆ v⋆' (λ ())})
... | yes (ns , v⋆) = no (λ { (_ , of-Λ v⋆' θs⋆ subs-Γ) → vval-helper v⋆ v⋆' (λ ())})
... | yes (tuple τs , v⋆) = no (λ { (_ , of-Λ v⋆' θs⋆ subs-Γ) → vval-helper v⋆ v⋆' (λ ())})
... | yes (∀[ Δᵢ ] Γᵢ , v⋆)
  with instantiations-dec {Δₒ ++ Δ} θs Δᵢ
... | no ¬θs⋆ = no (help v⋆ ¬θs⋆)
  where help : ∀ {v θs Δᵢ Γᵢ} →
                 ψ₁ , Δ , Γ ⊢ v of ∀[ Δᵢ ] Γᵢ vval →
                 ¬ Δₒ ++ Δ ⊢ θs of Δᵢ instantiations →
                 ¬ ∃ λ τ → (ψ₁ , Δ , Γ ⊢ Λ Δₒ ∙ v ⟦ θs ⟧ of τ vval)
        help v⋆ ¬θs⋆ (._ , of-Λ v⋆' θs⋆ subs-Γ)
          with vval-unique v⋆ v⋆'
        help v⋆ ¬θs⋆ (._ , of-Λ v⋆' θs⋆ subs-Γ)
            | refl
          = ¬θs⋆ θs⋆
... | yes θs⋆
  with weaken (length Δᵢ) (length Δₒ) Γᵢ ⟦ θs / 0 ⟧many?
... | yes (Γₒ , subs-Γ) = yes (_ , of-Λ v⋆ θs⋆ subs-Γ)
... | no ¬subs-Γ = no (help v⋆ ¬subs-Γ)
  where help : ∀ {v θs Δᵢ Γᵢ} →
                 ψ₁ , Δ , Γ ⊢ v of ∀[ Δᵢ ] Γᵢ vval →
                 ¬ (∃ λ Γₒ → weaken (length Δᵢ) (length Δₒ) Γᵢ ⟦ θs / 0 ⟧many≡ Γₒ) →
                 ¬ ∃ λ τ → (ψ₁ , Δ , Γ ⊢ Λ Δₒ ∙ v ⟦ θs ⟧ of τ vval)
        help v⋆ ¬subs-Γ (._ , of-Λ v⋆' θs⋆ subs-Γ)
          with vval-unique v⋆ v⋆'
        help v⋆ ¬subs-Γ (._ , of-Λ v⋆' θs⋆ subs-Γ)
            | refl
          = ¬subs-Γ (_ , subs-Γ)

instruction-unique : ∀ {ψ₁ Δ Γ ι Γ₁ Γ₂} →
                       ψ₁ , Δ , Γ ⊢ ι of Γ₁ instruction →
                       ψ₁ , Δ , Γ ⊢ ι of Γ₂ instruction →
                       Γ₁ ≡ Γ₂
instruction-unique (of-add eq₁ v⋆₁) (of-add eq₂ v⋆₂) = refl
instruction-unique (of-sub eq₁ v⋆₁) (of-sub eq₂ v⋆₂) = refl
instruction-unique of-salloc of-salloc = refl
instruction-unique (of-sfree drop₁) (of-sfree drop₂) = {!!}
  -- rewrite stack-drop-unique drop₁ drop₂ = refl
instruction-unique (of-sld x) (of-sld x₁) = {!!}
instruction-unique (of-sst x) (of-sst x₁) = {!!}
instruction-unique (of-ld eq₁ l₁) (of-ld eq₂ l₂)
  with trans (sym eq₁) eq₂
instruction-unique (of-ld eq₁ l₁) (of-ld eq₂ l₂)
    | refl with ↓-unique l₁ l₂
instruction-unique (of-ld eq₁ l₁) (of-ld eq₂ l₂)
    | refl | refl = refl
instruction-unique (of-st eq₁ lookup≤₁τ l₁ up₁) (of-st eq₂ lookup≤₂τ l₂ up₂)
  with trans (sym eq₁) eq₂
instruction-unique (of-st eq₁ lookup≤₁τ l₁ up₁) (of-st eq₂ lookup≤₂τ l₂ up₂)
    | refl with ↓-unique l₁ l₂
instruction-unique (of-st eq₁ lookup≤₁τ l₁ up₁) (of-st eq₂ lookup≤₂τ l₂ up₂)
    | refl | refl with ←-unique up₁ up₂
instruction-unique (of-st eq₁ lookup≤₁τ l₁ up₁) (of-st eq₂ lookup≤₂τ l₂ up₂)
    | refl | refl | refl = refl
instruction-unique (of-malloc τs⋆₁) (of-malloc τs⋆₂) = refl
instruction-unique (of-mov v⋆₁) (of-mov v⋆₂)
  with vval-unique v⋆₁ v⋆₂
instruction-unique (of-mov v⋆₁) (of-mov v⋆₂)
    | refl = refl
instruction-unique (of-beq eq₁ v⋆₁ Γ≤₁Γ') (of-beq eq₂ v⋆₂ Γ≤₂Γ') = refl


instructionsequence-dec : ∀ {ψ₁ Δ Γ} I →
                            Dec (ψ₁ , Δ , Γ ⊢ I instructionsequence)
instructionsequence-dec (ι ~> I) = {!!}
instructionsequence-dec {ψ₁} {Δ} {Γ} (jmp v)
  with vval-dec {ψ₁} {Δ} {Γ} v
... | no ¬v⋆ = no (λ { (of-jmp v⋆ Γ≤Γ') → ¬v⋆ (_ , v⋆)})
... | yes (α⁼ ι , v⋆) = no (λ { (of-jmp v⋆' Γ≤Γ') → vval-helper v⋆ v⋆' (λ ()) })
... | yes (int , v⋆) = no (λ { (of-jmp v⋆' Γ≤Γ') → vval-helper v⋆ v⋆' (λ ()) })
... | yes (ns , v⋆) = no (λ { (of-jmp v⋆' Γ≤Γ') → vval-helper v⋆ v⋆' (λ ()) })
... | yes (tuple x , v⋆) = no (λ { (of-jmp v⋆' Γ≤Γ') → vval-helper v⋆ v⋆' (λ ()) })
... | yes (∀[ a ∷ Δ' ] Γ' , v⋆) = no (λ { (of-jmp v⋆' Γ≤Γ') → vval-helper v⋆ v⋆' (λ ()) })
... | yes (∀[ [] ] Γ' , v⋆)
  with Δ ⊢ Γ ≤? Γ'
... | yes Γ≤Γ' = yes (of-jmp v⋆ Γ≤Γ')
... | no Γ≰Γ' = no (help v⋆ Γ≰Γ')
  where help : ψ₁ , Δ , Γ ⊢ v of ∀[ [] ] Γ' vval →
               ¬ (Δ ⊢ Γ ≤ Γ') →
               ¬ (ψ₁ , Δ , Γ ⊢ jmp v instructionsequence)
        help v⋆ Γ≰Γ' (of-jmp v⋆' Γ≤Γ')
          with vval-unique v⋆ v⋆'
        help v⋆ Γ≰Γ' (of-jmp v⋆' Γ≤Γ')
            | refl = Γ≰Γ' Γ≤Γ'
instructionsequence-dec halt = yes of-halt

gval-dec : ∀ {ψ₁} g τ → Dec (ψ₁ ⊢ g of τ gval)
gval-dec (code[ Δ ] Γ ∙ I) (α⁼ ι) = no (λ ())
gval-dec (code[ Δ ] Γ ∙ I) int = no (λ ())
gval-dec (code[ Δ ] Γ ∙ I) ns = no (λ ())
gval-dec (code[ Δ₁ ] Γ₁ ∙ I) (∀[ Δ₂ ] Γ₂)
  with Δ₁ ≟ Δ₂ | Γ₁ ≟ Γ₂
... | no Δ₁≢Δ₂ | _ = no (help Δ₁≢Δ₂)
  where help : ∀ {ψ₁ Δ₁ Γ₁ I Δ₂ Γ₂} →
                 Δ₁ ≢ Δ₂ →
                 ¬ (ψ₁ ⊢ code[ Δ₁ ] Γ₁ ∙ I of ∀[ Δ₂ ] Γ₂ gval)
        help neq (of-gval Γ⋆ I⋆) = neq refl
... | _ | no Γ₁≢Γ₂ = no (help Γ₁≢Γ₂)
  where help : ∀ {ψ₁ Δ₁ Γ₁ I Δ₂ Γ₂} →
                 Γ₁ ≢ Γ₂ →
                 ¬ (ψ₁ ⊢ code[ Δ₁ ] Γ₁ ∙ I of ∀[ Δ₂ ] Γ₂ gval)
        help neq (of-gval Γ⋆ I⋆) = neq refl
gval-dec {ψ₁} (code[ Δ ] Γ ∙ I) (∀[ .Δ ] .Γ)
    | yes refl | yes refl
    with Δ ⊢? Γ Valid | instructionsequence-dec I
... | yes Γ⋆ | yes I⋆ = yes (of-gval Γ⋆ I⋆)
... | no ¬Γ⋆ | _ = no (λ { (of-gval Γ⋆ I⋆) → ¬Γ⋆ Γ⋆})
... | _ | no ¬I⋆ = no (λ { (of-gval Γ⋆ I⋆) → ¬I⋆ I⋆})
gval-dec (code[ Δ ] Γ ∙ I) (tuple τs) = no (λ ())

gvals-dec : ∀ {ψ₁} gs τs → Dec (AllZip (λ g τ → ψ₁ ⊢ g of τ gval) gs τs)
gvals-dec [] [] = yes []
gvals-dec [] (τ ∷ τs) = no (λ ())
gvals-dec (g ∷ gs) [] = no (λ ())
gvals-dec (g ∷ gs) (τ ∷ τs)
  with gval-dec g τ | gvals-dec gs τs
... | yes g⋆ | yes gs⋆ = yes (g⋆ ∷ gs⋆)
... | no ¬g⋆ | _ = no (λ { (g⋆ ∷ gs⋆) → ¬g⋆ g⋆ })
... | _ | no ¬gs⋆ = no (λ { (g⋆ ∷ gs⋆) → ¬gs⋆ gs⋆ })

gval-unique-helper : ∀ {ψ₁ Δ Γ I τ} →
                       ψ₁ ⊢ code[ Δ ] Γ ∙ I of τ gval →
                       τ ≡ ∀[ Δ ] Γ
gval-unique-helper (of-gval Γ⋆ I⋆) = refl

gval-unique : ∀ g →
                ∃ λ τ →
                    (∀ {ψ₁ τ'} → ψ₁ ⊢ g of τ' gval → τ' ≡ τ)
gval-unique (code[ Δ ] Γ ∙ I)
  = ∀[ Δ ] Γ , gval-unique-helper

gvals-unique : ∀ gs →
                 ∃ λ τs →
                     (∀ {ψ₁ τs'} → AllZip (λ g τ → ψ₁ ⊢ g of τ gval) gs τs' → τs' ≡ τs)
gvals-unique []
  = [] , (λ { {ψ₁} {[]} [] → refl ; {ψ₁} {τ' ∷ τs'} () })
gvals-unique (g ∷ gs)
  with gval-unique g | gvals-unique gs
... | τ , τ-eq | τs , τs-eq
  = τ ∷ τs , help τ-eq τs-eq
    where help : ∀ {g gs τ τs} →
                   (∀ {ψ₁ τ'}  → ψ₁ ⊢ g of τ' gval → τ' ≡ τ) →
                   (∀ {ψ₁ τs'} → AllZip (λ g τ → ψ₁ ⊢ g of τ gval) gs τs' → τs' ≡ τs) →
                   (∀ {ψ₁ τs'} → AllZip (λ g τ → ψ₁ ⊢ g of τ gval) (g ∷ gs) τs' → τs' ≡ τ ∷ τs)
          help τ-eq τs-eq (g⋆ ∷ gs⋆)
            rewrite τ-eq g⋆
                  | τs-eq gs⋆
              = refl

globals-dec : ∀ G → Dec (∃ λ τs → ⊢ G of τs globals)
globals-dec gs
  with gvals-unique gs
... | τs , τs-eq
  with gvals-dec {τs} gs τs
... | yes gs⋆ = yes (τs , of-globals gs⋆)
... | no ¬gs⋆ = no (help τs-eq ¬gs⋆)
  where help : ∀ {gs τs} →
                 (∀ {ψ₁ τs'} → AllZip (λ g τ → ψ₁ ⊢ g of τ gval) gs τs' → τs' ≡ τs) →
                 ¬ AllZip (λ g τ → τs ⊢ g of τ gval) gs τs →
                 ¬ ∃ λ τs → ⊢ gs of τs globals
        help τs-eq ¬gs⋆ (τs , of-globals gs⋆)
          rewrite τs-eq gs⋆
            = ¬gs⋆ gs⋆
