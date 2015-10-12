open import Grammar
open import TypeJudgments
open import Util

open import Data.Nat.Properties using (cancel-+-left)

mutual
  infix 4 _⊢_≤τ_
  data _⊢_≤τ_ (Δ : TypeAssignment) : Type → Type → Set where
    α⁼-≤ :
          ∀ {ι} →
       Δ ⊢ α⁼ ι Type →
      ----------------
      Δ ⊢ α⁼ ι ≤τ α⁼ ι

    int-≤ :
      --------------
      Δ ⊢ int ≤τ int

    ns-≤ :
      ------------
      Δ ⊢ ns ≤τ ns

    ∀-≤ :
            ∀ {Δ' Γ₁ Γ₂} →
        Δ ⊢ Δ' TypeAssignment →
          Δ' ++ Δ ⊢ Γ₁ ≤Γ Γ₂ →
      ----------------------------
      Δ ⊢ ∀[ Δ' ] Γ₁ ≤τ ∀[ Δ' ] Γ₂

    tuple-≤ :
                    ∀ {m} {τs₁ τs₂ : Vec InitType m} →
      Allᵥ (λ {(τ⁻₁ , τ⁻₂) → Δ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂ }) (Vec-zip τs₁ τs₂) →
      -------------------------------------------------------------
                       Δ ⊢ tuple τs₁ ≤τ tuple τs₂

  infix 4 _⊢_≤τ⁻_
  data _⊢_≤τ⁻_ (Δ : TypeAssignment) : InitType → InitType → Set where
    τ⁻-≤ :
          ∀ {τ₁ τ₂ φ} →
          Δ ⊢ τ₁ ≤τ τ₂ →
      ---------------------
      Δ ⊢ τ₁ , φ ≤τ⁻ τ₂ , φ

  infix 4 _⊢_≤σ_
  data _⊢_≤σ_ (Δ : TypeAssignment) : StackType → StackType → Set where
    σ-≤ :
          ∀ {σ} →
      Δ ⊢ σ StackType →
      -----------------
         Δ ⊢ σ ≤σ σ

  infix 4 _⊢_≤Γ_
  data _⊢_≤Γ_ (Δ : TypeAssignment) : (Γ₁ Γ₂ : RegisterAssignment) → Set where
    Γ-≤ :
               ∀ {sp₁ sp₂ regs₁ regs₂} →
                Δ ⊢ sp₁ ≤σ sp₂ →
       Allᵥ (λ { (τ₁ , τ₂) → Δ ⊢ τ₁ ≤τ τ₂ })
              (Vec-zip regs₁ regs₂) →
      ----------------------------------------------
      Δ ⊢ registerₐ sp₁ regs₁ ≤Γ registerₐ sp₂ regs₂

private
  mutual
    infix 4 _⊢_≤τ?_
    _⊢_≤τ?_ : ∀ Δ τ₁ τ₂ → Dec (Δ ⊢ τ₁ ≤τ τ₂)
    Δ ⊢ α⁼ ι₁ ≤τ? α⁼ ι₂ with ι₁ ≟ ι₂ | ↓-decᵥ Δ ι₁ α
    Δ ⊢ α⁼ ι ≤τ? α⁼ .ι | yes refl | yes l = yes (α⁼-≤ (valid-α⁼ l))
    Δ ⊢ α⁼ ι  ≤τ? α⁼ .ι | yes refl | no ¬l =
      no (λ { (α⁼-≤ (valid-α⁼ l)) → ¬l l })
    Δ ⊢ α⁼ ι₁ ≤τ? α⁼ ι₂ | no ι₁≢ι₂ | _ = no (ι₁≢ι₂ ∘ help)
      where help : ∀ {Δ ι₁ ι₂} → Δ ⊢ α⁼ ι₁ ≤τ α⁼ ι₂ → ι₁ ≡ ι₂
            help (α⁼-≤ τ⋆) = refl
    Δ ⊢ α⁼ ι₁ ≤τ? int = no (λ ())
    Δ ⊢ α⁼ ι₁ ≤τ? ns = no (λ ())
    Δ ⊢ α⁼ ι₁ ≤τ? (∀[ Δ₂ ] Γ₂) = no (λ ())
    Δ ⊢ α⁼ ι₁ ≤τ? tuple τs₂ = no (λ ())
    Δ ⊢ int ≤τ? α⁼ ι₂ = no (λ ())
    Δ ⊢ int ≤τ? int = yes int-≤
    Δ ⊢ int ≤τ? ns = no (λ ())
    Δ ⊢ int ≤τ? (∀[ Δ₂ ] Γ₂) = no (λ ())
    Δ ⊢ int ≤τ? tuple τs₂ = no (λ ())
    Δ ⊢ ns ≤τ? α⁼ ι₂ = no (λ ())
    Δ ⊢ ns ≤τ? int = no (λ ())
    Δ ⊢ ns ≤τ? ns = yes ns-≤
    Δ ⊢ ns ≤τ? (∀[ Δ₂ ] Γ₂) = no (λ ())
    Δ ⊢ ns ≤τ? tuple τs₂ = no (λ ())
    Δ ⊢ ∀[ Δ₁ ] Γ₁ ≤τ? α⁼ ι₂ = no (λ ())
    Δ ⊢ ∀[ Δ₁ ] Γ₁ ≤τ? int = no (λ ())
    Δ ⊢ ∀[ Δ₁ ] Γ₁ ≤τ? ns = no (λ ())
    Δ ⊢ ∀[ Δ₁ ] Γ₁ ≤τ? (∀[ Δ₂ ] Γ₂)
      with Δ₁ ≟ Δ₂ | Δ ⊢? Δ₁ Valid | Δ₁ ++ Δ ⊢ Γ₁ ≤Γ? Γ₂
    Δ ⊢ ∀[ Δ' ] Γ₁ ≤τ? (∀[ .Δ' ] Γ₂)
      | yes refl | yes Δ'⋆ | yes Γ₁≤Γ₂ = yes (∀-≤ Δ'⋆ Γ₁≤Γ₂)
    Δ ⊢ ∀[ Δ' ] Γ₁ ≤τ? (∀[ .Δ' ] Γ₂)
      | yes refl | no ¬Δ'* | _ = no (λ { (∀-≤ Δ'⋆ Γ₁≤Γ₂) → ¬Δ'* Δ'⋆ })
    Δ ⊢ ∀[ Δ' ] Γ₁ ≤τ? (∀[ .Δ' ] Γ₂)
      | yes refl | _ | no Γ₁≰Γ₂  = no (λ { (∀-≤ Δ'⋆ Γ₁≤Γ₂) → Γ₁≰Γ₂ Γ₁≤Γ₂ })
    Δ ⊢ ∀[ Δ₁ ] Γ₁ ≤τ? (∀[ Δ₂ ] Γ₂) | no Δ₁≢Δ₂ | _ | _ = no (Δ₁≢Δ₂ ∘ help)
      where help : ∀ {Δ Δ₁ Δ₂ Γ₁ Γ₂} → Δ ⊢ ∀[ Δ₁ ] Γ₁ ≤τ ∀[ Δ₂ ] Γ₂ → Δ₁ ≡ Δ₂
            help (∀-≤ Δ'⋆ Γ₁≤Γ₂) = refl
    Δ ⊢ ∀[ Δ₁ ] Γ₁ ≤τ? tuple τs₂ = no (λ ())
    Δ ⊢ tuple τs₁ ≤τ? α⁼ ι₂ = no (λ ())
    Δ ⊢ tuple τs₁ ≤τ? int = no (λ ())
    Δ ⊢ tuple τs₁ ≤τ? ns = no (λ ())
    Δ ⊢ tuple τs₁ ≤τ? ∀[ Δ₂ ] Γ₂ = no (λ ())
    Δ ⊢ tuple {m₁} τs₁ ≤τ? tuple {m₂} τs₂ with m₁ ≟ m₂
    Δ ⊢ tuple τs₁ ≤τ? tuple τs₂ | yes refl =
      dec-inj tuple-≤ (λ { (tuple-≤ τs≤) → τs≤ }) (Δ ⊢ τs₁ ≤τs⁻? τs₂)
    Δ ⊢ tuple τs₁ ≤τ? tuple τs₂ | no m₁≢m₂ = no (m₁≢m₂ ∘ help)
      where help : ∀ {Δ m₁ m₂ τs₁ τs₂} →
                   Δ ⊢ tuple {m₁} τs₁ ≤τ tuple {m₂} τs₂ → m₁ ≡ m₂
            help (tuple-≤ τs₁≤τs₂) = refl

    infix 4 _⊢_≤τ⁻?_
    _⊢_≤τ⁻?_ : ∀ Δ τ⁻₁ τ⁻₂ → Dec (Δ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂)
    Δ ⊢ τ₁ , φ₁ ≤τ⁻? τ₂ , φ₂ with φ₁ ≟ φ₂ | Δ ⊢ τ₁ ≤τ? τ₂
    Δ ⊢ τ₁ , φ  ≤τ⁻? (τ₂ , .φ)
      | yes refl | yes τ₁≤τ₂ = yes (τ⁻-≤ τ₁≤τ₂)
    Δ ⊢ τ₁ , φ  ≤τ⁻? (τ₂ , .φ)
      | yes refl | no τ₁≰τ₂ = no (λ { (τ⁻-≤ τ₁≤τ₂) → τ₁≰τ₂ τ₁≤τ₂ })
    Δ ⊢ τ₁ , φ₁ ≤τ⁻? (τ₂ , φ₂)
      | no φ₁≢φ₂ | _ = no (φ₁≢φ₂ ∘ help)
      where help : ∀ {Δ τ₁ τ₂ φ₁ φ₂} →
                   Δ ⊢ τ₁ , φ₁ ≤τ⁻ τ₂ , φ₂ → φ₁ ≡ φ₂
            help (τ⁻-≤ τ₁≤τ₂) = refl

    infix 4 _⊢_≤τs⁻?_
    _⊢_≤τs⁻?_ : ∀ Δ {m} (τs⁻₁ τs⁻₂ : Vec InitType m) →
                  Dec (Allᵥ (λ { (τ⁻₁ , τ⁻₂) → Δ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂ })
                      (Vec-zip τs⁻₁ τs⁻₂))
    Δ ⊢ [] ≤τs⁻? [] = yes []
    Δ ⊢ τ₁ ∷ τs⁻₁ ≤τs⁻? τ₂ ∷ τs⁻₂ with Δ ⊢ τ₁ ≤τ⁻? τ₂ | Δ ⊢ τs⁻₁ ≤τs⁻? τs⁻₂
    ... | yes τ₁≤τ₂ | yes τs⁻₁≤τs⁻₂ = yes (τ₁≤τ₂ ∷ τs⁻₁≤τs⁻₂)
    ... | no τ₁≰τ₂ | _ = no (λ { (τ₁≤τ₂ ∷ τs⁻₁≤τs⁻₂) → τ₁≰τ₂ τ₁≤τ₂ })
    ... | _ | no τs⁻₁≰τs⁻₂ =
      no (λ { (τ₁≤τ₂ ∷ τs⁻₁≤τs⁻₂) → τs⁻₁≰τs⁻₂ τs⁻₁≤τs⁻₂ })

    infix 4 _⊢_≤σ?_
    _⊢_≤σ?_ : ∀ Δ σ₁ σ₂ → Dec (Δ ⊢ σ₁ ≤σ σ₂)
    Δ ⊢ σ₁ ≤σ? σ₂ with σ₁ ≟ σ₂ | Δ ⊢? σ₁ Valid
    Δ ⊢ σ  ≤σ? .σ | yes refl | yes σ⋆ = yes (σ-≤ σ⋆)
    Δ ⊢ σ  ≤σ? .σ | yes refl | no ¬σ⋆ = no (λ { (σ-≤ σ⋆) → ¬σ⋆ σ⋆ })
    Δ ⊢ σ₁ ≤σ? σ₂ | no σ₁≢σ₂ | _ = no (σ₁≢σ₂ ∘ help)
      where help : ∀ {Δ σ₁ σ₂} →
                   Δ ⊢ σ₁ ≤σ σ₂ → σ₁ ≡ σ₂
            help (σ-≤ σ⋆) = refl

    infix 4 _⊢_≤Γ?_
    _⊢_≤Γ?_ : ∀ Δ Γ₁ Γ₂ → Dec (Δ ⊢ Γ₁ ≤Γ Γ₂)
    Δ ⊢ registerₐ sp₁ regs₁ ≤Γ? registerₐ sp₂ regs₂
      with Δ ⊢ sp₁ ≤σ? sp₂ | Δ ⊢ regs₁ ≤regs? regs₂
    ... | yes sp₁≤sp₂ | yes regs₁≤regs₂ = yes (Γ-≤ sp₁≤sp₂ regs₁≤regs₂)
    ... | no sp₁≰sp₂  | _ =
      no (λ { (Γ-≤ sp₁≤sp₂ regs₁≤regs₂) → sp₁≰sp₂ sp₁≤sp₂ })
    ... | _ | no regs₁≰regs₂ =
      no (λ { (Γ-≤ sp₁≤sp₂ regs₁≤regs₂) → regs₁≰regs₂ regs₁≤regs₂ })

    infix 4 _⊢_≤regs?_
    _⊢_≤regs?_ : ∀ Δ {m} (regs₁ regs₂ : Vec Type m) →
                   Dec (Allᵥ (λ { (τ₁ , τ₂) → Δ ⊢ τ₁ ≤τ τ₂ })
                       (Vec-zip regs₁ regs₂))
    Δ ⊢ [] ≤regs? [] = yes []
    Δ ⊢ τ₁ ∷ regs₁ ≤regs? τ₂ ∷ regs₂ with
      Δ ⊢ τ₁ ≤τ? τ₂ | Δ ⊢ regs₁ ≤regs? regs₂
    ... | yes τ₁≤τ₂ | yes regs₁≤regs₂ = yes (τ₁≤τ₂ ∷ regs₁≤regs₂)
    ... | no τ₁≰τ₂ | _ = no (λ { (τ₁≤τ₂ ∷ regs₁≤regs₂) → τ₁≰τ₂ τ₁≤τ₂ })
    ... | _ | no regs₁≰regs₂ =
      no (λ { (τ₁≤τ₂ ∷ regs₁≤regs₂) → regs₁≰regs₂ regs₁≤regs₂ })

  mutual
    τ-refl : ∀ {Δ τ} → Δ ⊢ τ Type → Δ ⊢ τ ≤τ τ
    τ-refl (valid-α⁼ l) = α⁼-≤ (valid-α⁼ l)
    τ-refl valid-int = int-≤
    τ-refl valid-ns = ns-≤
    τ-refl (valid-∀ Δ⋆ Γ⋆) = ∀-≤ Δ⋆ (Γ-refl Γ⋆)
    τ-refl (valid-tuple τs⋆) = tuple-≤ (Allᵥ-zip (τs⁻-refl τs⋆))

    τ⁻-refl : ∀ {Δ τ⁻} → Δ ⊢ τ⁻ InitType → Δ ⊢ τ⁻ ≤τ⁻ τ⁻
    τ⁻-refl (valid-τ⁻ τ⋆) = τ⁻-≤ (τ-refl τ⋆)

    τs⁻-refl : ∀ {Δ m} {τs : Vec InitType m} →
                 Allᵥ (λ τ⁻ → Δ  ⊢ τ⁻ InitType) τs →
                 Allᵥ (λ τ⁻ → Δ  ⊢ τ⁻ ≤τ⁻ τ⁻) τs
    τs⁻-refl [] = []
    τs⁻-refl (τ⁻⋆ ∷ ps) = τ⁻-refl τ⁻⋆ ∷ τs⁻-refl ps

    σ-refl : ∀ {Δ σ} → Δ ⊢ σ StackType → Δ ⊢ σ ≤σ σ
    σ-refl σ⋆ = σ-≤ σ⋆

    Γ-refl : ∀ {Δ Γ} → Δ ⊢ Γ RegisterAssignment → Δ ⊢ Γ ≤Γ Γ
    Γ-refl (valid-registerₐ sp⋆ regs⋆) =
      Γ-≤ (σ-refl sp⋆) (Allᵥ-zip (regs-refl regs⋆))

    regs-refl : ∀ {Δ m} {regs : Vec Type m} →
                  Allᵥ (λ τ → Δ ⊢ τ Type) regs →
                  Allᵥ (λ τ → Δ ⊢ τ ≤τ τ) regs
    regs-refl {regs = []} [] = []
    regs-refl {regs = _ ∷ _} (τ⋆ ∷ regs⋆) = τ-refl τ⋆ ∷ regs-refl regs⋆

  mutual
    τ-trans : ∀ {Δ τ₁ τ₂ τ₃} → Δ ⊢ τ₁ ≤τ τ₂ → Δ ⊢ τ₂ ≤τ τ₃ → Δ ⊢ τ₁ ≤τ τ₃
    τ-trans (α⁼-≤ τ⋆) (α⁼-≤ _) = α⁼-≤ τ⋆
    τ-trans int-≤ int-≤ = int-≤
    τ-trans ns-≤ ns-≤ = ns-≤
    τ-trans (∀-≤ Δ'⋆ Γ₁₂≤) (∀-≤ _ Γ₂₃≤) = ∀-≤ Δ'⋆ (Γ-trans Γ₁₂≤ Γ₂₃≤)
    τ-trans (tuple-≤ τs₁₂≤) (tuple-≤ τs₂₃≤) = tuple-≤ (τs⁻-trans τs₁₂≤ τs₂₃≤)

    τ⁻-trans : ∀ {Δ τ⁻₁ τ⁻₂ τ⁻₃} → Δ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂ →
                                   Δ ⊢ τ⁻₂ ≤τ⁻ τ⁻₃ →
                                   Δ ⊢ τ⁻₁ ≤τ⁻ τ⁻₃
    τ⁻-trans (τ⁻-≤ τ₁₂≤) (τ⁻-≤ τ₂₃≤) = τ⁻-≤ (τ-trans τ₁₂≤ τ₂₃≤)

    τs⁻-trans :
      ∀ {Δ m} {τs₁ τs₂ τs₃ : Vec InitType m} →
        Allᵥ (λ { (τ⁻₁ , τ⁻₂) → Δ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂ }) (Vec-zip τs₁ τs₂) →
        Allᵥ (λ { (τ⁻₂ , τ⁻₃) → Δ ⊢ τ⁻₂ ≤τ⁻ τ⁻₃ }) (Vec-zip τs₂ τs₃) →
        Allᵥ (λ { (τ⁻₁ , τ⁻₃) → Δ ⊢ τ⁻₁ ≤τ⁻ τ⁻₃ }) (Vec-zip τs₁ τs₃)
    τs⁻-trans {τs₁ = []} {[]} {[]} [] [] = []
    τs⁻-trans {τs₁ = τ₁ ∷ τs₁} {τ₂ ∷ τs₂} {τ₃ ∷ τs₃}
      (τ₁₂≤ ∷ τs₁₂≤) (τ₂₃≤ ∷ τs₂₃≤) =
        τ⁻-trans τ₁₂≤ τ₂₃≤ ∷ τs⁻-trans τs₁₂≤ τs₂₃≤

    σ-trans : ∀ {Δ σ₁ σ₂ σ₃} → Δ ⊢ σ₁ ≤σ σ₂ → Δ ⊢ σ₂ ≤σ σ₃ → Δ ⊢ σ₁ ≤σ σ₃
    σ-trans (σ-≤ σ₁⋆) (σ-≤ σ₂⋆) = σ-≤ σ₁⋆

    Γ-trans : ∀ {Δ Γ₁ Γ₂ Γ₃} → Δ ⊢ Γ₁ ≤Γ Γ₂ → Δ ⊢ Γ₂ ≤Γ Γ₃ → Δ ⊢ Γ₁ ≤Γ Γ₃
    Γ-trans (Γ-≤ sp₁₂≤ regs₁₂≤) (Γ-≤ sp₂₃≤ regs₂₃≤) =
      Γ-≤ (σ-trans sp₁₂≤ sp₂₃≤) (regs-trans regs₁₂≤ regs₂₃≤)

    regs-trans : ∀ {Δ m} {τs₁ τs₂ τs₃ : Vec Type m} →
                   Allᵥ (λ { (τ₁ , τ₂) → Δ ⊢ τ₁ ≤τ τ₂ }) (Vec-zip τs₁ τs₂) →
                   Allᵥ (λ { (τ₂ , τ₃) → Δ ⊢ τ₂ ≤τ τ₃ }) (Vec-zip τs₂ τs₃) →
                   Allᵥ (λ { (τ₁ , τ₃) → Δ ⊢ τ₁ ≤τ τ₃ }) (Vec-zip τs₁ τs₃)
    regs-trans {τs₁ = []} {[]} {[]} [] [] = []
    regs-trans {τs₁ = τ₁ ∷ τs₁} {τ₂ ∷ τs₂} {τ₃ ∷ τs₃} (τ₁₂≤ ∷ τs₁₂≤)
      (τ₂₃≤ ∷ τs₂₃≤) = τ-trans τ₁₂≤ τ₂₃≤ ∷ regs-trans τs₁₂≤ τs₂₃≤

  mutual
    τ-valid : ∀ {Δ τ₁ τ₂} → Δ ⊢ τ₁ ≤τ τ₂ → Δ ⊢ τ₁ Type × Δ ⊢ τ₂ Type
    τ-valid (α⁼-≤ (valid-α⁼ l)) = valid-α⁼ l , valid-α⁼ l
    τ-valid int-≤ = valid-int , valid-int
    τ-valid ns-≤ = valid-ns , valid-ns
    τ-valid (∀-≤ Δ⋆ Γ≤) with Γ-valid Γ≤
    ... | Γ₁⋆ , Γ₂⋆ = valid-∀ Δ⋆ Γ₁⋆ , valid-∀ Δ⋆ Γ₂⋆
    τ-valid (tuple-≤ τs) with τs⁻-valid τs
    ... | τs₁⋆ , τs₂⋆ = (valid-tuple τs₁⋆) , valid-tuple τs₂⋆

    τ⁻-valid : ∀ {Δ τ⁻₁ τ⁻₂} → Δ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂ →
                               Δ ⊢ τ⁻₁ InitType × Δ ⊢ τ⁻₂ InitType
    τ⁻-valid (τ⁻-≤ τ≤) with τ-valid τ≤
    ... | τ⁻₁⋆ , τ⁻₂⋆ = valid-τ⁻ τ⁻₁⋆ , valid-τ⁻ τ⁻₂⋆

    τs⁻-valid :
      ∀ {Δ m} {τs₁ τs₂ : Vec InitType m} →
        Allᵥ (λ { (τ⁻₁ , τ⁻₂)  → Δ ⊢ τ⁻₁ ≤τ⁻ τ⁻₂ }) (Vec-zip τs₁ τs₂) →
        Allᵥ (λ τ⁻ → Δ ⊢ τ⁻ InitType) τs₁ ×
        Allᵥ (λ τ⁻ → Δ ⊢ τ⁻ InitType) τs₂
    τs⁻-valid {τs₁ = []} {[]} [] = [] , []
    τs⁻-valid {τs₁ = τ⁻₁ ∷ τs₁} {τ⁻₂ ∷ τs₂} (τ⁻≤ ∷ ps)
      with τ⁻-valid τ⁻≤ | τs⁻-valid ps
    ...   | τ⁻₁⋆ , τ⁻₂⋆ | τs₁⋆ , τs₂⋆ = τ⁻₁⋆ ∷ τs₁⋆ , τ⁻₂⋆ ∷ τs₂⋆

    σ-valid : ∀ {Δ σ₁ σ₂} → Δ ⊢ σ₁ ≤σ σ₂ →
                            Δ ⊢ σ₁ StackType ×
                            Δ ⊢ σ₂ StackType
    σ-valid (σ-≤ σ⋆) = σ⋆ , σ⋆

    Γ-valid : ∀ {Δ Γ₁ Γ₂} → Δ ⊢ Γ₁ ≤Γ Γ₂ →
                            Δ ⊢ Γ₁ RegisterAssignment ×
                            Δ ⊢ Γ₂ RegisterAssignment
    Γ-valid  (Γ-≤ sp≤ regs≤) with σ-valid sp≤ | regs-valid regs≤
    ... | sp₁⋆ , sp₂⋆ | regs₁⋆ , regs₂⋆ =
      valid-registerₐ sp₁⋆ regs₁⋆ , valid-registerₐ sp₂⋆ regs₂⋆

    regs-valid :
      ∀ {Δ m} {τs₁ τs₂ : Vec Type m} →
        Allᵥ (λ { (τ₁ , τ₂)  → Δ ⊢ τ₁ ≤τ τ₂ }) (Vec-zip τs₁ τs₂) →
        Allᵥ (λ τ → Δ ⊢ τ Type) τs₁ ×
        Allᵥ (λ τ → Δ ⊢ τ Type) τs₂
    regs-valid {τs₁ = []} {[]} [] = [] , []
    regs-valid {τs₁ = τ₁ ∷ τs₁} {τ₂ ∷ τs₂} (τ≤ ∷ τs≤)
      with τ-valid τ≤ | regs-valid τs≤
    ...   | τ₁⋆ , τ₂⋆ | τs₁⋆ , τs₂⋆ = τ₁⋆ ∷ τs₁⋆ , τ₂⋆ ∷ τs₂⋆

record Subtype {A Ctx : Set} (T : TypeLike A Ctx) : Set1 where
  constructor subtype
  field
    _⊢_≤_ : Ctx → A → A → Set
    _⊢_≤?_ : ∀ C v₁ v₂ → Dec (C ⊢ v₁ ≤ v₂)
    ≤-refl : ∀ {C v} → C ⊢ v Valid → C ⊢ v ≤ v
    ≤-trans : ∀ {C v₁ v₂ v₃} → C ⊢ v₁ ≤ v₂ → C ⊢ v₂ ≤ v₃ → C ⊢ v₁ ≤ v₃
    ≤-valid : ∀ {C v₁ v₂} → C ⊢ v₁ ≤ v₂ → C ⊢ v₁ Valid × C ⊢ v₂ Valid
open Subtype {{...}} public

Vec-subtype : ∀ {A Ctx t} {{_ : Subtype {A} {Ctx} t}} {m} →
                Subtype (Vec-typeLike {{t}} {m})
Vec-subtype {{t}} = subtype
    (λ C xs₁ xs₂ → Allᵥ (λ {(x₁ , x₂) → C ⊢ x₁ ≤ x₂ })
                        (Vec-zip xs₁ xs₂))
    (λ C xs₁ xs₂ → Allᵥ-dec (λ { (x₁ , x₂) → C ⊢ x₁ ≤? x₂ })
                            (Vec-zip xs₁ xs₂))
    (λ ps → Allᵥ-zip (Allᵥ-map (≤-refl {{t}}) ps))
    trans'
    valid
  where trans' : ∀ {A Ctx t} {{_ : Subtype t}} {m} →
                   {C : Ctx} {xs₁ xs₂ xs₃ : Vec A m} →
                   Allᵥ (λ { (x₁ , x₂) → C ⊢ x₁ ≤ x₂ }) (Vec-zip xs₁ xs₂) →
                   Allᵥ (λ { (x₂ , x₃) → C ⊢ x₂ ≤ x₃ }) (Vec-zip xs₂ xs₃) →
                   Allᵥ (λ { (x₁ , x₃) → C ⊢ x₁ ≤ x₃ }) (Vec-zip xs₁ xs₃)
        trans' {xs₁ = []} {[]} {[]} [] [] = []
        trans' {{t}} {xs₁ = x₁ ∷ xs₁} {x₂ ∷ xs₂} {x₃ ∷ xs₃} (x₁₂≤ ∷ xs₁₂≤)
          (x₂₃≤ ∷ xs₂₃≤) = (≤-trans {{t}} x₁₂≤ x₂₃≤) ∷ trans' xs₁₂≤ xs₂₃≤
        valid : ∀ {A Ctx t} {{_ : Subtype t}} {m} →
                  {C : Ctx} {xs₁ xs₂ : Vec A m} →
                  Allᵥ (λ { (x₁ , x₂) → C ⊢ x₁ ≤ x₂ }) (Vec-zip xs₁ xs₂) →
                  Allᵥ (λ { x₁ → C ⊢ x₁ Valid }) xs₁ ×
                  Allᵥ (λ { x₁ → C ⊢ x₁ Valid }) xs₂
        valid {xs₁ = []} {[]} [] = [] , []
        valid {{t}} {xs₁ = x₁ ∷ xs₁} {x₂ ∷ xs₂} (x≤ ∷ xs≤)
          with ≤-valid {{t}} x≤ | valid xs≤
        ... | x₁⋆ , x₂⋆ | xs₁⋆ , xs₂⋆ = x₁⋆ ∷ xs₁⋆ , x₂⋆ ∷ xs₂⋆

List-subtype : ∀ {A Ctx t} {{_ : Subtype {A} {Ctx} t}} →
                 Subtype (List-typeLike {{t}})
List-subtype {{t}} = subtype
    (λ C xs₁ xs₂ → length xs₁ ≡ length xs₂ ×
                   All (λ {(x₁ , x₂) → C ⊢ x₁ ≤ x₂ }) (zip xs₁ xs₂))
    (λ C xs₁ xs₂ → dec-inj₂ _,_ id
                            (length xs₁ ≟ length xs₂)
                            (All-dec (λ { (x₁ , x₂) → C ⊢ x₁ ≤? x₂ })
                                     (zip xs₁ xs₂)))
    (λ ps → refl , All-zip (All-map (≤-refl {{t}}) ps))
    trans'
    valid
  where trans' : ∀ {A Ctx t} {{_ : Subtype t}} →
                   {C : Ctx} {xs₁ xs₂ xs₃ : List A} →
                   length xs₁ ≡ length xs₂ ×
                     All (λ { (x₁ , x₂) → C ⊢ x₁ ≤ x₂ }) (zip xs₁ xs₂) →
                   length xs₂ ≡ length xs₃ ×
                     All (λ { (x₂ , x₃) → C ⊢ x₂ ≤ x₃ }) (zip xs₂ xs₃) →
                   length xs₁ ≡ length xs₃ ×
                     All (λ { (x₁ , x₃) → C ⊢ x₁ ≤ x₃ }) (zip xs₁ xs₃)
        trans' {xs₁ = []} {[]} {[]} (refl , []) (refl , []) = refl , []
        trans' {xs₁ = []} {_ ∷ _} {_} (() , _) _
        trans' {xs₁ = []} {_} {_ ∷ _} (eq₁₂ , _) (eq₂₃ , _)
          with trans eq₁₂ eq₂₃
        ... | ()
        trans' {xs₁ = _ ∷ _} {[]} {_} (() , _) _
        trans' {xs₁ = _ ∷ _} {_} {[]} (eq₁₂ , _) (eq₂₃ , _)
          with trans eq₁₂ eq₂₃
        ... | ()
        trans' {{t}} {xs₁ = x₁ ∷ xs₁} {x₂ ∷ xs₂} {x₃ ∷ xs₃}
          (eq₁₂ , x₁₂≤ ∷ xs₁₂≤) (eq₂₃ , x₂₃≤ ∷ xs₂₃≤) =
            (trans eq₁₂ eq₂₃) ,
            (≤-trans {{t}} x₁₂≤ x₂₃≤) ∷
              proj₂ (trans' (cancel-+-left 1 eq₁₂ , xs₁₂≤)
                            (cancel-+-left 1 eq₂₃ , xs₂₃≤))
        valid : ∀ {A Ctx t} {{_ : Subtype t}} →
                  {C : Ctx} {xs₁ xs₂ : List A} →
                  length xs₁ ≡ length xs₂ ×
                  All (λ { (x₁ , x₂) → C ⊢ x₁ ≤ x₂ }) (zip xs₁ xs₂) →
                  All (λ { x₁ → C ⊢ x₁ Valid }) xs₁ ×
                  All (λ { x₁ → C ⊢ x₁ Valid }) xs₂
        valid {xs₁ = []} {[]} (refl , []) = [] , []
        valid {xs₁ = []} {x₁ ∷ xs₂} (() , _)
        valid {xs₁ = x₁ ∷ xs₁} {[]} (() , _)
        valid {{t}} {xs₁ = x₁ ∷ xs₁} {x₂ ∷ xs₂} (eq , x≤ ∷ xs≤)
          with ≤-valid {{t}} x≤ | valid (cancel-+-left 1 eq , xs≤)
        ... | x₁⋆ , x₂⋆ | xs₁⋆ , xs₂⋆ = x₁⋆ ∷ xs₁⋆ , x₂⋆ ∷ xs₂⋆

instance
  Type-subtype : Subtype Type-typeLike
  Type-subtype = subtype _⊢_≤τ_ _⊢_≤τ?_ τ-refl τ-trans τ-valid

  Typevec-subType : ∀ {m} → Subtype (Typevec-typeLike {m})
  Typevec-subType = Vec-subtype

  Typelist-subType : Subtype Typelist-typeLike
  Typelist-subType = List-subtype

  InitType-subtype : Subtype InitType-typeLike
  InitType-subtype = subtype _⊢_≤τ⁻_ _⊢_≤τ⁻?_ τ⁻-refl τ⁻-trans τ⁻-valid

  InitTypevec-subType : ∀ {m} → Subtype (InitTypevec-typeLike {m})
  InitTypevec-subType = Vec-subtype

  InitTypelist-subType : Subtype InitTypelist-typeLike
  InitTypelist-subType = List-subtype

  StackType-subtype : Subtype StackType-typeLike
  StackType-subtype = subtype _⊢_≤σ_ _⊢_≤σ?_ σ-refl σ-trans σ-valid

  RegisterAssignment-subtype : Subtype RegisterAssignment-typeLike
  RegisterAssignment-subtype = subtype _⊢_≤Γ_ _⊢_≤Γ?_ Γ-refl Γ-trans Γ-valid
