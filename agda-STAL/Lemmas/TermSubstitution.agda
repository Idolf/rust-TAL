module Lemmas.TermSubstitution where

open import Util
open import Judgments
open import Lemmas.Equality using ()
open import Lemmas.Substitution
open import Lemmas.TypeSubstitution
open HighSyntax

-- The purpose of this file is to prove that
-- substitution is possible for instruction
-- sequences, and that result is valid.

private
  int-helper : ∀ {n} (♯r : Fin n) {pos θ τs₁ τs₂} →
                 τs₁ ⟦ θ / pos ⟧≡ τs₂ →
                 lookup ♯r τs₁ ≡ int →
                 lookup ♯r τs₂ ≡ int
  int-helper zero (subst-int ∷ sub-τs) refl = refl
  int-helper (suc ♯r) (sub-τ ∷ sub-τs) eq = int-helper ♯r sub-τs eq

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

  vval-subst : ∀ {ψ₁} Δ₁ Δ₂ {θ a σ₁ σ₂ τs₁ τs₂ v₁ τ₁} →
                 [] ⊢ ψ₁ Valid →
                 Δ₂ ⊢ θ of a instantiation →
                 τs₁ ⟦ θ / length Δ₁ ⟧≡ τs₂ →
                 ψ₁ , Δ₁ ++ a ∷ Δ₂ ⊢ v₁ of registerₐ σ₁ τs₁ ⇒ τ₁ vval →
                 ∃₂ λ v₂ τ₂ →
                   v₁ ⟦ θ / length Δ₁ ⟧≡ v₂ ×
                   τ₁ ⟦ θ / length Δ₁ ⟧≡ τ₂ ×
                   ψ₁ , Δ₁ ++ Δ₂ ⊢ v₂ of registerₐ σ₂ τs₂ ⇒ τ₂ vval
  vval-subst Δ₁ Δ₂ {v₁ = reg ♯r} ψ₁⋆ θ⋆ sub-τs of-reg
    = _ , _ , subst-reg , allzipᵥ-lookup ♯r sub-τs , of-reg
  vval-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-τs (of-globval l)
    = _ , _ , subst-globval , subst-outside-ctx (All-lookup l ψ₁⋆) , of-globval l
  vval-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-τs of-int
    = _ , _ , subst-int , subst-int , of-int
  vval-subst Δ₁ Δ₂ {a = a} {v₁ = Λ Δₒ ∙ v₁ ⟦ θs₁ ⟧} ψ₁⋆ θ⋆ sub-τs (of-Λ {Δ₁ = Δᵢ} .{Δ₂ = Δₒ} {Γ₁ = Γᵢ₁} {Γ₂ = Γₒ₁} v₁⋆ θs₁⋆ subs₁-Γ)
    rewrite sym (List-++-assoc Δₒ Δ₁ (a ∷ Δ₂))
    with θs-subst (Δₒ ++ Δ₁) Δ₂ θ⋆ {θs₁} {Δᵢ} θs₁⋆
  ... | θs₂ , sub-θs , θs₂⋆
    rewrite List-length-++ Δₒ {Δ₁}
          | List-++-assoc Δₒ Δ₁ Δ₂
    with vval-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-τs v₁⋆
  ... | v₂ , ∀[ .Δᵢ ] Γᵢ₂ , sub-v , subst-∀ sub-Γᵢ , v₂⋆
    with weaken-subst (length Δₒ) (m≤m+n (length Δᵢ) (length Δ₁)) sub-Γᵢ
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

  instruction-subst : ∀ {ψ₁} Δ₁ Δ₂ {θ a σ₁ σ₂ τs₁ τs₂} →
                        [] ⊢ ψ₁ Valid →
                        Δ₂ ⊢ θ of a instantiation →
                        σ₁ ⟦ θ / length Δ₁ ⟧≡ σ₂ →
                        τs₁ ⟦ θ / length Δ₁ ⟧≡ τs₂ →
                        ∀ {ι₁ σᵣ₁ τsᵣ₁} →
                        ψ₁ , Δ₁ ++ a ∷ Δ₂ ⊢ ι₁ of registerₐ σ₁ τs₁ ⇒ registerₐ σᵣ₁ τsᵣ₁ instruction →
                        ∃ λ ι₂ → ∃₂ λ σᵣ₂ τsᵣ₂ →
                             ι₁   ⟦ θ / length Δ₁ ⟧≡ ι₂ ×
                             σᵣ₁  ⟦ θ / length Δ₁ ⟧≡ σᵣ₂ ×
                             τsᵣ₁ ⟦ θ / length Δ₁ ⟧≡ τsᵣ₂ ×
                             ψ₁ , Δ₁ ++ Δ₂ ⊢ ι₂ of registerₐ σ₂ τs₂ ⇒ registerₐ σᵣ₂ τsᵣ₂ instruction

  instruction-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-σ sub-τs {add ♯rd ♯rs v} (of-add eq v⋆)
    with vval-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-τs v⋆
  ... | v' , int , sub-v , subst-int , v'⋆
    = , , , subst-add sub-v , sub-σ , allzipᵥ-update ♯rd subst-int sub-τs , of-add (int-helper ♯rs sub-τs eq) v'⋆

  instruction-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-σ sub-τs {sub ♯rd ♯rs v} (of-sub eq v⋆)
    with vval-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-τs v⋆
  ... | v' , int , sub-v , subst-int , v'⋆
    = , , , subst-sub sub-v , sub-σ , allzipᵥ-update ♯rd subst-int sub-τs , of-sub (int-helper ♯rs sub-τs eq) v'⋆

  instruction-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-σ sub-τs {salloc n} of-salloc
    = , , , subst-salloc , help n sub-σ , sub-τs , of-salloc
      where help : ∀ n {pos θ σ σ'} →
                     σ ⟦ θ / pos ⟧≡ σ' →
                     stack-append (replicate n uninit) σ ⟦ θ / pos ⟧≡ stack-append (replicate n uninit) σ'
            help zero sub-σ = sub-σ
            help (suc n) sub-σ = subst-uninit ∷ help n sub-σ

  instruction-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-σ sub-τs {sfree n} (of-sfree drop)
    with subst-stack-drop drop sub-σ
  ... | _ , drop' , sub-σ'
    = , , , subst-sfree , sub-σ' , sub-τs , of-sfree drop'

  instruction-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-σ sub-τs {sld ♯rd i} (of-sld l)
    with subst-stack-lookup l sub-σ
  ... | τ' , l' , sub-τ
    = , , , subst-sld , sub-σ , allzipᵥ-update ♯rd sub-τ sub-τs , of-sld l'

  instruction-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-σ sub-τs {sst i ♯rs} (of-sst up)
    with subst-stack-update up (allzipᵥ-lookup ♯rs sub-τs) sub-σ
  ... | sp' , up' , sub-σ'
    = , , , subst-sst , sub-σ' , sub-τs , of-sst up'

  instruction-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-σ sub-τs {ld ♯rd ♯rs i} (of-ld eq l)
    with allzipᵥ-lookup ♯rs sub-τs
  ... | sub-tuple
    rewrite eq
    with subst-tuple-helper sub-tuple
  ... | τs⁻' , eq' , sub-τs⁻
    with allzip-lookup₁ l sub-τs⁻
  ... | (τ' , init) , l' , subst-τ⁻ sub-τ
    = , , , subst-ld , sub-σ , allzipᵥ-update ♯rd sub-τ sub-τs , of-ld eq' l'

  instruction-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-σ sub-τs {st ♯rd i ♯rs} (of-st eq lookup≤τ l up)
    with allzipᵥ-lookup ♯rd sub-τs
  ... | sub-tuple
    rewrite eq
    with subst-tuple-helper sub-tuple
  ... | τs⁻₂ , eq' , sub-τs⁻
    with subtype-subst-exists Δ₁ θ⋆ lookup≤τ
  ... | lookup' , τ' , sub-lookup , sub-τ , lookup'≤τ'
    with allzip-update₁ up (subst-τ⁻ sub-τ) sub-τs⁻
  ... | τs⁻₂' , up' , sub-τs⁻'
    with allzip-lookup₁ l sub-τs⁻
  ... | (τ'' , φ) , l' , (subst-τ⁻ sub-τ')
    rewrite subst-unique sub-lookup (allzipᵥ-lookup ♯rs sub-τs)
          | subst-unique sub-τ sub-τ'
    = , , , subst-st , sub-σ , allzipᵥ-update ♯rd (subst-tuple sub-τs⁻') sub-τs , of-st eq' lookup'≤τ' l' up'

  instruction-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-σ sub-τs {malloc ♯rd τs} (of-malloc τs⋆)
    with valid-subst-exists Δ₁ θ⋆ τs⋆
  ... | τs' , sub-τs' , τs'⋆
    = , , , subst-malloc sub-τs' , sub-σ , allzipᵥ-update ♯rd (subst-tuple (AllZip-map' _ _ subst-τ⁻ sub-τs')) sub-τs , of-malloc τs'⋆

  instruction-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-σ sub-τs {mov ♯rd v} (of-mov v⋆)
    with vval-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-τs v⋆
  ... | v' , τ' , sub-v , sub-τ , v'⋆
    = , , , subst-mov sub-v , sub-σ , allzipᵥ-update ♯rd sub-τ sub-τs , of-mov v'⋆

  instruction-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-σ sub-τs {beq ♯r v} (of-beq eq v⋆ Γ≤Γ')
    with vval-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-τs v⋆
  ... | v' , ∀[ [] ] Γ' , sub-v , subst-∀ sub-Γᵢ , v'⋆
    = , , , subst-beq sub-v , sub-σ , sub-τs , of-beq (int-helper ♯r sub-τs eq) v'⋆ (subtype-subst Δ₁ θ⋆ Γ≤Γ' (subst-registerₐ sub-σ sub-τs) sub-Γᵢ)

  instructionsequence-subst : ∀ {ψ₁} Δ₁ Δ₂ {θ a Γ₁ Γ₂} →
                                [] ⊢ ψ₁ Valid →
                                Δ₂ ⊢ θ of a instantiation →
                                Γ₁ ⟦ θ / length Δ₁ ⟧≡ Γ₂ →
                                ∀ {I₁} →
                                ψ₁ , Δ₁ ++ a ∷ Δ₂ ⊢ I₁ of Γ₁ instructionsequence →
                                ∃ λ I₂ →
                                   I₁ ⟦ θ / length Δ₁ ⟧≡ I₂ ×
                                   ψ₁ , Δ₁ ++ Δ₂ ⊢ I₂ of Γ₂ instructionsequence
  instructionsequence-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ (subst-registerₐ sub-σ sub-τs) (of-~> {Γ' = registerₐ σ' τs'} ι₁⋆ I₁⋆)
    with instruction-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-σ sub-τs ι₁⋆
  ... | ι₂ , σₘ , τsₘ , sub-ι , sub-σₘ , sub-τsₘ , ι₂⋆
    with instructionsequence-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ (subst-registerₐ sub-σₘ sub-τsₘ) I₁⋆
  ... | I₂ , sub-I , I₂⋆
    = _ , subst-~> sub-ι sub-I , of-~> ι₂⋆ I₂⋆
  instructionsequence-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ (subst-registerₐ sub-σ sub-τs) (of-jmp v₁⋆ Γ₁≤Γ₁')
    with vval-subst Δ₁ Δ₂ ψ₁⋆ θ⋆ sub-τs v₁⋆
  ... | v₂ , ∀[ [] ] Γ₂' , sub-v , subst-∀ sub-Γ' , v₂⋆
    = _ , subst-jmp sub-v , of-jmp v₂⋆ (subtype-subst Δ₁ θ⋆ Γ₁≤Γ₁' (subst-registerₐ sub-σ sub-τs) sub-Γ')
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
