module ForgetMe where

open import Util
open import Judgments
open import Lemmas
open import TermSubtyping

instantiation-weaken : ∀ {Δ₁} Δ₂ {i a} →
                         Δ₁ ⊢ i of a instantiation →
                         Δ₁ ++ Δ₂ ⊢ i of a instantiation
instantiation-weaken Δ₂ (of-α τ⋆) = of-α (valid-++ τ⋆)
instantiation-weaken Δ₂ (of-ρ σ⋆) = of-ρ (valid-++ σ⋆)

instantiations-weaken : ∀ {Δ₁} Δ₂ {is Δ} →
                          Δ₁ ⊢ is of Δ instantiations →
                          Δ₁ ++ Δ₂ ⊢ is of Δ instantiations
instantiations-weaken Δ₂ [] = []
instantiations-weaken {Δ₁} Δ₂ (_∷_ {Δ' = Δ'} i⋆ is⋆)
  with instantiation-weaken Δ₂ i⋆
... | i⋆'
  rewrite List-++-assoc Δ' Δ₁ Δ₂
    = i⋆' ∷ instantiations-weaken Δ₂ is⋆

vval-weaken : ∀ {ψ₁ Δ₁} Δ₂ {Γ v τ} →
                ψ₁ , Δ₁ , Γ ⊢ v of τ vval →
                ψ₁ , Δ₁ ++ Δ₂ , Γ ⊢ v of τ vval
vval-weaken Δ₂ of-reg = of-reg
vval-weaken Δ₂ (of-globval l) = of-globval l
vval-weaken Δ₂ of-int = of-int
vval-weaken Δ₂ of-ns = of-ns
vval-weaken {Δ₁ = Δ₁} Δ₂ (of-Λ {Δ₂ = Δ₂'} v⋆ is⋆ subs-Γ)
  with instantiations-weaken Δ₂ is⋆
... | is⋆'
  rewrite List-++-assoc Δ₂' Δ₁ Δ₂ =
    of-Λ (vval-weaken Δ₂ v⋆) is⋆' subs-Γ

instruction-weaken : ∀ {ψ₁ Δ₁} Δ₂ {ι Γ Γ'} →
                       ψ₁ , Δ₁ , Γ ⊢ ι ⇒ Γ' instruction →
                       ψ₁ , Δ₁ ++ Δ₂ , Γ ⊢ ι ⇒ Γ' instruction
instruction-weaken Δ₂ (of-add eq v⋆) = of-add eq (vval-weaken Δ₂ v⋆)
instruction-weaken Δ₂ (of-sub eq v⋆) = of-sub eq (vval-weaken Δ₂ v⋆)
instruction-weaken Δ₂ of-salloc = of-salloc
instruction-weaken Δ₂ (of-sfree drop) = of-sfree drop
instruction-weaken Δ₂ (of-sld l) = of-sld l
instruction-weaken Δ₂ (of-sst up) = of-sst up
instruction-weaken Δ₂ (of-ld eq l) = of-ld eq l
instruction-weaken Δ₂ (of-st eq lookup≤τ l up) = of-st eq (≤-++ lookup≤τ) l up
instruction-weaken Δ₂ (of-malloc τs⋆) = of-malloc (valid-++ τs⋆)
instruction-weaken Δ₂ (of-mov v⋆) = of-mov (vval-weaken Δ₂ v⋆)
instruction-weaken Δ₂ (of-beq eq v⋆ Γ≤Γ') = of-beq eq (vval-weaken Δ₂ v⋆) (≤-++ Γ≤Γ')

instructionsequence-weaken' : ∀ {ψ₁ Δ₁} Δ₂ {Γ I} →
                                ψ₁ , Δ₁ , Γ ⊢ I instructionsequence →
                                ψ₁ , Δ₁ ++ Δ₂ , Γ ⊢ I instructionsequence
instructionsequence-weaken' Δ₂ (of-~> ι⋆ I⋆)
  with instruction-weaken Δ₂ ι⋆
... | ι⋆'
  = of-~> ι⋆' (instructionsequence-weaken' Δ₂ I⋆)
instructionsequence-weaken' Δ₂ (of-jmp v⋆ Γ≤Γ') = of-jmp (vval-weaken Δ₂ v⋆) (≤-++ Γ≤Γ')

instructionsequence-weaken : ∀ {ψ₁ Δ₁} Δ₂ {Γ I} →
                               Δ₁ ⊢ Γ Valid →
                               ψ₁ , Δ₁ , Γ ⊢ I instructionsequence →
                               ψ₁ , Δ₁ ++ Δ₂ , weaken (length Δ₁) (length Δ₂) Γ ⊢ I instructionsequence
instructionsequence-weaken {ψ₁} {Δ₁} Δ₂ {Γ} {I} Γ⋆ I⋆
  with instructionsequence-weaken' Δ₂ I⋆
... | I⋆' = subst (λ Γ → ψ₁ , Δ₁ ++ Δ₂ , Γ ⊢ I instructionsequence) (sym (weaken-outside-ctx-0 (length Δ₂) Γ⋆)) I⋆'

lookup-subst : ∀ {n} {regs regs' : Vec Type n} {i} ♯r →
                 regs ⟦ i / 0 ⟧≡ regs' →
                 lookup ♯r regs ⟦ i / 0 ⟧≡ lookup ♯r regs'
lookup-subst zero (sub-w ∷ sub-regs) = sub-w
lookup-subst (suc ♯r) (sub-w ∷ sub-regs) = lookup-subst ♯r sub-regs

instantiations-length : ∀ {Δ₁ is Δ₂} →
                          Δ₁ ⊢ is of Δ₂ instantiations →
                          length is ≡ length Δ₂
instantiations-length [] = refl
instantiations-length (i⋆ ∷ is⋆) = cong suc (instantiations-length is⋆)

instantiation-subst : ∀ {Δ i a i₁ i₂ a'} Δₑ →
                        Δ ⊢ i of a instantiation →
                        i₁ ⟦ i / length Δₑ ⟧≡ i₂ →
                        Δₑ ++ a ∷ Δ ⊢ i₁ of a' instantiation →
                        Δₑ ++ Δ ⊢ i₂ of a' instantiation
instantiation-subst Δₑ i⋆ (subst-α sub-τ) (of-α τ⋆) = of-α (valid-subst Δₑ i⋆ τ⋆ sub-τ )
instantiation-subst Δₑ i⋆ (subst-ρ sub-σ) (of-ρ σ⋆) = of-ρ (valid-subst Δₑ i⋆ σ⋆ sub-σ)

instantiations-subst : ∀ {Δ i a is is'} Δₒ {Δᵢ} →
                         Δ ⊢ i of a instantiation →
                         is ⟦ i / length Δₒ ⟧≡ is' →
                         Δₒ ++ a ∷ Δ ⊢ is of Δᵢ instantiations →
                         Δₒ ++ Δ ⊢ is' of Δᵢ instantiations
instantiations-subst Δₒ i⋆ [] [] = []
instantiations-subst {Δ} {a = a} Δₒ i⋆ (sub-i ∷ sub-is) (_∷_ {Δ' = Δ'} i'⋆ is⋆)
  rewrite instantiations-length is⋆
        | sym (List-length-++ Δ' {Δₒ})
        | sym (List-++-assoc Δ' Δₒ (a ∷ Δ))
  with instantiation-subst (Δ' ++ Δₒ) i⋆ sub-i i'⋆
... | i''⋆
   rewrite List-++-assoc Δ' Δₒ Δ
    = i''⋆ ∷ instantiations-subst Δₒ i⋆ sub-is is⋆

{-# TERMINATING #-}
subst-helper : ∀ {Δ Δᵢ} Δₒ {Γᵢ Γᵢ' Γₒ Γₒ' : RegisterAssignment} {i a is is'} →
                 Δ ⊢ i of a instantiation →
                 Δₒ ++ a ∷ Δ ⊢ is of Δᵢ instantiations →
                 Δᵢ ++ a ∷ Δ ⊢ Γᵢ Valid →
                 is ⟦ i / length Δₒ ⟧≡ is' →
                 Γₒ ⟦ i / length Δₒ ⟧≡ Γₒ' →
                 Γᵢ ⟦ i / length Δᵢ ⟧≡ Γᵢ' →
                 weaken (length Δᵢ) (length Δₒ) Γᵢ ⟦ is / 0 ⟧many≡ Γₒ →
                 weaken (length Δᵢ) (length Δₒ) Γᵢ' ⟦ is' / 0 ⟧many≡ Γₒ'
subst-helper Δₒ i⋆ [] Γᵢ⋆ sub-is Γₒ₁ Γᵢ₁ subs-Γ = subst-helper Δₒ i⋆ [] Γᵢ⋆ sub-is Γₒ₁ Γᵢ₁ subs-Γ
subst-helper Δₒ i⋆ (x ∷ is⋆) Γᵢ⋆ sub-is Γₒ₁ Γᵢ₁ subs-Γ = subst-helper Δₒ i⋆ (x ∷ is⋆) Γᵢ⋆ sub-is Γₒ₁ Γᵢ₁ subs-Γ

vval-subst : ∀ {ψ₁ a Δ i Γ Γ' v v' τ τ'} →
               [] ⊢ ψ₁ Valid →
               a ∷ Δ ⊢ Γ Valid →
               Δ ⊢ i of a instantiation →
               Γ ⟦ i / 0 ⟧≡ Γ' →
               v ⟦ i / 0 ⟧≡ v' →
               τ ⟦ i / 0 ⟧≡ τ' →
               ψ₁ , a ∷ Δ , Γ ⊢ v of τ vval →
               ψ₁ , Δ , Γ' ⊢ v' of τ' vval
vval-subst {v = reg ♯r} ψ₁⋆ Γ⋆ i⋆ (subst-registerₐ sub-sp sub-regs) subst-reg sub-τ of-reg
  rewrite subst-unique sub-τ (lookup-subst ♯r sub-regs) = of-reg
vval-subst ψ₁⋆ Γ⋆ i⋆ sub-Γ subst-globval sub-τ (of-globval l)
  with All-lookup l ψ₁⋆
... | τ⋆
  rewrite subst-unique sub-τ (subst-outside-ctx τ⋆)
    = of-globval l
vval-subst ψ₁⋆ Γ⋆ i⋆ sub-Γ subst-int subst-int of-int = of-int
vval-subst ψ₁⋆ Γ⋆ i⋆ sub-Γ subst-ns subst-ns of-ns = of-ns
vval-subst {ψ₁} {a} {Δ} {i} {Γᵥ} {Γᵥ'} {v = Λ Δₒ ∙ v ⟦ is ⟧} {Λ .Δₒ ∙ v' ⟦ is' ⟧} {∀[ .Δₒ ] Γₒ} {∀[ .Δₒ ] Γₒ'} ψ₁⋆ Γ⋆ i⋆ sub-Γᵥ (subst-Λ sub-v sub-is) (subst-∀ sub-Γₒ) (of-Λ {Δ₁ = Δᵢ} {Γ₁ = Γᵢ} v⋆ is⋆ subs-Γ)
  with vval-valid-type ψ₁⋆ Γ⋆ v⋆
... | valid-∀ Γᵢ⋆
  with valid-subst-exists {{RegisterAssignment-TypeSubstitution}} Δᵢ i⋆ Γᵢ⋆
... | Γᵢ' , sub-Γᵢ , Γᵢ'⋆
  with subst (λ ι → Γᵢ ⟦ i / ι ⟧≡ Γᵢ') (+-comm 0 (length Δᵢ)) sub-Γᵢ
... | sub-Γᵢ'
  with vval-subst ψ₁⋆ Γ⋆ i⋆ sub-Γᵥ sub-v (subst-∀ sub-Γᵢ') v⋆
... | v'⋆
  rewrite +-comm (length Δₒ) 0
  with instantiations-subst Δₒ i⋆ sub-is is⋆
... | is'⋆
  with subst-helper Δₒ i⋆ is⋆ Γᵢ⋆ sub-is sub-Γₒ sub-Γᵢ subs-Γ
... | subs-Γ' = of-Λ v'⋆ is'⋆ subs-Γ'


{-# TERMINATING #-}
instruction-subst : ∀ {ψ₁ a Δ i Γ₁ Γ₁' Γ₂ Γ₂' ι ι'} →
                      [] ⊢ ψ₁ Valid →
                      a ∷ Δ ⊢ Γ₁ Valid →
                      Δ ⊢ i of a instantiation →
                      Γ₁ ⟦ i / 0 ⟧≡ Γ₁' →
                      Γ₂ ⟦ i / 0 ⟧≡ Γ₂' →
                      ι ⟦ i / 0 ⟧≡ ι' →
                      ψ₁ , a ∷ Δ , Γ₁ ⊢ ι ⇒ Γ₂ instruction →
                      ψ₁ , Δ , Γ₁' ⊢ ι' ⇒ Γ₂' instruction
instruction-subst ψ₁⋆ Γ₁⋆ i⋆ sub-Γ₁ sub-Γ₂ (subst-add sub-v) (of-add eq v⋆) = instruction-subst ψ₁⋆ Γ₁⋆ i⋆ sub-Γ₁ sub-Γ₂ (subst-add sub-v) (of-add eq v⋆)
instruction-subst ψ₁⋆ Γ₁⋆ i⋆ sub-Γ₁ sub-Γ₂ (subst-sub sub-v) (of-sub eq v⋆) = instruction-subst ψ₁⋆ Γ₁⋆ i⋆ sub-Γ₁ sub-Γ₂ (subst-sub sub-v) (of-sub eq v⋆)
instruction-subst ψ₁⋆ Γ₁⋆ i⋆ sub-Γ₁ sub-Γ₂ subst-salloc of-salloc = instruction-subst ψ₁⋆ Γ₁⋆ i⋆ sub-Γ₁ sub-Γ₂ subst-salloc of-salloc
instruction-subst ψ₁⋆ Γ₁⋆ i⋆ sub-Γ₁ sub-Γ₂ subst-sfree (of-sfree drop) = instruction-subst ψ₁⋆ Γ₁⋆ i⋆ sub-Γ₁ sub-Γ₂ subst-sfree (of-sfree drop)
instruction-subst ψ₁⋆ Γ₁⋆ i⋆ sub-Γ₁ sub-Γ₂ subst-sld (of-sld l) = instruction-subst ψ₁⋆ Γ₁⋆ i⋆ sub-Γ₁ sub-Γ₂ subst-sld (of-sld l)
instruction-subst ψ₁⋆ Γ₁⋆ i⋆ sub-Γ₁ sub-Γ₂ subst-sst (of-sst up) = instruction-subst ψ₁⋆ Γ₁⋆ i⋆ sub-Γ₁ sub-Γ₂ subst-sst (of-sst up)
instruction-subst ψ₁⋆ Γ₁⋆ i⋆ sub-Γ₁ sub-Γ₂ subst-ld (of-ld eq l) = instruction-subst ψ₁⋆ Γ₁⋆ i⋆ sub-Γ₁ sub-Γ₂ subst-ld (of-ld eq l)
instruction-subst ψ₁⋆ Γ₁⋆ i⋆ sub-Γ₁ sub-Γ₂ subst-st (of-st eq lookup≤τ l up) = instruction-subst ψ₁⋆ Γ₁⋆ i⋆ sub-Γ₁ sub-Γ₂ subst-st (of-st eq lookup≤τ l up)
instruction-subst ψ₁⋆ Γ₁⋆ i⋆ sub-Γ₁ sub-Γ₂ (subst-malloc sub-τs) (of-malloc τs⋆) = instruction-subst ψ₁⋆ Γ₁⋆ i⋆ sub-Γ₁ sub-Γ₂ (subst-malloc sub-τs) (of-malloc τs⋆)
instruction-subst ψ₁⋆ Γ₁⋆ i⋆ sub-Γ₁ sub-Γ₂ (subst-mov sub-v) (of-mov v⋆) = instruction-subst ψ₁⋆ Γ₁⋆ i⋆ sub-Γ₁ sub-Γ₂ (subst-mov sub-v) (of-mov v⋆)
instruction-subst ψ₁⋆ Γ₁⋆ i⋆ sub-Γ₁ sub-Γ₁' (subst-beq sub-v) (of-beq eq v⋆ Γ₁≤Γ₂) = instruction-subst ψ₁⋆ Γ₁⋆ i⋆ sub-Γ₁ sub-Γ₁' (subst-beq sub-v) (of-beq eq v⋆ Γ₁≤Γ₂)
--   with subtype-subst-exists [] i⋆ Γ₁≤Γ₂
-- ... | Γ₁' , Γ₂' , sub-Γ₁'' , sub-Γ₂ , Γ₁'≤Γ₂'
--   rewrite subst-unique sub-Γ₁  sub-Γ₁''
--         | subst-unique sub-Γ₁' sub-Γ₁''
--       = of-beq {!!} (vval-subst ψ₁⋆ Γ₁⋆ i⋆ sub-Γ₁'' sub-v (subst-∀ sub-Γ₂) v⋆) Γ₁'≤Γ₂'

instructionsequence-subst : ∀ {ψ₁ a Δ i Γ Γ' I I'} →
                              [] ⊢ ψ₁ Valid →
                              a ∷ Δ ⊢ Γ Valid →
                              Δ ⊢ i of a instantiation →
                              Γ ⟦ i / 0 ⟧≡ Γ' →
                              I ⟦ i / 0 ⟧≡ I' →
                              ψ₁ , a ∷ Δ , Γ ⊢ I instructionsequence →
                              ψ₁ , Δ , Γ' ⊢ I' instructionsequence
instructionsequence-subst ψ₁⋆ Γ⋆ i⋆ sub-Γ₁ (subst-~> sub-ι sub-I) (of-~> ι⋆ I⋆)
  with valid-subst-exists [] i⋆ (instruction-valid-type ψ₁⋆ Γ⋆ ι⋆)
... | Γ₂' , sub-Γ₂ , Γ₂'⋆
  with instruction-subst ψ₁⋆ Γ⋆ i⋆ sub-Γ₁ sub-Γ₂ sub-ι ι⋆
... | ι'⋆
  with instructionsequence-subst ψ₁⋆ (instruction-valid-type ψ₁⋆ Γ⋆ ι⋆) i⋆ sub-Γ₂ sub-I I⋆
... | I'⋆
  = of-~> ι'⋆ I'⋆
instructionsequence-subst ψ₁⋆ Γ⋆ i⋆ sub-Γ₁ (subst-jmp sub-v) (of-jmp v⋆ Γ₁≤Γ₂)
  with subtype-subst-exists [] i⋆ Γ₁≤Γ₂
... | Γ₁' , Γ₂' , sub-Γ₁' , sub-Γ₂ , Γ₁'≤Γ₂'
  rewrite subst-unique sub-Γ₁ sub-Γ₁'
    = of-jmp (vval-subst ψ₁⋆ Γ⋆ i⋆ sub-Γ₁' sub-v (subst-∀ sub-Γ₂) v⋆) Γ₁'≤Γ₂'

instructionsequence-subst-many : ∀ {ψ₁ Δ₁ Δ₂ is Γ Γ' I I'} →
                                   [] ⊢ ψ₁ Valid →
                                   Δ₁ ++ Δ₂ ⊢ Γ Valid →
                                   Δ₂ ⊢ is of Δ₁ instantiations →
                                   Γ ⟦ is / 0 ⟧many≡ Γ' →
                                   I ⟦ is / 0 ⟧many≡ I' →
                                   ψ₁ , Δ₁ ++ Δ₂ , Γ ⊢ I instructionsequence →
                                   ψ₁ , Δ₂ , Γ' ⊢ I' instructionsequence
instructionsequence-subst-many ψ₁⋆ Γ⋆ [] [] [] I⋆ = I⋆
instructionsequence-subst-many ψ₁⋆ Γ⋆ (i⋆ ∷ is⋆) (sub-Γ ∷ subs-Γ) (sub-I ∷ subs-I) I⋆
  with instructionsequence-subst ψ₁⋆ Γ⋆ i⋆ sub-Γ sub-I I⋆
... | I'⋆
  with instructionsequence-subst-many ψ₁⋆ (valid-subst [] i⋆ Γ⋆ sub-Γ) is⋆ subs-Γ subs-I I'⋆
... | I''⋆ = I''⋆

heap-length : ∀ {ψ₁ H ψ₂} →
                ψ₁ ⊢ H of ψ₂ heap →
                length H ≡ length ψ₂
heap-length (of-heap τs⋆) = AllZip-length τs⋆

≤∀⇒≡∀ : ∀ {τ Δ Δ' Γ'} →
          Δ ⊢ τ ≤ ∀[ Δ' ] Γ' →
          ∃ λ Γ →
            τ ≡ ∀[ Δ' ] Γ ×
            Δ' ++ Δ ⊢ Γ' ≤ Γ
≤∀⇒≡∀ (∀-≤ Γ'≤Γ) = _ , refl , Γ'≤Γ

-- wval-strict : ∀ {ψ₁ ψ₂ w τ} →
--                 ψ₁ , ψ₂ ⊢ w of τ wval →
--                 ∃ λ τᵣ →
--                   ψ₁ , ψ₂ ⊢ w of τᵣ wval ×
--                   (∀ {τ} → ψ₁ , ψ₂ ⊢ w of τ wval → [] ⊢ τᵣ ≤ τ)
-- wval-strict {ψ₁} {ψ₂} {globval ♯l} {τ} (of-globval {τ₁ = τᵣ} l τᵣ≤τ) = τᵣ , of-globval l (≤-refl (proj₁ (≤-valid τᵣ≤τ))) , help
--   where help : ∀ {τ} →
--                   ψ₁ , ψ₂ ⊢ globval ♯l of τ wval →
--                   [] ⊢ τᵣ ≤ τ
--         help (of-globval l' τᵣ≤τ')
--           rewrite ↓-unique l' l = τᵣ≤τ'
-- wval-strict {ψ₁} {ψ₂} {heapval ♯l} {τ} (of-heapval {τ₁ = τᵣ} l τᵣ≤τ) = τᵣ , of-heapval l (≤-refl (proj₁ (≤-valid τᵣ≤τ))) , help
--   where help : ∀ {τ} →
--                   ψ₁ , ψ₂ ⊢ heapval ♯l of τ wval →
--                   [] ⊢ τᵣ ≤ τ
--         help (of-heapval l' τᵣ≤τ')
--           rewrite ↓-unique l' l = τᵣ≤τ'
-- wval-strict {ψ₁} {ψ₂} {int i} of-int = int , of-int , help
--   where help : ∀ {τ} →
--                  ψ₁ , ψ₂ ⊢ int i of τ wval →
--                  [] ⊢ int ≤ τ
--         help of-int = int-≤
-- wval-strict {ψ₁} {ψ₂} {ns} of-ns = ns , of-ns , help
--   where help : ∀ {τ} →
--                  ψ₁ , ψ₂ ⊢ ns of τ wval →
--                  [] ⊢ ns ≤ τ
--         help of-ns = ns-≤
-- wval-strict {ψ₁} {ψ₂} {Λ Δ₂ ∙ w ⟦ is ⟧} {∀[ .Δ₂ ] Γ} (of-Λ {Δ₁ = Δ₁} .{Δ₂} w⋆ is⋆ subs-Γ)
--   with wval-strict w⋆
-- ... | τᵣ , τᵣ⋆ , func
--   with func w⋆
-- ... | τᵣ≤∀
--   with ≤∀⇒≡∀ τᵣ≤∀
-- ... | Γᵢᵣ , eq , Γ≤Γᵢᵣ
--   rewrite eq
--         | List-++-right-identity Δ₁
--   with valid-++ {Δ' = Δ₂} (proj₂ (≤-valid Γ≤Γᵢᵣ))
-- ... | Γᵢᵣ⋆
--   with valid-subst-exists-many [] is⋆ (subst₂ _⊢_Valid refl (sym (weaken-outside-ctx-0 (length Δ₂) (proj₂ (≤-valid Γ≤Γᵢᵣ)))) Γᵢᵣ⋆)
-- ... | Γₒᵣ , subs-Γᵣ , Γᵣ⋆
--   = ∀[ Δ₂ ] Γₒᵣ , of-Λ τᵣ⋆ is⋆ subs-Γᵣ , help
--     where help : ∀ {τ} →
--                     ψ₁ , ψ₂ ⊢ Λ Δ₂ ∙ w ⟦ is ⟧ of τ wval →
--                     [] ⊢ ∀[ Δ₂ ] Γₒᵣ ≤ τ
--           help (of-Λ {Γ₁ = Γ₁} {Γ₂} w⋆' is⋆ subs-Γ)
--             with func w⋆'
--           ... | ∀-≤ Γ₁≤Γᵢᵣ
--             with subtype-weaken Δ₁ Δ₂ [] Γ₁≤Γᵢᵣ
--           ... | Γ₁'≤Γᵢᵣ'
--             rewrite List-++-right-identity Δ₂
--             with subtype-subst-many {{RegisterAssignment-SubtypeSubstitution}} [] is⋆ Γ₁'≤Γᵢᵣ' subs-Γ subs-Γᵣ
--           ... | Γ₂≤Γₒᵣ
--             = ∀-≤ (≤-++ Γ₂≤Γₒᵣ)
