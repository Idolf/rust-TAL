module ForgetMe where

open import Util
open import Judgments
open import Lemmas
open import TermSubtyping
open import TermSubstitution

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

instantiation-subst-exist : ∀ Δ₁ {Δ₂ i a i₁ i₂ a'} Δₑ →
                              Δ₂ ⊢ i of a instantiation →
                              Δ₁ ++ a ∷ Δ₂ ⊢ i₁ of a' instantiation →


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
  with instantiation-subst (Δ' ++ Δₒ) i⋆ {!!} {!!}
... | i''⋆
   rewrite List-++-assoc Δ' Δₒ Δ
    = {!!} ∷ instantiations-subst Δₒ i⋆ sub-is is⋆

-- subst-helper₂ : ∀ {Δ} Δ₁ Δ₂ {Γ₁ Γ₁' Γ₂ : RegisterAssignment} {i a} {i₁ i₂ a'} →
--                   Δ ⊢ i of a instantiation →
--                   Δ₁ ++ Δ₂ ++ a ∷ Δ ⊢ i₁ of a' instantiation →
--                   a' ∷ Δ₁ ++ Δ₂ ++ a ∷ Δ ⊢ Γ₁ Valid →
--                   i₁ ⟦ i / length (Δ₁ ++ Δ₂) ⟧≡ i₂ →
--                   Γ₁ ⟦ i / length (a' ∷ Δ₁ ++ Δ₂) ⟧≡ Γ₁' →
--                   Γ₁ ⟦ i₁ / 0 ⟧≡ Γ₂ →
--                   ∃ λ Γ₂' →
--                     Γ₂  ⟦ i / length (Δ₁ ++ Δ₂) ⟧≡ Γ₂' ×
--                     Γ₁' ⟦ i₂ / 0 ⟧≡ Γ₂'
-- subst-helper₂ Δ₂ i⋆ i₁⋆ sub-i sub-Γ₁ sub-Γ = {!!}

-- subst-helper₃ : ∀ {Δ Δ₁} Δ₂ {Γ₁ Γ₁' Γ₂ : RegisterAssignment} {i a} {is is'} →
--                   Δ ⊢ i of a instantiation →
--                   Δ₂ ++ a ∷ Δ ⊢ is of Δ₁ instantiations →
--                   Δ₁ ++ Δ₂ ++ a ∷ Δ ⊢ Γ₁ Valid →
--                   is ⟦ i / length Δ₂ ⟧≡ is' →
--                   Γ₁ ⟦ i / length (Δ₁ ++ Δ₂) ⟧≡ Γ₁' →
--                   Γ₁ ⟦ is / 0 ⟧many≡ Γ₂ →
--                   ∃ λ Γ₂' →
--                     Γ₂  ⟦ i / length Δ₂ ⟧≡ Γ₂' ×
--                     Γ₁' ⟦ is' / 0 ⟧many≡ Γ₂'
-- subst-helper₃ Δ₂ i⋆ [] Γ₁⋆ [] sub-Γ₁ [] = _ , sub-Γ₁ , []
-- subst-helper₃ {Δ} {a' ∷ Δ₁} Δ₂ i⋆ (i₁⋆ ∷ is⋆) Γ₁⋆ (sub-i ∷ sub-is) sub-Γ₁ (sub-Γ ∷ subs-Γ)
--   rewrite instantiations-length is⋆
--         | sym (List-length-++ Δ₁ {Δ₂})
--         = {!!}
-- --   with subst-helper₂ Δ₁ Δ₂ i⋆ i₁⋆ Γ₁⋆ sub-i sub-Γ₁ sub-Γ
-- -- ... | Γ₂' , sub-Γ₂ , sub-Γ'
-- --   with subst-helper₃ Δ₂ i⋆ is⋆ (valid-subst {{RegisterAssignment-TypeSubstitution}}  [] i₁⋆ Γ₁⋆ sub-Γ) sub-is sub-Γ₂ subs-Γ
-- -- ... | Γₑ , sub-Γₑ , subs-Γ' = Γₑ , sub-Γₑ , sub-Γ' ∷ subs-Γ'

-- subst-helper : ∀ {Δ Δᵢ} Δₒ {Γᵢ Γᵢ' Γₒ Γₒ' : RegisterAssignment} {i a is is'} →
--                  Δ ⊢ i of a instantiation →
--                  Δₒ ++ a ∷ Δ ⊢ is of Δᵢ instantiations →
--                  Δᵢ ++ a ∷ Δ ⊢ Γᵢ Valid →
--                  is ⟦ i / length Δₒ ⟧≡ is' →
--                  Γₒ ⟦ i / length Δₒ ⟧≡ Γₒ' →
--                  Γᵢ ⟦ i / length Δᵢ ⟧≡ Γᵢ' →
--                  weaken (length Δᵢ) (length Δₒ) Γᵢ ⟦ is / 0 ⟧many≡ Γₒ →
--                  weaken (length Δᵢ) (length Δₒ) Γᵢ' ⟦ is' / 0 ⟧many≡ Γₒ'
-- subst-helper {Δ} {Δᵢ} Δₒ {a = a} i⋆ is⋆ Γᵢ⋆ sub-is sub-Γₒ sub-Γᵢ subs-Γ = {!!}
-- --   with subst-helper₃ Δₒ i⋆ is⋆ (valid-weaken Δᵢ Δₒ (a ∷ Δ) Γᵢ⋆) sub-is (weaken-subst Δᵢ Δₒ Δ Γᵢ⋆ sub-Γᵢ) subs-Γ
-- -- ... | Γₒ' , sub-Γₒ' , subs-Γ'
-- --   rewrite subst-unique sub-Γₒ sub-Γₒ' = subs-Γ'

vval-subst2 : ∀ {ψ₁} Δ₁ {a Δ₂ i} →
                [] ⊢ ψ₁ Valid →
                Δ₂ ⊢ i of a instantiation →
                ∀ {Γ₁} →
                Δ₁ ++ a ∷ Δ₂ ⊢ Γ₁ Valid →
                ∀ {τ₁} →
                Δ₁ ++ a ∷ Δ₂ ⊢ τ₁ Valid →
                ∀ {v₁} →
                ψ₁ , Δ₁ ++ a ∷ Δ₂ , Γ₁ ⊢ v₁ of τ₁ vval →
                ∃₂ λ Γ₂ τ₂ → ∃ λ v₂ →
                  Γ₁ ⟦ i / length Δ₁ ⟧≡ Γ₂ ×
                  τ₁ ⟦ i / length Δ₁ ⟧≡ τ₂ ×
                  v₁ ⟦ i / length Δ₁ ⟧≡ v₂ ×
                  Δ₁ ++ Δ₂ ⊢ Γ₂ Valid ×
                  Δ₁ ++ Δ₂ ⊢ τ₂ Valid ×
                  ψ₁ , Δ₁ ++ Δ₂ , Γ₂ ⊢ v₂ of τ₂ vval
vval-subst2 Δ₁ ψ₁⋆ i⋆ Γ₁⋆ τ₁⋆ {reg ♯r} of-reg
  with valid-subst-exists Δ₁ i⋆ Γ₁⋆
... | registerₐ sp regs , subst-registerₐ sub-sp sub-regs , valid-registerₐ sp⋆ regs⋆
  with allzipᵥ-lookup ♯r sub-regs
... | sub-τ
  with Allᵥ-lookup ♯r regs⋆
... | τ₂⋆
  = _ , _ , _ , subst-registerₐ sub-sp sub-regs , sub-τ , subst-reg , valid-registerₐ sp⋆ regs⋆ , τ₂⋆ , of-reg
vval-subst2 Δ₁ ψ₁⋆ i⋆ Γ₁⋆ τ₁⋆ (of-globval l)
  with valid-subst-exists Δ₁ i⋆ Γ₁⋆
... | Γ₂ , sub-Γ , Γ₂⋆
  with All-lookup l ψ₁⋆
... | τ₁⋆'
  = _ , _ , _ , sub-Γ , subst-outside-ctx τ₁⋆' , subst-globval , Γ₂⋆ , valid-weaken-empty-ctx _ τ₁⋆' , of-globval l
vval-subst2 Δ₁ ψ₁⋆ i⋆ Γ₁⋆ τ₁⋆ of-int
  with valid-subst-exists Δ₁ i⋆ Γ₁⋆
... | Γ₂ , sub-Γ , Γ₂⋆
  = _ , _ , _ , sub-Γ , subst-int , subst-int , Γ₂⋆ , valid-int , of-int
vval-subst2 Δ₁ ψ₁⋆ i⋆ Γ₁⋆ τ₁⋆ of-ns
  with valid-subst-exists Δ₁ i⋆ Γ₁⋆
... | Γ₂ , sub-Γ , Γ₂⋆
  = _ , _ , _ , sub-Γ , subst-ns , subst-ns , Γ₂⋆ , valid-ns , of-ns
vval-subst2 {ψ₁} Δ₁ {a} {Δ₂} ψ₁⋆ i⋆ {Γ₁} Γ₁⋆ .{∀[ Δₒ ] Γₒ₁} τₒ₁⋆ {Λ Δₒ ∙ vᵢ₁ ⟦ is₁ ⟧} (of-Λ .{ψ₁} .{Δ₁ ++ a ∷ Δ₂} .{Γ₁} {Δᵢ} .{Δₒ} {Γᵢ₁} {Γₒ₁} .{vᵢ₁} .{is₁} vᵢ₁⋆ is⋆ Γ-stuff)
  with vval-subst2 Δ₁ ψ₁⋆ i⋆ Γ₁⋆ (vval-valid-type ψ₁⋆ Γ₁⋆ vᵢ₁⋆) vᵢ₁⋆
... | Γ₂ , ∀[ .Δᵢ ] Γᵢ₂ , vᵢ₂ , sub-Γ , subst-∀ sub-Γᵢ , sub-vᵢ , Γ₂⋆ , valid-∀ Γᵢ₂⋆ , vᵢ₂⋆
  -- with valid-subst-exists Δ₁ i⋆ is⋆
-- ... | wut
  with {!!} | {!!}
... | Γₒ₂ | is₂
  = Γ₂ , ∀[ Δₒ ] Γₒ₂ , Λ Δₒ ∙ vᵢ₂ ⟦ is₂ ⟧ , sub-Γ , subst-∀ {!!} , subst-Λ sub-vᵢ {!!} , Γ₂⋆ , valid-∀ {!!} , of-Λ {ψ₁} {Δ₁ ++ Δ₂} {Γ₂} {Δᵢ} {Δₒ} {Γᵢ₂} {Γₒ₂} {vᵢ₂} {is₂} vᵢ₂⋆ {!!} {!!}


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
  with vval-subst ψ₁⋆ Γ⋆ i⋆ sub-Γᵥ {!!} (subst-∀ sub-Γᵢ') v⋆
... | v'⋆
  = {!!}
--   rewrite +-comm (length Δₒ) 0 = ?
--   with instantiations-subst Δₒ i⋆ sub-is is⋆
-- ... | is'⋆
--   with subst-helper Δₒ i⋆ is⋆ Γᵢ⋆ sub-is sub-Γₒ sub-Γᵢ subs-Γ
-- ... | subs-Γ' = of-Λ v'⋆ is'⋆ subs-Γ'


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
instructionsequence-subst-many ψ₁⋆ Γ⋆ (i⋆ ∷ is⋆) (sub-Γ ∷ subs-Γ) (sub-I ∷ subs-I) I⋆ = {!!}
--   with instructionsequence-subst ψ₁⋆ Γ⋆ i⋆ sub-Γ sub-I I⋆
-- ... | I'⋆
--   with instructionsequence-subst-many ψ₁⋆ (valid-subst [] i⋆ Γ⋆ sub-Γ) is⋆ subs-Γ subs-I I'⋆
-- ... | I''⋆ = I''⋆

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
