module TermSubstitution where

open import Util
open import Judgments
open import Lemmas
open import TermSubtyping
open import Data.List.Base

lookup-helper : ∀ {n} ♯r pos inc (regs : Vec Type n) →
                  lookup ♯r (weaken pos inc regs) ≡ weaken pos inc (lookup ♯r regs)
lookup-helper zero pos inc (τ ∷ τs) = refl
lookup-helper (suc ♯r) pos inc (τ ∷ τs) = lookup-helper ♯r pos inc τs

-- {-# TERMINATING #-}
-- of-vval-weaken :
--   ∀ Δ₁ Δ₂ Δ₃ {ψ₁ Γ v τ} →
--     ψ₁ , Δ₁ ++ Δ₃ , Γ ⊢ v of τ vval →
--     ψ₁ , Δ₁ ++ Δ₂ ++ Δ₃ ,
--       weaken (length Δ₁) (length Δ₂) Γ ⊢
--       weaken (length Δ₁) (length Δ₂) v of
--       weaken (length Δ₁) (length Δ₂) τ vval
-- of-vval-weaken Δ₁ Δ₂ Δ₃ {Γ = registerₐ sp regs} {v = reg ♯r} (of-reg lookup≤τ)
--   with subtype-weaken Δ₁ Δ₂ Δ₃ lookup≤τ
-- ... | lookup'≤τ'
--   rewrite sym (lookup-helper ♯r (length Δ₁) (length Δ₂) regs)
--     = of-reg lookup'≤τ'
-- of-vval-weaken Δ₁ Δ₂ Δ₃ (of-globval l τ≤τ')
--   with (weaken-empty-ctx (length Δ₁) (length Δ₂) (proj₂ (≤-valid τ≤τ')))
-- ... | eq rewrite eq = of-globval l τ≤τ'
-- of-vval-weaken Δ₁ Δ₂ Δ₃ of-int = of-int
-- of-vval-weaken Δ₁ Δ₂ Δ₃ of-ns = of-ns
-- of-vval-weaken Δ₁ Δ₂ Δ₃ {ψ₁} {Γ} {v = Λ Δ ∙ v ⟦ is ⟧} v⋆ = of-vval-weaken Δ₁ Δ₂ Δ₃ v⋆

-- {-# TERMINATING #-}
-- of-vval-subst :
--   ∀ {ψ₁ Δ₁ Δ₂ Γ Γ' τ τ' a i} →
--     Δ₁ ⊢ i Valid →
--     InstantiationMatch i a →
--     Γ ⟦ i / length Δ₁ ⟧≡ Γ' →
--     τ ⟦ i / length Δ₁ ⟧≡ τ' →
--     ∀ {v : SmallValue} →
--     ψ₁ , Δ₁ ++ a ∷ Δ₂ , Γ ⊢ v of τ vval →
--     ∃ λ v' →
--       v ⟦ i / length Δ₁ ⟧≡ v' ×
--       ψ₁ , Δ₁ ++ Δ₂ , Γ' ⊢ v' of τ' vval
-- of-vval-subst i⋆ m (subst-registerₐ sub-sp sub-regs) sub-τ {reg ♯r} (of-reg lookup≤τ)
--   with subtype-subst-exists i⋆ m lookup≤τ
-- ... | lookup' , τ' , sub-lookup , sub-τ' , lookup'≤τ'
--   with allzipᵥ-lookup ♯r sub-regs
-- ... | sub-lookup'
--   rewrite subst-unique sub-τ sub-τ'
--         | subst-unique sub-lookup sub-lookup'
--   = reg ♯r , subst-reg , of-reg lookup'≤τ'
-- of-vval-subst {i = i} i⋆ m sub-Γ sub-τ {globval ♯l} (of-globval l τ≤τ')
--   rewrite subst-unique sub-τ (subst-outside-ctx (proj₂ (≤-valid τ≤τ')))
--   = globval ♯l , subst-globval , of-globval l τ≤τ'
-- of-vval-subst i⋆ m sub-Γ subst-int of-int = _ , subst-int , of-int
-- of-vval-subst i⋆ m sub-Γ subst-ns of-ns = ns , subst-ns , of-ns
-- of-vval-subst {Γ = Γ} {Γ'} i⋆ m sub-Γ sub-τ {Λ Δ₂ ∙ v ⟦ is ⟧} v⋆
--   = of-vval-subst i⋆ m sub-Γ sub-τ v⋆

subst-many-registerₐ-split :
  ∀ {sp sp' regs regs' is ι} →
    registerₐ sp regs ⟦ is / ι ⟧many≡ registerₐ sp' regs' →
    sp ⟦ is / ι ⟧many≡ sp' ×
    regs ⟦ is / ι ⟧many≡ regs'
subst-many-registerₐ-split [] = [] , []
subst-many-registerₐ-split (subst-registerₐ sub-sp sub-regs ∷ subs-Γ)
  with subst-many-registerₐ-split subs-Γ
... | subs-sp , subs-regs = sub-sp ∷ subs-sp , sub-regs ∷ subs-regs

subst-many-lookup :
  ∀ {n} {regs regs' : Vec Type n} {is ι} ♯r →
    regs ⟦ is / ι ⟧many≡ regs' →
    lookup ♯r regs ⟦ is / ι ⟧many≡ lookup ♯r regs'
subst-many-lookup ♯r [] = []
subst-many-lookup ♯r (sub-regs ∷ subs-regs) = allzipᵥ-lookup ♯r sub-regs ∷ subst-many-lookup ♯r subs-regs

subst-reg-many : ∀ ♯r is ι →
                   reg ♯r ⟦ is / ι ⟧many≡ reg ♯r
subst-reg-many ♯r [] ι = []
subst-reg-many ♯r (i ∷ is) ι = subst-reg ∷ subst-reg-many ♯r is ι

subst-globval-many : ∀ (♯l : ℕ) is ι →
                       _⟦_/_⟧many≡_ {A = SmallValue} (globval ♯l) is ι (globval ♯l)
subst-globval-many ♯l [] ι = []
subst-globval-many ♯l (i ∷ is) ι = subst-globval ∷ subst-globval-many ♯l is ι

subst-many-int-type : ∀ is ι →
                        _⟦_/_⟧many≡_ {A = Type} int is ι int
subst-many-int-type [] ι = []
subst-many-int-type (i ∷ is) ι = subst-int ∷ subst-many-int-type is ι

subst-many-ns-type : ∀ is ι →
                       _⟦_/_⟧many≡_ {A = Type} ns is ι ns
subst-many-ns-type [] ι = []
subst-many-ns-type (i ∷ is) ι = subst-ns ∷ subst-many-ns-type is ι

subst-many-int : ∀ i is ι →
                   _⟦_/_⟧many≡_ {A = SmallValue} (int i) is ι (int i)
subst-many-int i [] ι = []
subst-many-int i (_ ∷ is) ι = subst-int ∷ subst-many-int i is ι

subst-many-ns : ∀ is ι →
                  _⟦_/_⟧many≡_ {A = SmallValue} ns is ι ns
subst-many-ns [] ι = []
subst-many-ns (_ ∷ is) ι = subst-ns ∷ subst-many-ns is ι

-- of-vval-subst :
--   ∀ {ψ₁ Δ₁ Δ₂ Γ Γ' τ τ' is} →
--     Δ₁ ⊢ is Valid →
--     InstantiationMatches is Δ₂ →
--     Γ ⟦ is / length Δ₁ ⟧many≡ Γ' →
--     τ ⟦ is / length Δ₁ ⟧many≡ τ' →
--     ∀ {v : SmallValue} →
--     ψ₁ , Δ₁ ++ Δ₂ , Γ ⊢ v of τ vval →
--     ∃ λ v' →
--       v ⟦ is / length Δ₁ ⟧many≡ v' ×
--       ψ₁ , Δ₁ ++ Δ₂ , Γ' ⊢ v' of τ' vval
-- of-vval-subst {Δ₁ = Δ₁} {Γ = registerₐ sp regs} {registerₐ sp' regs'} {is = is}
--               is⋆ ms subs-Γ subs-τ {reg ♯r} (of-reg lookup≤τ)
--   with subst-many-registerₐ-split subs-Γ
-- ... | subs-sp , subs-regs
--   with subtype-subst-exists-many is⋆ ms lookup≤τ
-- ... | lookup' , τ' , subs-lookup , subs-τ' , lookup'≤τ'
--   with subst-many-lookup ♯r subs-regs
-- ... | subs-lookup'
--   rewrite subst-unique-many subs-τ subs-τ'
--         | subst-unique-many subs-lookup subs-lookup'
--   = reg ♯r , subst-reg-many ♯r is (length Δ₁) , of-reg (≤-++ lookup'≤τ')
-- of-vval-subst {Δ₁ = Δ₁} {is = is} is⋆ ms subs-Γ subs-τ {globval ♯l} (of-globval l τ≤τ')
--   rewrite subst-unique-many subs-τ (subst-outside-ctx-many (proj₂ (≤-valid τ≤τ')))
--   = globval ♯l , subst-globval-many ♯l is (length Δ₁) , of-globval l τ≤τ'
-- of-vval-subst {Δ₁ = Δ₁} {is = is} is⋆ ms subs-Γ subs-τ {int i} of-int
--   rewrite subst-unique-many subs-τ (subst-many-int-type is (length Δ₁))
--   = int i , subst-many-int i is (length Δ₁) , of-int
-- of-vval-subst {Δ₁ = Δ₁} {is = is} is⋆ ms subs-Γ subs-τ {ns} of-ns
--   rewrite subst-unique-many subs-τ (subst-many-ns-type is (length Δ₁))
--   = ns , subst-many-ns is (length Δ₁) , of-ns
-- of-vval-subst is⋆ ms subs-Γ subs-τ (of-Λ v⋆ is'⋆ ms' subs-Γ' x₃) = {!!}

-- of-instructionsequence-subst :
--   ∀ {ψ₁
