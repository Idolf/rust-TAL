open import Types
open import Weakening
open import ValidTypes

open import Data.Product using (_,_ ; _×_ ; Σ-syntax)
open import Data.Nat using (ℕ ; suc ; _+_ ; _∸_ ; _<_ ; _≥_ ; s≤s ; z≤n ; zero ; _≤?_)
import Data.Nat.Properties as P
open import Data.Product using (_,_ ; ∃)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; sym ; cong ; cong₂ ; refl ; subst)
open import Relation.Nullary using (yes ; no)
import Algebra as A
open P.SemiringSolver
     using (prove; solve; _:=_; con; var; _:+_; _:*_; :-_; _:-_)
module R = A.CommutativeSemiring P.commutativeSemiring
module M = A.CommutativeMonoid R.+-commutativeMonoid renaming (_∙_ to _+_ ; _≈_ to _≡_)

-- ↓ₐ-add-left : ∀ {Δ₁ Δ₂ ι a} → Δ₂ ↓ₐ ι ≡ a → Δ₁ ++ Δ₂ ↓ₐ ι ≡ a
-- ↓ₐ-add-left here = here
-- ↓ₐ-add-left (there l) = there (↓ₐ-add-left l)

-- ↓ₐ-add-right : ∀ {Δ₁ Δ₂ ι a} → Δ₁ ↓ₐ ι ≡ a → Δ₁ ++ Δ₂ ↓ₐ length Δ₂ + ι ≡ weaken-CtxVal a 0 (length Δ₂)
-- ↓ₐ-add-right {Δ₂ = Ɛ} l = {!!}
-- ↓ₐ-add-right {Δ₂ = Δ₂ , a} l = {!!}

-- ↓ₐ-add-right' : ∀ {Δ₁ Δ₂ ι a} → Δ₁ ↓ₐ ι ≡ a → Δ₁ ++ Δ₂ ↓ₐ ι + length Δ₂ ≡ a
-- ↓ₐ-add-right' {Δ₂ = Δ₂} {ι} l rewrite M.comm ι (length Δ₂) = ↓ₐ-add-right {Δ₂ = Δ₂} l

-- ↓ₐ-remove-left : ∀ {Δ₁ Δ₂ ι a} → Δ₁ ++ Δ₂ ↓ₐ ι ≡ a → ι < length Δ₂ → Δ₂ ↓ₐ ι ≡ a
-- ↓ₐ-remove-left {Δ₂ = Ɛ} l ()
-- ↓ₐ-remove-left {Δ₂ = Δ₂ , a} here lt = here
-- ↓ₐ-remove-left {Δ₂ = Δ₂ , a} (there l) (s≤s lt) = there (↓ₐ-remove-left l lt)

-- ↓ₐ-remove-right : ∀ {Δ₁ Δ₂ ι a} → Δ₁ ++ Δ₂ ↓ₐ ι ≡ a → ι ≥ length Δ₂ → Δ₁ ↓ₐ ι ∸ length Δ₂ ≡ a
-- ↓ₐ-remove-right {Δ₂ = Ɛ} l ge = l
-- ↓ₐ-remove-right {Δ₂ = Δ₂ , a} (there l) (s≤s ge) = ↓ₐ-remove-right l ge

-- ↓ₐ-remove : ∀ {Δ₁} Δ₂ {ι a} → Δ₁ ++ Δ₂ ↓ₐ ι ≡ a → (∃ λ ι' → ι ≡ length Δ₂ + ι' × Δ₁ ↓ₐ ι' ≡ a) ⊎ (ι < length Δ₂ × Δ₂ ↓ₐ ι ≡ a)
-- ↓ₐ-remove Ɛ l = inj₁ (_ , (refl , l))
-- ↓ₐ-remove (Δ₂ , a) here = inj₂ (s≤s z≤n , here)
-- ↓ₐ-remove (Δ₂ , a) (there l) with ↓ₐ-remove Δ₂ l
-- ↓ₐ-remove (Δ₂ , a₁) (there l) | inj₁ (ι' , (refl , l')) = inj₁ (ι' , (refl , l'))
-- ↓ₐ-remove (Δ₂ , a₁) (there l) | inj₂ (ι<lengthΔ₂ , l') = inj₂ (s≤s ι<lengthΔ₂ , there l')

-- -- length-++ : ∀ Δ₁ Δ₂ → length Δ₁ + length Δ₂ ≡ length (Δ₁ ++ Δ₂)
-- -- length-++ Δ₁ Δ₂ rewrite M.comm (length Δ₁) (length Δ₂) = help Δ₂ Δ₁
-- --   where help : ∀ Δ₁ Δ₂ → length Δ₁ + length Δ₂ ≡ length (Δ₂ ++ Δ₁)
-- --         help Ɛ Δ₂ = refl
-- --         help (Δ₁ , a) Δ₂ = cong suc (help Δ₁ Δ₂)


-- -- ++-assoc : ∀ Δ₁ Δ₂ Δ₃ → (Δ₁ ++ Δ₂) ++ Δ₃ ≡ Δ₁ ++ (Δ₂ ++ Δ₃)
-- -- ++-assoc Δ₁ Δ₂ Ɛ = refl
-- -- ++-assoc Δ₁ Δ₂ (Δ₃ , a) rewrite ++-assoc Δ₁ Δ₂ Δ₃ = refl

-- -- weaken-length : ∀ Δ e → length (weaken-Ctx Δ e) ≡ length Δ
-- -- weaken-length Ɛ e = refl
-- -- weaken-length (Δ , a) e = cong suc (weaken-length Δ e)


-- private
--   helper : {A : Set} → (A → ℕ → ℕ → A) → A → Ctx → Ctx → A
--   helper f a Δ₂ Δₑ = f a (length Δ₂) (length Δₑ)

-- weaken-ℕʰ : ℕ → Ctx → Ctx → ℕ
-- weaken-ℕʰ = helper weaken-ℕ

-- weaken-Ctxʰ : Ctx → Ctx → Ctx → Ctx
-- weaken-Ctxʰ Δ₁ Δₑ Δ₂ = Δ₁ ++ Δₑ ++ weaken-Ctx Δ₂ (length Δₑ)

-- weaken-CtxValʰ : CtxVal → Ctx → Ctx → CtxVal
-- weaken-CtxValʰ = helper weaken-CtxVal

-- weaken-Stackʰ : Stack → Ctx → Ctx → Stack
-- weaken-Stackʰ = helper weaken-Stack

-- weaken-StackValʰ : StackVal → Ctx → Ctx → StackVal
-- weaken-StackValʰ = helper weaken-StackVal

-- weaken-Typeʰ : Type → Ctx → Ctx → Type
-- weaken-Typeʰ = helper weaken-Type

-- weaken-Registerʰ : Register → Ctx → Ctx → Register
-- weaken-Registerʰ = helper weaken-Register

-- weaken-Lifetimeʰ : Lifetime → Ctx → Ctx → Lifetime
-- weaken-Lifetimeʰ = helper weaken-Lifetime

-- mutual
--   weaken-Ctx-valid : ∀ {Δ₁ Δₑ} Δ₂ → ⊢ Δ₁ ++ Δ₂ Ctx →
--                                     ⊢ Δ₁ ++ Δₑ Ctx →
--                                     ⊢ weaken-Ctxʰ Δ₁ Δₑ Δ₂ Ctx
--   weaken-Ctx-valid Ɛ Δ₂⋆ Δₑ⋆ = Δₑ⋆
--   weaken-Ctx-valid (Δ₂ , a) (valid-∷ Δ₂⋆ v⋆) Δₑ⋆ = valid-∷ (weaken-Ctx-valid Δ₂ Δ₂⋆ Δₑ⋆) (weaken-CtxVal-valid v⋆)

--   weaken-CtxVal-valid : ∀ {Δ₁ Δₑ Δ₂ a} → Δ₁ ++ Δ₂ ⊢ a CtxVal →
--                                          weaken-Ctxʰ Δ₁ Δₑ Δ₂ ⊢ weaken-CtxValʰ a Δ₂ Δₑ CtxVal
--   weaken-CtxVal-valid valid-ρ = valid-ρ
--   weaken-CtxVal-valid (valid-α σ⋆) = valid-α (weaken-Stack-valid σ⋆)
--   weaken-CtxVal-valid (valid-β σ⋆) = valid-β (weaken-Stack-valid σ⋆)
--   weaken-CtxVal-valid (valid-≤a ℓ₁⋆ ℓ₂⋆ σ⋆) = valid-≤a (weaken-Lifetime-valid ℓ₁⋆) (weaken-Lifetime-valid ℓ₂⋆) (weaken-Stack-valid σ⋆)

--   weaken-Stack-valid : ∀ {Δ₁ Δₑ Δ₂ σ} → Δ₁ ++ Δ₂ ⊢ σ Stack →
--                                         weaken-Ctxʰ Δ₁ Δₑ Δ₂ ⊢ weaken-Stackʰ σ Δ₂ Δₑ Stack
--   weaken-Stack-valid valid-nil = valid-nil
--   weaken-Stack-valid (valid-∷ σ⋆ v⋆) = valid-∷ (weaken-Stack-valid σ⋆) (weaken-StackVal-valid v⋆)
--   weaken-Stack-valid {Δ₂ = Δ₂} (valid-ρ⁼ l) = valid-ρ⁼ (help Δ₂ l)
--     where help : ∀ {Δ₁ Δₑ} Δ₂ {ι} → Δ₁ ++ Δ₂ ↓ₐ ι ≡ ρ → weaken-Ctxʰ Δ₁ Δₑ Δ₂ ↓ₐ weaken-ℕʰ ι Δ₂ Δₑ ≡ ρ
--           help Ɛ l = ↓ₐ-add-right' l
--           help (Δ₃ , .ρ) here = here
--           help (Δ₃ , a) (there l) = there (help Δ₃ l)
--   weaken-StackVal-valid : ∀ {Δ₁ Δₑ Δ₂ σ v} → Δ₁ ++ Δ₂ , σ ⊢ v StackVal →
--                             weaken-Ctxʰ Δ₁ Δₑ Δ₂ , weaken-Stackʰ σ Δ₂ Δₑ ⊢ weaken-StackValʰ v Δ₂ Δₑ StackVal
--   weaken-StackVal-valid (valid-type τ⋆) = valid-type (weaken-Type-valid τ⋆)
--   weaken-StackVal-valid valid-γ = valid-γ

--   weaken-Type-valid : ∀ {Δ₁ Δₑ Δ₂ σ τ} → Δ₁ ++ Δ₂ , σ ⊢ τ Type →
--                         weaken-Ctxʰ Δ₁ Δₑ Δ₂ , weaken-Stackʰ σ Δ₂ Δₑ ⊢ weaken-Typeʰ τ Δ₂ Δₑ Type
--   weaken-Type-valid (♯b , τ⋆) = ♯b , weaken-Typeₙ-valid τ⋆

--   weaken-Typeₙ-valid : ∀ {Δ₁ Δₑ Δ₂ σ τ ♯b} → Δ₁ ++ Δ₂ , σ ⊢ τ Typeₙ ♯b →
--                       weaken-Ctxʰ Δ₁ Δₑ Δ₂ , weaken-Stackʰ σ Δ₂ Δₑ ⊢ weaken-Typeʰ τ Δ₂ Δₑ Typeₙ ♯b
--   weaken-Typeₙ-valid {Δ₁} {Δₑ} {Δ₂} (valid-β⁼ l suf) with ↓ₐ-remove Δ₂ l
--   weaken-Typeₙ-valid {Δ₁} {Δₑ} {Δ₂} {σ} (valid-β⁼ {σʰ} l suf) | inj₁ (ιʰ , (refl , lʰ)) = {!!}
--   weaken-Typeₙ-valid {Δ₁} {Δₑ} {Δ₂} (valid-β⁼ l suf) | inj₂ y = {!!}
--   -- with ↓ₐ-remove Δ₂ l
--   --   weaken-Stack-valid {Δ₁} {Δₑ} {Δ₂} (valid-ρ⁼ l) | inj₁ (ιʰ , (refl , lʰ))
--   --     rewrite sym (weaken-length Δ₂ (length Δₑ)) |
--   --             weaken-ℕ-≥ (length (weaken-Ctx Δ₂ (length Δₑ)) + ιʰ) (length (weaken-Ctx Δ₂ (length Δₑ))) (length Δₑ) (P.m≤m+n _ _) |
--   --             lemma (length (weaken-Ctx Δ₂ (length Δₑ))) ιʰ (length Δₑ) |
--   --             length-++ Δₑ (weaken-Ctx Δ₂ (length Δₑ)) = valid-ρ⁼ (↓ₐ-add-rightʰ lʰ)
--   --   weaken-Stack-valid {Δ₁} {Δₑ} {Δ₂} (valid-ρ⁼ {ι} l) | inj₂ (ι<lengthΔ₂ , lʰ)
--   --     rewrite weaken-ℕ-< ι (length Δ₂) (length Δₑ) {!!} = {!!}

--   weaken-Typeₙ-valid valid-int = valid-int
--   weaken-Typeₙ-valid valid-void = valid-void
--   weaken-Typeₙ-valid (valid-~ τ⋆) = valid-~ (weaken-Type-valid τ⋆)
--   weaken-Typeₙ-valid (valid-& ℓ⋆ τ⋆) = valid-& (weaken-Lifetime-valid ℓ⋆) (weaken-Type-valid τ⋆)
--   weaken-Typeₙ-valid (valid-∀ Δ⋆ Γ⋆) = valid-∀ Δ⋆ {!!}

--   private
--     lemma : ∀ x y z → x + y + z ≡ y + (z + x)
--     lemma = solve 3 (λ x y z → x :+ y :+ z := y :+ (z :+ x)) refl

--   weaken-Register-valid : ∀ {Δ₁ Δₑ Δ₂ Γ} → Δ₁ ++ Δ₂ ⊢ Γ Register →
--                             weaken-Ctxʰ Δ₁ Δₑ Δ₂ ⊢ weaken-Registerʰ Γ Δ₂ Δₑ Register
--   weaken-Register-valid Γ⋆ = {!!}

--   weaken-Lifetime-valid : ∀ {Δ₁ Δₑ Δ₂ σ ℓ} → Δ₁ ++ Δ₂ , σ ⊢ ℓ Lifetime →
--                             weaken-Ctxʰ Δ₁ Δₑ Δ₂ , weaken-Stackʰ σ Δ₂ Δₑ ⊢ weaken-Lifetimeʰ ℓ Δ₂ Δₑ Lifetime
--   weaken-Lifetime-valid = {!!}
