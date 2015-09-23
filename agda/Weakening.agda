open import Types
open import Eq

open import Data.Vec using (Vec ; [] ; _∷_)
open import Data.Nat using (ℕ ; suc ; zero ; _+_ ; _<_ ; _≥_ ; _≤_ ; z≤n ; s≤s ; _∸_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂)
import Data.Nat.Properties as P
import Algebra as A
module R = A.CommutativeSemiring P.commutativeSemiring
module M = A.CommutativeMonoid R.+-commutativeMonoid renaming (_∙_ to _+_ ; _≈_ to _≡_)
open P.SemiringSolver
  using (prove; solve; _:=_; con; var; _:+_; _:*_; :-_; _:-_)


-- Some lemmas
private
  data foo (n m : ℕ) : Set where
    foo< : n < m → foo n m
    foo≥ : n ≥ m → foo n m

  bar : ∀ n m → foo n m
  bar n zero = foo≥ z≤n
  bar zero (suc m) = foo< (s≤s z≤n)
  bar (suc n) (suc m) with bar n m
  bar (suc n) (suc m) | foo< x = foo< (s≤s x)
  bar (suc n) (suc m) | foo≥ x = foo≥ (s≤s x)

  baz : ∀ {x y z q} → x ≤ z → y ≤ q → x + y ≤ z + q
  baz {z = z} z≤n ge₂ = P.≤-steps z ge₂
  baz (s≤s ge₁) ge₂ = s≤s (baz ge₁ ge₂)

  lemma' : ∀ {x y} → suc x ≤ suc y → x ≤ y
  lemma' (s≤s le) = le

  lemma1 : ∀ x y z → x + y < z → x < z ∸ y
  lemma1 x zero z le rewrite M.comm x 0 = le
  lemma1 x (suc y) zero ()
  lemma1 x (suc y) (suc z) le rewrite M.comm x (suc y) | M.comm y x = lemma1 x y z (lemma' le)

  lemma2 : ∀ x y z → x + y ≥ z → x ≥ z ∸ y
  lemma2 x zero z ge rewrite M.comm x 0 = ge
  lemma2 x (suc y) zero ge = z≤n
  lemma2 x (suc y) (suc z) ge rewrite M.comm x (suc y) | M.comm y x = lemma2 x y z (lemma' ge)

  lemma3 : ∀ x y → x + suc y ≡ suc x + y
  lemma3 x y rewrite M.comm x (suc y) | M.comm y x = refl

  lemma4 : ∀ {x y} → x ≤ y → x ∸ y ≡ 0
  lemma4 {zero} {y} le = P.0∸n≡0 y
  lemma4 {suc x} (s≤s le) = lemma4 le

private
  weaken-ℕ : ℕ → ℕ → ℕ → ℕ
  weaken-ℕ v zero e = v + e
  weaken-ℕ zero (suc pos) e = zero
  weaken-ℕ (suc v) (suc pos) e = suc (weaken-ℕ v pos e)

  weaken-ℕ-< : ∀ n pos e → n < pos → weaken-ℕ n pos e ≡ n
  weaken-ℕ-< x zero e ()
  weaken-ℕ-< zero (suc pos) e lt = refl
  weaken-ℕ-< (suc x) (suc pos) e (s≤s lt) = cong suc (weaken-ℕ-< x pos e lt)

  weaken-ℕ-≥ : ∀ n pos e → n ≥ pos → weaken-ℕ n pos e ≡ n + e
  weaken-ℕ-≥ n zero e ge = refl
  weaken-ℕ-≥ zero (suc pos) e ()
  weaken-ℕ-≥ (suc n) (suc pos) e (s≤s ge) = cong suc (weaken-ℕ-≥ n pos e ge)

  weaken-ℕ-id : ∀ n {pos} → weaken-ℕ n pos 0 ≡ n
  weaken-ℕ-id zero {zero} = refl
  weaken-ℕ-id zero {suc pos} = refl
  weaken-ℕ-id (suc n) {zero} = M.comm (suc n) 0
  weaken-ℕ-id (suc n) {suc pos} = cong suc (weaken-ℕ-id n {pos})

  weaken-ℕ-comp₁ : ∀ n {pos e₁ e₂} → weaken-ℕ (weaken-ℕ n pos e₁) pos e₂ ≡ weaken-ℕ n pos (e₁ + e₂)
  weaken-ℕ-comp₁ n {pos} {e₁} {e₂} with bar n pos
  weaken-ℕ-comp₁ n {pos} {e₁} {e₂} | foo< n<pos =
    begin
      weaken-ℕ (weaken-ℕ n pos e₁) pos e₂
    ≡⟨ weaken-ℕ-< n pos e₁ n<pos ∥ (λ v → weaken-ℕ v pos e₂)⟩
      weaken-ℕ n pos e₂
    ≡⟨ weaken-ℕ-< n pos e₂ n<pos ⟩
      n
    ⟨ weaken-ℕ-< n pos (e₁ + e₂) n<pos ⟩≡
      weaken-ℕ n pos (e₁ + e₂)
    ∎

  weaken-ℕ-comp₁ n {pos} {e₁} {e₂} | foo≥ n≥pos =
    begin
      weaken-ℕ (weaken-ℕ n pos e₁) pos e₂
    ≡⟨ weaken-ℕ-≥ n pos e₁ n≥pos ∥ (λ v → weaken-ℕ v pos e₂)⟩
      weaken-ℕ (n + e₁) pos e₂
    ≡⟨ M.comm n e₁ ∥ (λ v → weaken-ℕ v pos e₂)⟩
      weaken-ℕ (e₁ + n) pos e₂
    ≡⟨ weaken-ℕ-≥ (e₁ + n) pos e₂ (P.≤-steps e₁ n≥pos) ⟩
      (e₁ + n) + e₂
    ≡⟨ solve 3 (λ n e₁ e₂ → (e₁ :+ n) :+ e₂ := n :+ (e₁ :+ e₂)) refl n e₁ e₂ ⟩
      n + (e₁ + e₂)
    ⟨ weaken-ℕ-≥ n pos (e₁ + e₂) n≥pos ⟩≡
      weaken-ℕ n pos (e₁ + e₂)
    ∎

  weaken-ℕ-comp₂ : ∀ n {pos Δ-pos e₁ e₂} → weaken-ℕ (weaken-ℕ n pos e₁) (Δ-pos + pos) e₂ ≡ weaken-ℕ (weaken-ℕ n (Δ-pos ∸ e₁ + pos) e₂) pos e₁
  weaken-ℕ-comp₂ n {pos} {Δ-pos} {e₁} {e₂} with bar n pos
  weaken-ℕ-comp₂ n {pos} {Δ-pos} {e₁} {e₂} | foo< n<pos =
    begin
      weaken-ℕ (weaken-ℕ n pos e₁) (Δ-pos + pos) e₂
    ≡⟨ weaken-ℕ-< n pos e₁ n<pos ∥ (λ v → weaken-ℕ v (Δ-pos + pos) e₂) ⟩
      weaken-ℕ n (Δ-pos + pos) e₂
    ≡⟨ weaken-ℕ-< n (Δ-pos + pos) e₂ (P.≤-steps Δ-pos n<pos) ⟩
      n
    ⟨ weaken-ℕ-< n pos e₁ n<pos ⟩≡
      weaken-ℕ n pos e₁
    ⟨ weaken-ℕ-< n (Δ-pos ∸ e₁ + pos) e₂ (P.≤-steps (Δ-pos ∸ e₁) n<pos) ∥ (λ v → weaken-ℕ v pos e₁) ⟩≡
      weaken-ℕ (weaken-ℕ n (Δ-pos ∸ e₁ + pos) e₂) pos e₁
    ∎
  weaken-ℕ-comp₂ n {zero} {Δ-pos} {e₁} {e₂} | foo≥ z≤n with bar (n + e₁) Δ-pos
  weaken-ℕ-comp₂ n {zero} {Δ-pos} {e₁} {e₂} | foo≥ z≤n | foo< n+e₁<Δ-pos =
    begin
      weaken-ℕ (n + e₁) (Δ-pos + 0) e₂
    ≡⟨ M.comm Δ-pos 0 ∥ (λ v → weaken-ℕ (n + e₁) v e₂) ⟩
      weaken-ℕ (n + e₁) Δ-pos e₂
    ≡⟨ weaken-ℕ-< (n + e₁) Δ-pos e₂ n+e₁<Δ-pos ⟩
      n + e₁
    ⟨ weaken-ℕ-< n (Δ-pos ∸ e₁) e₂ (lemma1 n e₁ Δ-pos n+e₁<Δ-pos) ∥ (λ v → v + e₁) ⟩≡
      weaken-ℕ n (Δ-pos ∸ e₁) e₂ + e₁
    ≡⟨ M.comm 0 (Δ-pos ∸ e₁) ∥ (λ v → weaken-ℕ n v e₂ + e₁) ⟩
      weaken-ℕ n (Δ-pos ∸ e₁ + 0) e₂ + e₁
    ∎
  weaken-ℕ-comp₂ n {zero} {Δ-pos} {e₁} {e₂} | foo≥ z≤n | foo≥ n+e₁≥Δ-pos =
    begin
      weaken-ℕ (n + e₁) (Δ-pos + 0) e₂
    ≡⟨ M.comm Δ-pos 0 ∥ (λ v → weaken-ℕ (n + e₁) v e₂) ⟩
      weaken-ℕ (n + e₁) Δ-pos e₂
    ≡⟨ weaken-ℕ-≥ (n + e₁) Δ-pos e₂ n+e₁≥Δ-pos ⟩
      n + e₁ + e₂
    ≡⟨ solve 3 (λ n e₁ e₂ → n :+ e₁ :+ e₂ := n :+ e₂ :+ e₁) refl n e₁ e₂ ⟩
      n + e₂ + e₁
    ⟨ weaken-ℕ-≥ n (Δ-pos ∸ e₁) e₂ (lemma2 n e₁ Δ-pos n+e₁≥Δ-pos) ∥ (λ v → v + e₁) ⟩≡
      weaken-ℕ n (Δ-pos ∸ e₁) e₂ + e₁
    ⟨ M.comm (Δ-pos ∸ e₁) 0 ∥ (λ v → weaken-ℕ n v e₂ + e₁) ⟩≡
      weaken-ℕ n (Δ-pos ∸ e₁ + 0) e₂ + e₁
    ∎
  weaken-ℕ-comp₂ zero {suc pos} {Δ-pos} {e₁} {e₂} | foo≥ ()
  weaken-ℕ-comp₂ (suc n) {suc pos} {Δ-pos} {e₁} {e₂} | foo≥ n≥pos =
    begin
      weaken-ℕ (weaken-ℕ (suc n) (suc pos) e₁) (Δ-pos + suc pos) e₂
    ≡⟨ lemma3 Δ-pos pos ∥ (λ v → weaken-ℕ (weaken-ℕ (suc n) (suc pos) e₁) v e₂) ⟩
      weaken-ℕ (weaken-ℕ (suc n) (suc pos) e₁) (suc (Δ-pos + pos)) e₂
    ≡⟨ refl ⟩
      suc (weaken-ℕ (weaken-ℕ n pos e₁) (Δ-pos + pos) e₂)
    ≡⟨ weaken-ℕ-comp₂ n {pos} {Δ-pos} {e₁} {e₂} ∥ suc ⟩
      suc (weaken-ℕ (weaken-ℕ n (Δ-pos ∸ e₁ + pos) e₂) pos e₁)
    ≡⟨ refl ⟩
      weaken-ℕ (weaken-ℕ (suc n) (suc (Δ-pos ∸ e₁ + pos)) e₂) (suc pos) e₁
    ⟨ lemma3 (Δ-pos ∸ e₁) pos ∥ (λ v → weaken-ℕ (weaken-ℕ (suc n) v e₂) (suc pos) e₁) ⟩≡
      weaken-ℕ (weaken-ℕ (suc n) (Δ-pos ∸ e₁ + suc pos) e₂) (suc pos) e₁
    ∎

private
  mutual
    weaken-Ctx : Ctx → ℕ → ℕ → Ctx
    weaken-Ctx Ɛ pos e = Ɛ
    weaken-Ctx (Δ , a) pos e = weaken-Ctx' Δ pos e , weaken-CtxVal a pos e

    weaken-Ctx' : Ctx → ℕ → ℕ → Ctx
    weaken-Ctx' Δ zero e = Δ
    weaken-Ctx' Δ (suc pos) e = weaken-Ctx Δ pos e

    weaken-Ctx-id : ∀ Δ {pos} → weaken-Ctx Δ pos 0 ≡ Δ
    weaken-Ctx-id Ɛ = refl
    weaken-Ctx-id (Δ , a) {pos} = cong₂ _,_ (weaken-Ctx'-id Δ {pos}) (weaken-CtxVal-id a)

    weaken-Ctx'-id : ∀ Δ {pos} → weaken-Ctx' Δ pos 0 ≡ Δ
    weaken-Ctx'-id Δ {zero} = refl
    weaken-Ctx'-id Δ {suc pos} = weaken-Ctx-id Δ

    weaken-Ctx-comp₁ : ∀ Δ {pos e₁ e₂} → weaken-Ctx (weaken-Ctx Δ pos e₁) pos e₂ ≡ weaken-Ctx Δ pos (e₁ + e₂)
    weaken-Ctx-comp₁ Ɛ = refl
    weaken-Ctx-comp₁ (Δ , a) {pos} = cong₂ _,_ (weaken-Ctx'-comp₁ Δ {pos}) (weaken-CtxVal-comp₁ a)

    weaken-Ctx'-comp₁ : ∀ Δ {pos e₁ e₂} → weaken-Ctx' (weaken-Ctx' Δ pos e₁) pos e₂ ≡ weaken-Ctx' Δ pos (e₁ + e₂)
    weaken-Ctx'-comp₁ Δ {zero} = refl
    weaken-Ctx'-comp₁ Δ {suc pos} = weaken-Ctx-comp₁ Δ

    weaken-CtxVal : CtxVal → ℕ → ℕ → CtxVal
    weaken-CtxVal ρ pos e = ρ
    weaken-CtxVal (α σ) pos e = α (weaken-Stack σ pos e)
    weaken-CtxVal (β σ ♯b) pos e = β (weaken-Stack σ pos e) ♯b
    weaken-CtxVal (ℓ₁ ≤a ℓ₂ / σ) pos e = weaken-Lifetime ℓ₁ pos e ≤a weaken-Lifetime ℓ₂ pos e / weaken-Stack σ pos e

    weaken-CtxVal-id : ∀ a {pos} → weaken-CtxVal a pos 0 ≡ a
    weaken-CtxVal-id ρ = refl
    weaken-CtxVal-id (α σ) = cong α (weaken-Stack-id σ)
    weaken-CtxVal-id (β σ ♯b) = cong₂ β (weaken-Stack-id σ) refl
    weaken-CtxVal-id (ℓ₁ ≤a ℓ₂ / σ) = cong₃ _≤a_/_ (weaken-Lifetime-id ℓ₁) (weaken-Lifetime-id ℓ₂) (weaken-Stack-id σ)

    weaken-CtxVal-comp₁ : ∀ a {pos e₁ e₂} → weaken-CtxVal (weaken-CtxVal a pos e₁) pos e₂ ≡ weaken-CtxVal a pos (e₁ + e₂)
    weaken-CtxVal-comp₁ ρ = refl
    weaken-CtxVal-comp₁ (α σ) = cong α (weaken-Stack-comp₁ σ)
    weaken-CtxVal-comp₁ (β σ ♯b) = cong₂ β (weaken-Stack-comp₁ σ) refl
    weaken-CtxVal-comp₁ (ℓ₁ ≤a ℓ₂ / σ) = cong₃ _≤a_/_ (weaken-Lifetime-comp₁ ℓ₁) (weaken-Lifetime-comp₁ ℓ₂) (weaken-Stack-comp₁ σ)

    weaken-CtxVal-comp₂ : ∀ a {pos Δ-pos e₁ e₂} → weaken-CtxVal (weaken-CtxVal a pos e₁) (Δ-pos + pos) e₂ ≡ weaken-CtxVal (weaken-CtxVal a (Δ-pos ∸ e₁ + pos) e₂) pos e₁
    weaken-CtxVal-comp₂ ρ = refl
    weaken-CtxVal-comp₂ (α σ) = cong α (weaken-Stack-comp₂ σ)
    weaken-CtxVal-comp₂ (β σ ♯b) = cong₂ β (weaken-Stack-comp₂ σ) refl
    weaken-CtxVal-comp₂ (ℓ₁ ≤a ℓ₂ / σ) = cong₃ _≤a_/_ (weaken-Lifetime-comp₂ ℓ₁) (weaken-Lifetime-comp₂ ℓ₂) (weaken-Stack-comp₂ σ)

    weaken-Stack : Stack → ℕ → ℕ → Stack
    weaken-Stack nil pos e = nil
    weaken-Stack (v ∷ σ) pos e = weaken-StackVal v pos e ∷ weaken-Stack σ pos e
    weaken-Stack (ρ⁼ ι) pos e = ρ⁼ (weaken-ℕ ι pos e)

    weaken-Stack-id : ∀ σ {pos} → weaken-Stack σ pos 0 ≡ σ
    weaken-Stack-id nil = refl
    weaken-Stack-id (v ∷ σ) = cong₂ _∷_ (weaken-StackVal-id v) (weaken-Stack-id σ)
    weaken-Stack-id (ρ⁼ ι) {pos} = cong ρ⁼ (weaken-ℕ-id ι {pos})

    weaken-Stack-comp₁ : ∀ σ {pos e₁ e₂} → weaken-Stack (weaken-Stack σ pos e₁) pos e₂ ≡ weaken-Stack σ pos (e₁ + e₂)
    weaken-Stack-comp₁ nil = refl
    weaken-Stack-comp₁ (v ∷ σ) = cong₂ _∷_ (weaken-StackVal-comp₁ v) (weaken-Stack-comp₁ σ)
    weaken-Stack-comp₁ (ρ⁼ ι) {pos} = cong ρ⁼ (weaken-ℕ-comp₁ ι {pos})

    weaken-Stack-comp₂ : ∀ σ {pos Δ-pos e₁ e₂} → weaken-Stack (weaken-Stack σ pos e₁) (Δ-pos + pos) e₂ ≡ weaken-Stack (weaken-Stack σ (Δ-pos ∸ e₁ + pos) e₂) pos e₁
    weaken-Stack-comp₂ nil = refl
    weaken-Stack-comp₂ (v ∷ σ) = cong₂ _∷_ (weaken-StackVal-comp₂ v) (weaken-Stack-comp₂ σ)
    weaken-Stack-comp₂ (ρ⁼ ι) {pos} = cong ρ⁼ (weaken-ℕ-comp₂ ι {pos})

    weaken-StackVal : StackVal → ℕ → ℕ → StackVal
    weaken-StackVal (type τ) pos e = type (weaken-Type τ pos e)
    weaken-StackVal γ pos e = γ

    weaken-StackVal-id : ∀ v {pos} → weaken-StackVal v pos 0 ≡ v
    weaken-StackVal-id (type τ) = cong type (weaken-Type-id τ)
    weaken-StackVal-id γ = refl

    weaken-StackVal-comp₁ : ∀ v {pos e₁ e₂} → weaken-StackVal (weaken-StackVal v pos e₁) pos e₂ ≡ weaken-StackVal v pos (e₁ + e₂)
    weaken-StackVal-comp₁ (type τ) = cong type (weaken-Type-comp₁ τ)
    weaken-StackVal-comp₁ γ = refl

    weaken-StackVal-comp₂ : ∀ v {pos Δ-pos e₁ e₂} → weaken-StackVal (weaken-StackVal v pos e₁) (Δ-pos + pos) e₂ ≡ weaken-StackVal (weaken-StackVal v (Δ-pos ∸ e₁ + pos) e₂) pos e₁
    weaken-StackVal-comp₂ (type τ) = cong type (weaken-Type-comp₂ τ)
    weaken-StackVal-comp₂ γ = refl

    weaken-Type : Type → ℕ → ℕ → Type
    weaken-Type (β⁼ ι) pos e = β⁼ (weaken-ℕ ι pos e)
    weaken-Type int pos e = int
    weaken-Type (void ♯b) pos e = void ♯b
    weaken-Type (~ τ) pos e = ~ (weaken-Type τ pos e)
    weaken-Type (& ℓ q τ) pos e = & (weaken-Lifetime ℓ pos e) q (weaken-Type τ pos e)
    weaken-Type (∀[ Δ ] Γ) pos e = ∀[ Δ ] weaken-Register Γ (pos + length Δ) e

    weaken-Type-id : ∀ τ {pos} → weaken-Type τ pos 0 ≡ τ
    weaken-Type-id (β⁼ ι) {pos} = cong β⁼ (weaken-ℕ-id ι {pos})
    weaken-Type-id int = refl
    weaken-Type-id (void ♯b) = refl
    weaken-Type-id (~ τ) = cong ~ (weaken-Type-id τ)
    weaken-Type-id (& ℓ q τ) = cong₃ & (weaken-Lifetime-id ℓ) refl (weaken-Type-id τ)
    weaken-Type-id (∀[ Δ ] Γ) = cong₂ ∀[_]_ refl (weaken-Register-id Γ)

    weaken-Type-comp₁ : ∀ τ {pos e₁ e₂} → weaken-Type (weaken-Type τ pos e₁) pos e₂ ≡ weaken-Type τ pos (e₁ + e₂)
    weaken-Type-comp₁ (β⁼ ι) {pos} = cong β⁼ (weaken-ℕ-comp₁ ι {pos})
    weaken-Type-comp₁ int = refl
    weaken-Type-comp₁ (void ♯b) = refl
    weaken-Type-comp₁ (~ τ) = cong ~ (weaken-Type-comp₁ τ)
    weaken-Type-comp₁ (& ℓ q τ) = cong₃ & (weaken-Lifetime-comp₁ ℓ) refl (weaken-Type-comp₁ τ)
    weaken-Type-comp₁ (∀[ Δ ] Γ) = cong₂ ∀[_]_ refl (weaken-Register-comp₁ Γ)

    weaken-Type-comp₂ : ∀ τ {pos Δ-pos e₁ e₂} → weaken-Type (weaken-Type τ pos e₁) (Δ-pos + pos) e₂ ≡ weaken-Type (weaken-Type τ (Δ-pos ∸ e₁ + pos) e₂) pos e₁
    weaken-Type-comp₂ (β⁼ ι) {pos} = cong β⁼ (weaken-ℕ-comp₂ ι {pos})
    weaken-Type-comp₂ int = refl
    weaken-Type-comp₂ (void ♯b) = refl
    weaken-Type-comp₂ (~ τ) = cong ~ (weaken-Type-comp₂ τ)
    weaken-Type-comp₂ (& ℓ q τ) = cong₃ & (weaken-Lifetime-comp₂ ℓ) refl (weaken-Type-comp₂ τ)
    weaken-Type-comp₂ (∀[ Δ ] Γ) {pos} {Δ-pos} {e₁} {e₂} =
      begin
        weaken-Type (weaken-Type (∀[ Δ ] Γ) pos e₁) (Δ-pos + pos) e₂
      ≡⟨ refl ⟩
        ∀[ Δ ] weaken-Register (weaken-Register Γ (pos + length Δ) e₁) (Δ-pos + pos + length Δ) e₂
      ≡⟨ M.assoc Δ-pos pos (length Δ) ∥ (λ v → ∀[ Δ ] weaken-Register (weaken-Register Γ (pos + length Δ) e₁) v e₂) ⟩
        ∀[ Δ ] weaken-Register (weaken-Register Γ (pos + length Δ) e₁) (Δ-pos + (pos + length Δ)) e₂
      ≡⟨ weaken-Register-comp₂ Γ {pos + length Δ} ∥ (λ v → ∀[ Δ ] v) ⟩
        ∀[ Δ ] weaken-Register (weaken-Register Γ (Δ-pos ∸ e₁ + (pos + length Δ)) e₂) (pos + length Δ) e₁
      ⟨ M.assoc (Δ-pos ∸ e₁) pos (length Δ) ∥ (λ v → ∀[ Δ ] weaken-Register (weaken-Register Γ v e₂) (pos + length Δ) e₁) ⟩≡
        ∀[ Δ ] weaken-Register (weaken-Register Γ (Δ-pos ∸ e₁ + pos + length Δ) e₂) (pos + length Δ) e₁
      ≡⟨ refl ⟩
        weaken-Type (weaken-Type (∀[ Δ ] Γ) (Δ-pos ∸ e₁ + pos) e₂) pos e₁
      ∎

    weaken-Types : ∀ {m} → Vec Type m → ℕ → ℕ → Vec Type m
    weaken-Types [] pos e = []
    weaken-Types (τ ∷ τs) pos e = weaken-Type τ pos e ∷ weaken-Types τs pos e

    weaken-Types-id : ∀ {m} (τs : Vec Type m) {pos} → weaken-Types τs pos 0 ≡ τs
    weaken-Types-id [] = refl
    weaken-Types-id (τ ∷ τs) = cong₂ _∷_ (weaken-Type-id τ) (weaken-Types-id τs)

    weaken-Types-comp₁ : ∀ {m} (τs : Vec Type m) {pos e₁ e₂} → weaken-Types (weaken-Types τs pos e₁) pos e₂ ≡ weaken-Types τs pos (e₁ + e₂)
    weaken-Types-comp₁ [] = refl
    weaken-Types-comp₁ (τ ∷ τs) = cong₂ _∷_ (weaken-Type-comp₁ τ) (weaken-Types-comp₁ τs)

    weaken-Types-comp₂ : ∀ {m} (τs : Vec Type m) {pos Δ-pos e₁ e₂} → weaken-Types (weaken-Types τs pos e₁) (Δ-pos + pos) e₂ ≡ weaken-Types (weaken-Types τs (Δ-pos ∸ e₁ + pos) e₂) pos e₁
    weaken-Types-comp₂ [] = refl
    weaken-Types-comp₂ (τ ∷ τs) = cong₂ _∷_ (weaken-Type-comp₂ τ) (weaken-Types-comp₂ τs)

    weaken-Register : Register → ℕ → ℕ → Register
    weaken-Register (register sp regs) pos e = register (weaken-Stack sp pos e) (weaken-Types regs pos e)

    weaken-Register-id : ∀ Γ {pos} → weaken-Register Γ pos 0 ≡ Γ
    weaken-Register-id (register sp regs) = cong₂ register (weaken-Stack-id sp) (weaken-Types-id regs)

    weaken-Register-comp₁ : ∀ Γ {pos e₁ e₂} → weaken-Register (weaken-Register Γ pos e₁) pos e₂ ≡ weaken-Register Γ pos (e₁ + e₂)
    weaken-Register-comp₁ (register sp regs) = cong₂ register (weaken-Stack-comp₁ sp) (weaken-Types-comp₁ regs)

    weaken-Register-comp₂ : ∀ Γ {pos Δ-pos e₁ e₂} → weaken-Register (weaken-Register Γ pos e₁) (Δ-pos + pos) e₂ ≡ weaken-Register (weaken-Register Γ (Δ-pos ∸ e₁ + pos) e₂) pos e₁
    weaken-Register-comp₂ (register sp regs) = cong₂ register (weaken-Stack-comp₂ sp) (weaken-Types-comp₂ regs)

    weaken-Lifetime : Lifetime → ℕ → ℕ → Lifetime
    weaken-Lifetime (α⁼ ι) pos e = α⁼ (weaken-ℕ ι pos e)
    weaken-Lifetime (γ⁼ ι) pos e = γ⁼ ι
    weaken-Lifetime static pos e = static

    weaken-Lifetime-id : ∀ ℓ {pos} → weaken-Lifetime ℓ pos 0 ≡ ℓ
    weaken-Lifetime-id (α⁼ ι) {pos} = cong α⁼ (weaken-ℕ-id ι {pos})
    weaken-Lifetime-id (γ⁼ ι) = refl
    weaken-Lifetime-id static = refl

    weaken-Lifetime-comp₁ : ∀ ℓ {pos e₁ e₂} → weaken-Lifetime (weaken-Lifetime ℓ pos e₁) pos e₂ ≡ weaken-Lifetime ℓ pos (e₁ + e₂)
    weaken-Lifetime-comp₁ (α⁼ ι) {pos} = cong α⁼ (weaken-ℕ-comp₁ ι {pos})
    weaken-Lifetime-comp₁ (γ⁼ ι) = refl
    weaken-Lifetime-comp₁ static = refl

    weaken-Lifetime-comp₂ : ∀ ℓ {pos Δ-pos e₁ e₂} → weaken-Lifetime (weaken-Lifetime ℓ pos e₁) (Δ-pos + pos) e₂ ≡ weaken-Lifetime (weaken-Lifetime ℓ (Δ-pos ∸ e₁ + pos) e₂) pos e₁
    weaken-Lifetime-comp₂ (α⁼ ι) {pos} = cong α⁼ (weaken-ℕ-comp₂ ι {pos})
    weaken-Lifetime-comp₂ (γ⁼ ι) = refl
    weaken-Lifetime-comp₂ static = refl

record Weaken {a} (A : Set a) : Set a where
  field
    weaken : A → ℕ → ℕ → A
    weaken-id : ∀ x {pos} → weaken x pos 0 ≡ x
    weaken-comp₁ : ∀ x {pos e₁ e₂} → weaken (weaken x pos e₁) pos e₂ ≡ weaken x pos (e₁ + e₂)
  weakenʰ : A → Ctx → Ctx → A
  weakenʰ a Δ₂ Δₑ = weaken a (length Δ₂) (length Δₑ)

  weaken¹ : A → A
  weaken¹ a = weaken a 0 1
open Weaken {{...}} public

record Weaken⁺ {a} (A : Set a) {{W : Weaken A}} : Set a where
  field
    weaken-comp₂ : ∀ (x : A) {pos Δ-pos e₁ e₂} → weaken (weaken x pos e₁) (Δ-pos + pos) e₂ ≡ weaken (weaken x (Δ-pos ∸ e₁ + pos) e₂) pos e₁

  weaken-comp-≤ : ∀ (x : A) {pos Δ-pos e₁ e₂} {{_ : Δ-pos ≤ e₁}} → weaken (weaken x pos e₁) (Δ-pos + pos) e₂ ≡ weaken x pos (e₁ + e₂)
  weaken-comp-≤ x {pos} {Δ-pos} {e₁} {e₂} {{Δ-pos≤e₁}} =
    begin
      weaken (weaken x pos e₁) (Δ-pos + pos) e₂
    ≡⟨ weaken-comp₂ x ⟩
      weaken (weaken x (Δ-pos ∸ e₁ + pos) e₂) pos e₁
    ≡⟨ lemma4 Δ-pos≤e₁ ∥ (λ v → weaken (weaken x (v + pos) e₂) pos e₁) ⟩
      weaken (weaken x pos e₂) pos e₁
    ≡⟨ weaken-comp₁ x ⟩
      weaken x pos (e₂ + e₁)
    ≡⟨ M.comm e₂ e₁ ∥ weaken x pos ⟩
      weaken x pos (e₁ + e₂)
    ∎

open Weaken⁺ {{...}} public

instance
  Weaken-ℕ : Weaken ℕ
  Weaken-ℕ = record { weaken = weaken-ℕ
                    ; weaken-id = weaken-ℕ-id
                    ; weaken-comp₁ = weaken-ℕ-comp₁ }

  Weaken⁺-ℕ : Weaken⁺ ℕ
  Weaken⁺-ℕ = record { weaken-comp₂ = weaken-ℕ-comp₂ }

  Weaken-Ctx : Weaken Ctx
  Weaken-Ctx = record { weaken = weaken-Ctx
                      ; weaken-id = weaken-Ctx-id
                      ; weaken-comp₁ = weaken-Ctx-comp₁ }

  Weaken-CtxVal : Weaken CtxVal
  Weaken-CtxVal = record { weaken = weaken-CtxVal
                         ; weaken-id = weaken-CtxVal-id
                         ; weaken-comp₁ = weaken-CtxVal-comp₁ }

  Weaken⁺-CtxVal : Weaken⁺ CtxVal
  Weaken⁺-CtxVal = record { weaken-comp₂ = weaken-CtxVal-comp₂ }

  Weaken-Stack : Weaken Stack
  Weaken-Stack = record { weaken = weaken-Stack
                         ; weaken-id = weaken-Stack-id
                         ; weaken-comp₁ = weaken-Stack-comp₁ }

  Weaken⁺-Stack : Weaken⁺ Stack
  Weaken⁺-Stack = record { weaken-comp₂ = weaken-Stack-comp₂ }

  Weaken-StackVal : Weaken StackVal
  Weaken-StackVal = record { weaken = weaken-StackVal
                         ; weaken-id = weaken-StackVal-id
                         ; weaken-comp₁ = weaken-StackVal-comp₁ }

  Weaken⁺-StackVal : Weaken⁺ StackVal
  Weaken⁺-StackVal = record { weaken-comp₂ = weaken-StackVal-comp₂ }

  Weaken-Type : Weaken Type
  Weaken-Type = record { weaken = weaken-Type
                         ; weaken-id = weaken-Type-id
                         ; weaken-comp₁ = weaken-Type-comp₁ }

  Weaken⁺-Type : Weaken⁺ Type
  Weaken⁺-Type = record { weaken-comp₂ = weaken-Type-comp₂ }

  Weaken-Register : Weaken Register
  Weaken-Register = record { weaken = weaken-Register
                         ; weaken-id = weaken-Register-id
                         ; weaken-comp₁ = weaken-Register-comp₁ }

  Weaken⁺-Register : Weaken⁺ Register
  Weaken⁺-Register = record { weaken-comp₂ = weaken-Register-comp₂ }

  Weaken-Lifetime : Weaken Lifetime
  Weaken-Lifetime = record { weaken = weaken-Lifetime
                         ; weaken-id = weaken-Lifetime-id
                         ; weaken-comp₁ = weaken-Lifetime-comp₁ }

  Weaken⁺-Lifetime : Weaken⁺ Lifetime
  Weaken⁺-Lifetime = record { weaken-comp₂ = weaken-Lifetime-comp₂ }


Weaken-Ctx' : Weaken Ctx
Weaken-Ctx' = record { weaken = weaken-Ctx' ; weaken-id = weaken-Ctx'-id ; weaken-comp₁ = weaken-Ctx'-comp₁ }

infix 4 _↓ₐ_≡_ _↓ᵥ_≡_ _⊏_

data _↓ₐ_≡_ : Ctx → ℕ → CtxVal → Set where
  here  :
        ∀ {Δ a} →
    -----------------
    Δ , a ↓ₐ zero ≡ a

  there :
          ∀ {Δ a₁ a₂ ι} →
           Δ ↓ₐ ι ≡ a₁ →
    ----------------------------
    Δ , a₂ ↓ₐ suc ι ≡ weaken¹ a₁

data _↓ᵥ_≡_ : Stack → ℕ → StackVal → Set where
  here :
         ∀ {σ v} →
    -----------------
    v ∷ σ ↓ᵥ zero ≡ v

  there :
       ∀ {σ v₁ v₂ ι} →
        σ ↓ᵥ ι ≡ v₁ →
    --------------------
    v₂ ∷ σ ↓ᵥ suc ι ≡ v₁

data _⊏_ : Stack → Stack → Set where
  here  : ∀ {σ}      → σ ⊏ σ
  there : ∀ {σ σ' v} → σ ⊏ σ' → σ ⊏ v ∷ σ'
