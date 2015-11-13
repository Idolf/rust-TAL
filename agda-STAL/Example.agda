open import Util
open import Judgments
open import Lemmas

-- Static type checking
foo-word : SmallValue
foo-word = Λ [] ∙ globval 0 ⟦ α (α⁼ 0) ∷ α (α⁼ 1) ∷ α (α⁼ 2) ∷ α (α⁼ 3) ∷ ρ (ρ⁼ 4) ∷ [] ⟧

foo : InstructionSequence
foo = jmp foo-word

foo-Γ : RegisterAssignment
foo-Γ = registerₐ (ρ⁼ 4) (α⁼ 0 ∷ α⁼ 1 ∷ α⁼ 2 ∷ α⁼ 3 ∷ [])

foo-Δ : TypeAssumptions
foo-Δ = α ∷ α ∷ α ∷ α ∷ ρ ∷ []

foo-τ : Type
foo-τ = ∀[ foo-Δ  ] foo-Γ

foo-is : [ foo-τ ] , foo-Δ , foo-Γ ⊢ foo instructionsequence
foo-is = of-jmp (of-Λ (of-globval here (≤-refl (valid-∀ (valid-registerₐ (valid-ρ⁼ (there (there (there (there here))))) (valid-α⁼ here ∷ valid-α⁼ (there here) ∷ valid-α⁼ (there (there here)) ∷ valid-α⁼ (there (there (there here))) ∷ []))))) (of-α (valid-α⁼ here) ∷ of-α (valid-α⁼ (there here)) ∷ of-α (valid-α⁼ (there (there here))) ∷ of-α (valid-α⁼ (there (there (there here)))) ∷ of-ρ (valid-ρ⁼ (there (there (there (there here))))) ∷ []) ((registerₐ (ρ⁼ (suc (suc (suc (suc zero))))) (α⁼ zero ∷ α⁼ (suc zero) ∷ α⁼ (suc (suc zero)) ∷ α⁼ (suc (suc (suc zero))) ∷ [])) , ((subst-registerₐ (subst-ρ-< (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) (subst-α-< (s≤s z≤n) ∷ subst-α-< (s≤s (s≤s z≤n)) ∷ subst-α-< (s≤s (s≤s (s≤s z≤n))) ∷ subst-α-< (s≤s (s≤s (s≤s (s≤s z≤n)))) ∷ [])) , ((registerₐ (ρ⁼ (suc (suc (suc (suc zero))))) (α⁼ zero ∷ α⁼ (suc zero) ∷ α⁼ (suc (suc zero)) ∷ α⁼ (suc (suc (suc zero))) ∷ [])) , ((subst-registerₐ (subst-ρ-< (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) (subst-α-< (s≤s z≤n) ∷ subst-α-< (s≤s (s≤s z≤n)) ∷ subst-α-< (s≤s (s≤s (s≤s z≤n))) ∷ subst-α-< (s≤s (s≤s (s≤s (s≤s z≤n)))) ∷ [])) , ((registerₐ (ρ⁼ (suc (suc (suc (suc zero))))) (α⁼ zero ∷ α⁼ (suc zero) ∷ α⁼ (suc (suc zero)) ∷ α⁼ (suc (suc (suc zero))) ∷ [])) , ((subst-registerₐ (subst-ρ-< (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) (subst-α-< (s≤s z≤n) ∷ subst-α-< (s≤s (s≤s z≤n)) ∷ subst-α-< (s≤s (s≤s (s≤s z≤n))) ∷ subst-α-< (s≤s (s≤s (s≤s (s≤s z≤n)))) ∷ [])) , ((registerₐ (ρ⁼ (suc (suc (suc (suc zero))))) (α⁼ zero ∷ α⁼ (suc zero) ∷ α⁼ (suc (suc zero)) ∷ α⁼ (suc (suc (suc zero))) ∷ [])) , ((subst-registerₐ (subst-ρ-< (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) (subst-α-< (s≤s z≤n) ∷ subst-α-< (s≤s (s≤s z≤n)) ∷ subst-α-< (s≤s (s≤s (s≤s z≤n))) ∷ subst-α-< (s≤s (s≤s (s≤s (s≤s z≤n)))) ∷ [])) , ((registerₐ (ρ⁼ (suc (suc (suc (suc zero))))) (α⁼ zero ∷ α⁼ (suc zero) ∷ α⁼ (suc (suc zero)) ∷ α⁼ (suc (suc (suc zero))) ∷ [])) , ((subst-registerₐ (subst-ρ-< (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) (subst-α-< (s≤s z≤n) ∷ subst-α-< (s≤s (s≤s z≤n)) ∷ subst-α-< (s≤s (s≤s (s≤s z≤n))) ∷ subst-α-< (s≤s (s≤s (s≤s (s≤s z≤n)))) ∷ [])) , refl)))))))))) (Γ-≤ (ρ⁼-≤ (there (there (there (there here))))) (α⁼-≤ here ∷ α⁼-≤ (there here) ∷ α⁼-≤ (there (there here)) ∷ α⁼-≤ (there (there (there here))) ∷ []))) (Γ-≤ (ρ⁼-≤ (there (there (there (there here))))) (α⁼-≤ here ∷ α⁼-≤ (there here) ∷ α⁼-≤ (there (there here)) ∷ α⁼-≤ (there (there (there here))) ∷ []))

-- Dynamic type-checking
foo-word' : SmallValue
foo-word' = Λ [] ∙ globval 0 ⟦ α int ∷ α int ∷ α int ∷ α int ∷ ρ [] ∷ [] ⟧

foo' : InstructionSequence
foo' = jmp foo-word'

int-reg : RegisterFile
int-reg = register [] (int 0 ∷ int 1 ∷ int 2 ∷ int 3 ∷ [])

foo-G : Globals
foo-G = [ code[ foo-Δ ] foo-Γ ∙ foo ]

foo'-program : foo-G ⊢ [] , int-reg , foo' program
foo'-program = of-program (of-globals (of-gval (valid-registerₐ (valid-ρ⁼ (there (there (there (there here))))) (valid-α⁼ here ∷ valid-α⁼ (there here) ∷ valid-α⁼ (there (there here)) ∷ valid-α⁼ (there (there (there here))) ∷ [])) foo-is ∷ [])) (of-heap []) (of-register [] (of-int ∷ (of-int ∷ (of-int ∷ of-int ∷ [])))) (of-jmp (of-Λ (of-globval here (≤-refl (valid-∀ (valid-registerₐ (valid-ρ⁼ (there (there (there (there here))))) (valid-α⁼ here ∷ valid-α⁼ (there here) ∷ valid-α⁼ (there (there here)) ∷ valid-α⁼ (there (there (there here))) ∷ []))))) (of-α valid-int ∷ of-α valid-int ∷ of-α valid-int ∷ of-α valid-int ∷ of-ρ [] ∷ []) (registerₐ (ρ⁼ (suc (suc (suc zero)))) (int ∷ α⁼ zero ∷ α⁼ (suc zero) ∷ α⁼ (suc (suc zero)) ∷ []) , (subst-registerₐ (subst-ρ-> (s≤s z≤n)) (subst-α-≡ ∷ subst-α-> (s≤s z≤n) ∷ subst-α-> (s≤s z≤n) ∷ subst-α-> (s≤s z≤n) ∷ [])) , ((registerₐ (ρ⁼ (suc (suc zero))) (int ∷ int ∷ α⁼ zero ∷ α⁼ (suc zero) ∷ [])) , ((subst-registerₐ (subst-ρ-> (s≤s z≤n)) (subst-int ∷ subst-α-≡ ∷ subst-α-> (s≤s z≤n) ∷ subst-α-> (s≤s z≤n) ∷ [])) , ((registerₐ (ρ⁼ (suc zero)) (int ∷ int ∷ int ∷ α⁼ zero ∷ [])) , ((subst-registerₐ (subst-ρ-> (s≤s z≤n)) (subst-int ∷ subst-int ∷ subst-α-≡ ∷ subst-α-> (s≤s z≤n) ∷ [])) , ((registerₐ (ρ⁼ zero) (int ∷ int ∷ int ∷ int ∷ [])) , ((subst-registerₐ (subst-ρ-> (s≤s z≤n)) (subst-int ∷ subst-int ∷ subst-int ∷ subst-α-≡ ∷ [])) , ((registerₐ [] (int ∷ int ∷ int ∷ int ∷ [])) , ((subst-registerₐ subst-ρ-≡ (subst-int ∷ subst-int ∷ subst-int ∷ subst-int ∷ [])) , refl))))))))) (Γ-≤ [] (int-≤ ∷ int-≤ ∷ int-≤ ∷ int-≤ ∷ []))) (Γ-≤ [] (int-≤ ∷ int-≤ ∷ int-≤ ∷ int-≤ ∷ [])))

-- Execution
foo-exec : ∀ {H R} → foo-G ⊢ H , R , foo' ⇒ H , R , foo'
foo-exec {R = register sp stack} = step-jmp (instantiate-Λ (instantiate-globval here) ((jmp Λ [] ∙ globval zero ⟦ α int ∷ α (α⁼ zero) ∷ α (α⁼ (suc zero)) ∷ α (α⁼ (suc (suc zero))) ∷ ρ (ρ⁼ (suc (suc (suc zero)))) ∷ [] ⟧) , ((subst-jmp (subst-Λ subst-globval (subst-α subst-α-≡ ∷ subst-α (subst-α-> (s≤s z≤n)) ∷ subst-α (subst-α-> (s≤s z≤n)) ∷ subst-α (subst-α-> (s≤s z≤n)) ∷ subst-ρ (subst-ρ-> (s≤s z≤n)) ∷ []))) , ((jmp Λ [] ∙ globval zero ⟦ α int ∷ α int ∷ α (α⁼ zero) ∷ α (α⁼ (suc zero)) ∷ ρ (ρ⁼ (suc (suc zero))) ∷ [] ⟧) , ((subst-jmp (subst-Λ subst-globval (subst-α subst-int ∷ subst-α subst-α-≡ ∷ subst-α (subst-α-> (s≤s z≤n)) ∷ subst-α (subst-α-> (s≤s z≤n)) ∷ subst-ρ (subst-ρ-> (s≤s z≤n)) ∷ []))) , ((jmp Λ [] ∙ globval zero ⟦ α int ∷ α int ∷ α int ∷ α (α⁼ zero) ∷ ρ (ρ⁼ (suc zero)) ∷ [] ⟧) , ((subst-jmp (subst-Λ subst-globval (subst-α subst-int ∷ subst-α subst-int ∷ subst-α subst-α-≡ ∷ subst-α (subst-α-> (s≤s z≤n)) ∷ subst-ρ (subst-ρ-> (s≤s z≤n)) ∷ []))) , ((jmp Λ [] ∙ globval zero ⟦ α int ∷ α int ∷ α int ∷ α int ∷ ρ (ρ⁼ zero) ∷ [] ⟧) , ((subst-jmp (subst-Λ subst-globval (subst-α subst-int ∷ subst-α subst-int ∷ subst-α subst-int ∷ subst-α subst-α-≡ ∷ subst-ρ (subst-ρ-> (s≤s z≤n)) ∷ []))) , ((jmp Λ [] ∙ globval zero ⟦ α int ∷ α int ∷ α int ∷ α int ∷ ρ [] ∷ [] ⟧) , ((subst-jmp (subst-Λ subst-globval (subst-α subst-int ∷ subst-α subst-int ∷ subst-α subst-int ∷ subst-α subst-int ∷ subst-ρ subst-ρ-≡ ∷ []))) , refl)))))))))))
