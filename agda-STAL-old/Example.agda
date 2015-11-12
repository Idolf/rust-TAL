open import Util
open import Judgments
open import Lemmas

-- Static type checking
foo-word : WordValue
foo-word = globval 0 5 ⟦⟦ α (α⁼ 4) ∷ α (α⁼ 4) ∷ α (α⁼ 4) ∷ α (α⁼ 4) ∷ ρ (ρ⁼ 4) ∷ [] ⟧⟧

foo : InstructionSequence
foo = jmp (word foo-word)

foo-Γ : RegisterAssignment
foo-Γ = registerₐ (ρ⁼ 4) (α⁼ 0 ∷ α⁼ 1 ∷ α⁼ 2 ∷ α⁼ 3 ∷ [])

foo-Δ : TypeAssignment
foo-Δ = α ∷ α ∷ α ∷ α ∷ ρ ∷ []

foo-τ : Type
foo-τ = ∀[ foo-Δ  ] foo-Γ

foo-is : [ foo-τ ] , foo-Δ , foo-Γ ⊢ foo instructionsequence
foo-is = of-jmp (of-word (of-inst (of-inst (of-inst (of-inst (of-inst (of-globval here (∀-≤ (valid-α ∷ valid-α ∷ valid-α ∷ valid-α ∷ valid-ρ ∷ []) (Γ-≤ (ρ⁼-≤ (there (there (there (there here))))) (α⁼-≤ here ∷ α⁼-≤ (there here) ∷ α⁼-≤ (there (there here)) ∷ α⁼-≤ (there (there (there here))) ∷ []))) refl) (valid-zero (valid-inst (valid-α (valid-α⁼ (there (there (there (there here)))))))) (run-inst match-α) (subst-registerₐ (subst-ρ-¬inst (subst-inst-> (s≤s z≤n))) (subst-α-inst (subst-α-¬inst (subst-weaken-≥ z≤n)) ∷ subst-α-¬inst (subst-inst-> (s≤s z≤n)) ∷ subst-α-¬inst (subst-inst-> (s≤s z≤n)) ∷ subst-α-¬inst (subst-inst-> (s≤s z≤n)) ∷ [])) (Γ-≤ (ρ⁼-≤ (there (there (there here)))) (α⁼-≤ (there (there (there (there here)))) ∷ α⁼-≤ here ∷ α⁼-≤ (there here) ∷ α⁼-≤ (there (there here)) ∷ []))) (valid-zero (valid-inst (valid-α (valid-α⁼ (there (there (there (there here)))))))) (run-inst match-α) (subst-registerₐ (subst-ρ-¬inst (subst-inst-> (s≤s z≤n))) (subst-α-¬inst (subst-inst-> (s≤s z≤n)) ∷ subst-α-inst (subst-α-¬inst (subst-weaken-≥ z≤n)) ∷ subst-α-¬inst (subst-inst-> (s≤s z≤n)) ∷ subst-α-¬inst (subst-inst-> (s≤s z≤n)) ∷ [])) (Γ-≤ (ρ⁼-≤ (there (there here))) (α⁼-≤ (there (there (there here))) ∷ α⁼-≤ (there (there (there (there here)))) ∷ α⁼-≤ here ∷ α⁼-≤ (there here) ∷ []))) (valid-zero (valid-inst (valid-α (valid-α⁼ (there (there (there (there here)))))))) (run-inst match-α) (subst-registerₐ (subst-ρ-¬inst (subst-inst-> (s≤s z≤n))) (subst-α-¬inst (subst-inst-> (s≤s z≤n)) ∷ subst-α-¬inst (subst-inst-> (s≤s z≤n)) ∷ subst-α-inst (subst-α-¬inst (subst-weaken-≥ z≤n)) ∷ subst-α-¬inst (subst-inst-> (s≤s z≤n)) ∷ [])) (Γ-≤ (ρ⁼-≤ (there here)) (α⁼-≤ (there (there here)) ∷ α⁼-≤ (there (there (there here))) ∷ α⁼-≤ (there (there (there (there here)))) ∷ α⁼-≤ here ∷ []))) (valid-zero (valid-inst (valid-α (valid-α⁼ (there (there (there (there here)))))))) (run-inst match-α) (subst-registerₐ (subst-ρ-¬inst (subst-inst-> (s≤s z≤n))) (subst-α-¬inst (subst-inst-> (s≤s z≤n)) ∷ subst-α-¬inst (subst-inst-> (s≤s z≤n)) ∷ subst-α-¬inst (subst-inst-> (s≤s z≤n)) ∷ subst-α-inst (subst-α-¬inst (subst-weaken-≥ z≤n)) ∷ [])) (Γ-≤ (ρ⁼-≤ here) (α⁼-≤ (there here) ∷ α⁼-≤ (there (there here)) ∷ α⁼-≤ (there (there (there here))) ∷ α⁼-≤ (there (there (there (there here)))) ∷ []))) (valid-zero (valid-inst (valid-ρ (valid-ρ⁼ (there (there (there (there here)))))))) (run-inst match-ρ) (subst-registerₐ (subst-ρ-inst (subst-ρ-¬inst (subst-weaken-≥ z≤n))) (subst-α-¬inst (subst-inst-> (s≤s z≤n)) ∷ subst-α-¬inst (subst-inst-> (s≤s z≤n)) ∷ subst-α-¬inst (subst-inst-> (s≤s z≤n)) ∷ subst-α-¬inst (subst-inst-> (s≤s z≤n)) ∷ [])) (Γ-≤ (ρ⁼-≤ (there (there (there (there here))))) (α⁼-≤ here ∷ α⁼-≤ (there here) ∷ α⁼-≤ (there (there here)) ∷ α⁼-≤ (there (there (there here))) ∷ [])))) (Γ-≤ (ρ⁼-≤ (there (there (there (there here))))) (α⁼-≤ here ∷ α⁼-≤ (there here) ∷ α⁼-≤ (there (there here)) ∷ α⁼-≤ (there (there (there here))) ∷ []))

-- Dynamic type-checking
foo-word' : WordValue
foo-word' = globval 0 5 ⟦⟦ α int ∷ α int ∷ α int ∷ α int ∷ ρ [] ∷ [] ⟧⟧

foo' : InstructionSequence
foo' = jmp (word foo-word')

int-reg : RegisterFile
int-reg = register [] (int 0 ∷ int 1 ∷ int 2 ∷ int 3 ∷ [])

foo-G : Globals
foo-G = [ code[ foo-Δ ] foo-Γ ∙ foo ]

foo'-program : foo-G ⊢ [] , int-reg , foo' program
foo'-program = of-program (of-globals ((of-gval (valid-α ∷ valid-α ∷ valid-α ∷ valid-α ∷ valid-ρ ∷ []) (valid-registerₐ (valid-ρ⁼ (there (there (there (there here))))) (valid-α⁼ here ∷ valid-α⁼ (there here) ∷ valid-α⁼ (there (there here)) ∷ valid-α⁼ (there (there (there here))) ∷ [])) foo-is) ∷ [])) (of-heap []) (of-register [] (of-int ∷ of-int ∷ of-int ∷ of-int ∷ [])) (of-jmp (of-word (of-inst (of-inst (of-inst (of-inst (of-inst (of-globval here (∀-≤ (valid-α ∷ valid-α ∷ valid-α ∷ valid-α ∷ valid-ρ ∷ []) (Γ-≤ (ρ⁼-≤ (there (there (there (there here))))) (α⁼-≤ here ∷ α⁼-≤ (there here) ∷ α⁼-≤ (there (there here)) ∷ α⁼-≤ (there (there (there here))) ∷ []))) refl) (valid-zero (valid-inst (valid-α valid-int))) (run-inst match-α) (subst-registerₐ (subst-ρ-¬inst (subst-inst-> (s≤s z≤n))) (subst-α-inst subst-int ∷ subst-α-¬inst (subst-inst-> (s≤s z≤n)) ∷ subst-α-¬inst (subst-inst-> (s≤s z≤n)) ∷ subst-α-¬inst (subst-inst-> (s≤s z≤n)) ∷ [])) (Γ-≤ (ρ⁼-≤ (there (there (there here)))) (int-≤ ∷ α⁼-≤ here ∷ α⁼-≤ (there here) ∷ α⁼-≤ (there (there here)) ∷ []))) (valid-zero (valid-inst (valid-α valid-int))) (run-inst match-α) (subst-registerₐ (subst-ρ-¬inst (subst-inst-> (s≤s z≤n))) (subst-int ∷ subst-α-inst subst-int ∷ subst-α-¬inst (subst-inst-> (s≤s z≤n)) ∷ subst-α-¬inst (subst-inst-> (s≤s z≤n)) ∷ [])) (Γ-≤ (ρ⁼-≤ (there (there here))) (int-≤ ∷ int-≤ ∷ α⁼-≤ here ∷ α⁼-≤ (there here) ∷ []))) (valid-zero (valid-inst (valid-α valid-int))) (run-inst match-α) (subst-registerₐ (subst-ρ-¬inst (subst-inst-> (s≤s z≤n))) (subst-int ∷ subst-int ∷ subst-α-inst subst-int ∷ subst-α-¬inst (subst-inst-> (s≤s z≤n)) ∷ [])) (Γ-≤ (ρ⁼-≤ (there here)) (int-≤ ∷ int-≤ ∷ int-≤ ∷ α⁼-≤ here ∷ []))) (valid-zero (valid-inst (valid-α valid-int))) (run-inst match-α) (subst-registerₐ (subst-ρ-¬inst (subst-inst-> (s≤s z≤n))) (subst-int ∷ subst-int ∷ subst-int ∷ subst-α-inst subst-int ∷ [])) (Γ-≤ (ρ⁼-≤ here) (int-≤ ∷ int-≤ ∷ int-≤ ∷ int-≤ ∷ []))) (valid-zero (valid-inst (valid-ρ valid-[]))) (run-inst match-ρ) (subst-registerₐ (subst-ρ-inst subst-[]) (subst-int ∷ subst-int ∷ subst-int ∷ subst-int ∷ [])) (Γ-≤ [] (int-≤ ∷ int-≤ ∷ int-≤ ∷ int-≤ ∷ [])))) (Γ-≤ [] (int-≤ ∷ int-≤ ∷ int-≤ ∷ int-≤ ∷ [])))

-- -- Execution
foo-exec : ∀ {H R} → foo-G ⊢ H , R , foo' ⇒ H , R , foo'
foo-exec {R = register sp stack} = exec-jmp (instantiate-⟦⟧ (instantiate-⟦⟧ (instantiate-⟦⟧ (instantiate-⟦⟧ (instantiate-⟦⟧ (instantiate-globval here) (subst-jmp (subst-word (subst-⟦⟧ (subst-⟦⟧ (subst-⟦⟧ (subst-⟦⟧ (subst-⟦⟧ subst-globval (subst-inst (subst-α (subst-α-inst subst-int)))) (subst-inst (subst-α (subst-α-¬inst (subst-inst-> (s≤s (s≤s (s≤s (s≤s z≤n))))))))) (subst-inst (subst-α (subst-α-¬inst (subst-inst-> (s≤s (s≤s (s≤s z≤n)))))))) (subst-inst (subst-α (subst-α-¬inst (subst-inst-> (s≤s (s≤s z≤n))))))) (subst-inst (subst-ρ (subst-ρ-¬inst (subst-inst-> (s≤s z≤n))))))))) (subst-jmp (subst-word (subst-⟦⟧ (subst-⟦⟧ (subst-⟦⟧ (subst-⟦⟧ (subst-⟦⟧ subst-globval (subst-inst (subst-α subst-int))) (subst-inst (subst-α (subst-α-inst subst-int)))) (subst-inst (subst-α (subst-α-¬inst (subst-inst-> (s≤s (s≤s (s≤s z≤n)))))))) (subst-inst (subst-α (subst-α-¬inst (subst-inst-> (s≤s (s≤s z≤n))))))) (subst-inst (subst-ρ (subst-ρ-¬inst (subst-inst-> (s≤s z≤n))))))))) (subst-jmp (subst-word (subst-⟦⟧ (subst-⟦⟧ (subst-⟦⟧ (subst-⟦⟧ (subst-⟦⟧ subst-globval (subst-inst (subst-α subst-int))) (subst-inst (subst-α subst-int))) (subst-inst (subst-α (subst-α-inst subst-int)))) (subst-inst (subst-α (subst-α-¬inst (subst-inst-> (s≤s (s≤s z≤n))))))) (subst-inst (subst-ρ (subst-ρ-¬inst (subst-inst-> (s≤s z≤n))))))))) (subst-jmp (subst-word (subst-⟦⟧ (subst-⟦⟧ (subst-⟦⟧ (subst-⟦⟧ (subst-⟦⟧ subst-globval (subst-inst (subst-α subst-int))) (subst-inst (subst-α subst-int))) (subst-inst (subst-α subst-int))) (subst-inst (subst-α (subst-α-inst subst-int)))) (subst-inst (subst-ρ (subst-ρ-¬inst (subst-inst-> (s≤s z≤n))))))))) (subst-jmp (subst-word (subst-⟦⟧ (subst-⟦⟧ (subst-⟦⟧ (subst-⟦⟧ (subst-⟦⟧ subst-globval (subst-inst (subst-α subst-int))) (subst-inst (subst-α subst-int))) (subst-inst (subst-α subst-int))) (subst-inst (subst-α subst-int))) (subst-inst (subst-ρ (subst-ρ-inst subst-[])))))))
