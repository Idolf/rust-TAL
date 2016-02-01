module SimpleSoundness where


steps-soundness : ∀ {n P₁ P₂} →
                    ⊢ P₁ program →
                    ⊢ P₁ ⇒ₙ n / P₂ →
                    ∃ λ P₃ →
                      ⊢ P₃ program ×
                      ⊢ P₂ ⇒ P₃
