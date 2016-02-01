module Lemmas.Semantics where

open import Util
open import Judgments

module SimpleSemanticsLemmas where
  open import Lemmas.SimpleSemantics
  open SimpleGrammar
  open SimpleSemantics

  step-unique : ∀ {G P P₁ P₂} →
                  G ⊢ P ⇒ P₁ →
                  G ⊢ P ⇒ P₂ →
                  P₁ ≡ P₂
  step-unique = step-uniqueₛ

  step-prg-unique : ∀ {P P₁ P₂} →
                      ⊢ P ⇒ P₁ →
                      ⊢ P ⇒ P₂ →
                      P₁ ≡ P₂
  step-prg-unique = step-prg-uniqueₛ

  exec-unique : ∀ {P P₁ P₂ n} →
                  ⊢ P ⇒ₙ n / P₁ →
                  ⊢ P ⇒ₙ n / P₂ →
                  P₁ ≡ P₂
  exec-unique = exec-uniqueₛ

  step-dec : ∀ G P → Dec (∃ λ P' → G ⊢ P ⇒ P')
  step-dec = step-decₛ

  step-prg-dec : ∀ P → Dec (∃ λ P' → ⊢ P ⇒ P')
  step-prg-dec = step-prg-decₛ

  exec-dec : ∀ P n → Dec (∃ λ P' → ⊢ P ⇒ₙ n / P')
  exec-dec = exec-decₛ

module HighSemanticsLemmas where
  open import Lemmas.HighSemantics
  open HighGrammar
  open HighSemantics

  step-unique : ∀ {G P P₁ P₂} →
                  G ⊢ P ⇒ P₁ →
                  G ⊢ P ⇒ P₂ →
                  P₁ ≡ P₂
  step-unique = step-uniqueₕ

  step-prg-unique : ∀ {P P₁ P₂} →
                      ⊢ P ⇒ P₁ →
                      ⊢ P ⇒ P₂ →
                      P₁ ≡ P₂
  step-prg-unique = step-prg-uniqueₕ

  exec-unique : ∀ {P P₁ P₂ n} →
                  ⊢ P ⇒ₙ n / P₁ →
                  ⊢ P ⇒ₙ n / P₂ →
                  P₁ ≡ P₂
  exec-unique = exec-uniqueₕ

  step-dec : ∀ G P → Dec (∃ λ P' → G ⊢ P ⇒ P')
  step-dec = step-decₕ

  step-prg-dec : ∀ P → Dec (∃ λ P' → ⊢ P ⇒ P')
  step-prg-dec = step-prg-decₕ

  exec-dec : ∀ P n → Dec (∃ λ P' → ⊢ P ⇒ₙ n / P')
  exec-dec = exec-decₕ
