module Lemmas.Semantics where

open import Util
open import Judgments

module SimpleSemanticsLemmas where
  open import Lemmas.SimpleSemantics
  open SimpleGrammar
  open SimpleSemantics

  instantiate-unique : ∀ {G w I₁ I₂} →
                         InstantiateGlobal G w I₁ →
                         InstantiateGlobal G w I₂ →
                         I₁ ≡ I₂
  instantiate-unique = instantiate-uniqueₛ

  step-unique : ∀ {G P P₁ P₂} →
                  G ⊢ P ⇒ P₁ →
                  G ⊢ P ⇒ P₂ →
                  P₁ ≡ P₂
  step-unique = step-uniqueₛ

  step-prg-unique : ∀ {ℒ ℒ₁ ℒ₂} →
                      ⊢ ℒ ⇒ ℒ₁ →
                      ⊢ ℒ ⇒ ℒ₂ →
                      ℒ₁ ≡ ℒ₂
  step-prg-unique = step-prg-uniqueₛ

  exec-unique : ∀ {ℒ ℒ₁ ℒ₂ n} →
                  ⊢ ℒ ⇒ₙ n / ℒ₁ →
                  ⊢ ℒ ⇒ₙ n / ℒ₂ →
                  ℒ₁ ≡ ℒ₂
  exec-unique = exec-uniqueₛ

  instantiate-dec : ∀ G w → Dec (∃ λ I → InstantiateGlobal G w I)
  instantiate-dec = instantiate-decₛ

  step-dec : ∀ G P → Dec (∃ λ P' → G ⊢ P ⇒ P')
  step-dec = step-decₛ

  step-prg-dec : ∀ ℒ → Dec (∃ λ ℒ' → ⊢ ℒ ⇒ ℒ')
  step-prg-dec = step-prg-decₛ

  exec-dec : ∀ ℒ n → Dec (∃ λ ℒ' → ⊢ ℒ ⇒ₙ n / ℒ')
  exec-dec = exec-decₛ

module HighSemanticsLemmas where
  open import Lemmas.HighSemantics
  open HighGrammar
  open HighSemantics

  instantiate-unique : ∀ {G w I₁ I₂} →
                         InstantiateGlobal G w I₁ →
                         InstantiateGlobal G w I₂ →
                         I₁ ≡ I₂
  instantiate-unique = instantiate-uniqueₕ

  step-unique : ∀ {G P P₁ P₂} →
                  G ⊢ P ⇒ P₁ →
                  G ⊢ P ⇒ P₂ →
                  P₁ ≡ P₂
  step-unique = step-uniqueₕ

  step-prg-unique : ∀ {ℒ ℒ₁ ℒ₂} →
                      ⊢ ℒ ⇒ ℒ₁ →
                      ⊢ ℒ ⇒ ℒ₂ →
                      ℒ₁ ≡ ℒ₂
  step-prg-unique = step-prg-uniqueₕ

  exec-unique : ∀ {ℒ ℒ₁ ℒ₂ n} →
                  ⊢ ℒ ⇒ₙ n / ℒ₁ →
                  ⊢ ℒ ⇒ₙ n / ℒ₂ →
                  ℒ₁ ≡ ℒ₂
  exec-unique = exec-uniqueₕ

  instantiate-dec : ∀ G w → Dec (∃ λ I → InstantiateGlobal G w I)
  instantiate-dec = instantiate-decₕ

  step-dec : ∀ G P → Dec (∃ λ P' → G ⊢ P ⇒ P')
  step-dec = step-decₕ

  step-prg-dec : ∀ ℒ → Dec (∃ λ ℒ' → ⊢ ℒ ⇒ ℒ')
  step-prg-dec = step-prg-decₕ

  exec-dec : ∀ ℒ n → Dec (∃ λ ℒ' → ⊢ ℒ ⇒ₙ n / ℒ')
  exec-dec = exec-decₕ
