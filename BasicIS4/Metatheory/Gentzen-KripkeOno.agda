module BasicIS4.Metatheory.Gentzen-BasicKripkeBozicDosen where

open import BasicIS4.Syntax.Gentzen public
open import BasicIS4.Semantics.BasicKripkeBozicDosen public


-- Soundness with respect to all models, or evaluation.

mutual
  eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
  eval (var i)           γ = lookup i γ
  eval (lam t)           γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
  eval (app {A} {B} t u) γ = _⟪$⟫_ {A} {B} (eval t γ) (eval u γ)
  eval (multibox ts u)   γ = λ ζ → eval u (thing ts γ ζ)
  eval (down {A} t)      γ = ⟪⇓⟫ {A} (eval t γ)
  eval (pair t u)        γ = eval t γ , eval u γ
  eval (fst t)           γ = π₁ (eval t γ)
  eval (snd t)           γ = π₂ (eval t γ)
  eval tt                γ = ∙

  -- TODO: What is this?
  thing : ∀ {{_ : Model}} {Δ Γ} {w : World}
          → Γ ⊢⋆ □⋆ Δ → w ⊩⋆ Γ → ∀ {v′} → w R v′ → v′ ⊩⋆ □⋆ Δ
  thing {⌀}     ∙        γ ζ = ∙
  thing {Δ , B} (ts , t) γ ζ = thing ts γ ζ , λ ζ′ → eval t γ (transR ζ ζ′)

eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ⊨⋆ Π
eval⋆ {⌀}     ∙        γ = ∙
eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ


-- TODO: Correctness of evaluation with respect to conversion.
