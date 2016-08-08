module BasicIS4.Gentzen.TreeWithContext.KripkeSoundness where

open import BasicIS4.Gentzen.TreeWithContext public


-- Soundness, or evaluation, with only modal accessibility.

module WithRegularForcing where
  open import BasicIS4.KripkeSemantics public
  open RegularForcing public

  mutual
    eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
    eval (var i)         γ = lookup i γ
    eval (lam t)         γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
    eval (app t u)       γ = (eval t γ) refl≤ (eval u γ)
    eval (multibox ts u) γ = λ ζ → eval u (eval⋆ ts γ ζ)
    eval (down t)        γ = (eval t γ) reflR
    eval (pair t u)      γ = eval t γ , eval u γ
    eval (fst t)         γ = π₁ (eval t γ)
    eval (snd t)         γ = π₂ (eval t γ)
    eval tt              γ = ∙

    eval⋆ : ∀ {{_ : Model}} {Δ Γ} {w : World}
            → Γ ⊢⋆ □⋆ Δ → w ⊩⋆ Γ → ∀ {v′} → w R v′ → v′ ⊩⋆ □⋆ Δ
    eval⋆ {⌀}     ∙        γ ζ = ∙
    eval⋆ {Δ , B} (ts , t) γ ζ = eval⋆ ts γ ζ , λ ζ′ → eval t γ (transR ζ ζ′)


-- Soundness, or evaluation, with both intuitionistic and modal accessibility.

module WithBidirectionalForcing where
  open import BasicIS4.KripkeSemantics public
  open DualRelationForcing public

  mutual
    eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
    eval (var i)         γ = lookup i γ
    eval (lam t)         γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
    eval (app t u)       γ = (eval t γ) refl≤ (eval u γ)
    eval (multibox ts u) γ = λ ξ ζ → eval u (eval⋆ ts γ ξ ζ)
    eval (down t)        γ = (eval t γ) refl≤ reflR
    eval (pair t u)      γ = eval t γ , eval u γ
    eval (fst t)         γ = π₁ (eval t γ)
    eval (snd t)         γ = π₂ (eval t γ)
    eval tt              γ = ∙

    eval⋆ : ∀ {{_ : Model}} {Δ Γ} {w : World}
            → Γ ⊢⋆ □⋆ Δ → w ⊩⋆ Γ → ∀ {w′} → w ≤ w′ → ∀ {v′} → w′ R v′ → v′ ⊩⋆ □⋆ Δ
    eval⋆ {⌀}     ∙        γ ξ ζ = ∙
    eval⋆ {Δ , B} (ts , t) γ ξ ζ = eval⋆ ts γ ξ ζ , λ ξ′ ζ′ →
                                   let _ , (ξ″ , ζ″) = R⨾≤→≤⨾R (_ , (ζ , ξ′))
                                   in  eval t γ (trans≤ ξ ξ″) (transR ζ″ ζ′)


-- The remaining soundness proofs are subsumed by the above.

module Ono where
  open import BasicIS4.KripkeSemantics.Ono public
  open RegularForcing public

  mutual
    eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
    eval (var i)         γ = lookup i γ
    eval (lam t)         γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
    eval (app t u)       γ = (eval t γ) refl≤ (eval u γ)
    eval (multibox ts u) γ = λ ζ → eval u (eval⋆ ts γ ζ)
    eval (down t)        γ = (eval t γ) reflR
    eval (pair t u)      γ = eval t γ , eval u γ
    eval (fst t)         γ = π₁ (eval t γ)
    eval (snd t)         γ = π₂ (eval t γ)
    eval tt              γ = ∙

    eval⋆ : ∀ {{_ : Model}} {Δ Γ} {w : World}
            → Γ ⊢⋆ □⋆ Δ → w ⊩⋆ Γ → ∀ {v′} → w R v′ → v′ ⊩⋆ □⋆ Δ
    eval⋆ {⌀}     ∙        γ ζ = ∙
    eval⋆ {Δ , B} (ts , t) γ ζ = eval⋆ ts γ ζ , λ ζ′ → eval t γ (transR ζ ζ′)

module BozicDosen where
  open import BasicIS4.KripkeSemantics.BozicDosen public
  open RegularForcing public

  mutual
    eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
    eval (var i)         γ = lookup i γ
    eval (lam t)         γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
    eval (app t u)       γ = (eval t γ) refl≤ (eval u γ)
    eval (multibox ts u) γ = λ ζ → eval u (eval⋆ ts γ ζ)
    eval (down t)        γ = (eval t γ) reflR
    eval (pair t u)      γ = eval t γ , eval u γ
    eval (fst t)         γ = π₁ (eval t γ)
    eval (snd t)         γ = π₂ (eval t γ)
    eval tt              γ = ∙

    eval⋆ : ∀ {{_ : Model}} {Δ Γ} {w : World}
            → Γ ⊢⋆ □⋆ Δ → w ⊩⋆ Γ → ∀ {v′} → w R v′ → v′ ⊩⋆ □⋆ Δ
    eval⋆ {⌀}     ∙        γ ζ = ∙
    eval⋆ {Δ , B} (ts , t) γ ζ = eval⋆ ts γ ζ , λ ζ′ → eval t γ (transR ζ ζ′)

module EwaldEtAl where
  open import BasicIS4.KripkeSemantics.EwaldEtAl public
  open DualRelationForcing public

  mutual
    eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
    eval (var i)         γ = lookup i γ
    eval (lam t)         γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
    eval (app t u)       γ = (eval t γ) refl≤ (eval u γ)
    eval (multibox ts u) γ = λ ξ ζ → eval u (eval⋆ ts γ ξ ζ)
    eval (down t)        γ = (eval t γ) refl≤ reflR
    eval (pair t u)      γ = eval t γ , eval u γ
    eval (fst t)         γ = π₁ (eval t γ)
    eval (snd t)         γ = π₂ (eval t γ)
    eval tt              γ = ∙

    eval⋆ : ∀ {{_ : Model}} {Δ Γ} {w : World}
            → Γ ⊢⋆ □⋆ Δ → w ⊩⋆ Γ → ∀ {w′} → w ≤ w′ → ∀ {v′} → w′ R v′ → v′ ⊩⋆ □⋆ Δ
    eval⋆ {⌀}     ∙        γ ξ ζ = ∙
    eval⋆ {Δ , B} (ts , t) γ ξ ζ = eval⋆ ts γ ξ ζ , λ ξ′ ζ′ →
                                   let _ , (ξ″ , ζ″) = R⨾≤→≤⨾R (_ , (ζ , ξ′))
                                   in  eval t γ (trans≤ ξ ξ″) (transR ζ″ ζ′)

module AlechinaEtAl where
  open import BasicIS4.KripkeSemantics.AlechinaEtAl public
  open DualRelationForcing public

  mutual
    eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
    eval (var i)         γ = lookup i γ
    eval (lam t)         γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
    eval (app t u)       γ = (eval t γ) refl≤ (eval u γ)
    eval (multibox ts u) γ = λ ξ ζ → eval u (eval⋆ ts γ ξ ζ)
    eval (down t)        γ = (eval t γ) refl≤ reflR
    eval (pair t u)      γ = eval t γ , eval u γ
    eval (fst t)         γ = π₁ (eval t γ)
    eval (snd t)         γ = π₂ (eval t γ)
    eval tt              γ = ∙

    eval⋆ : ∀ {{_ : Model}} {Δ Γ} {w : World}
            → Γ ⊢⋆ □⋆ Δ → w ⊩⋆ Γ → ∀ {w′} → w ≤ w′ → ∀ {v′} → w′ R v′ → v′ ⊩⋆ □⋆ Δ
    eval⋆ {⌀}     ∙        γ ξ ζ = ∙
    eval⋆ {Δ , B} (ts , t) γ ξ ζ = eval⋆ ts γ ξ ζ , λ ξ′ ζ′ →
                                   let _ , (ξ″ , ζ″) = R⨾≤→≤⨾R (_ , (ζ , ξ′))
                                   in  eval t γ (trans≤ ξ ξ″) (transR ζ″ ζ′)