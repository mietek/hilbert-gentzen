module BasicIS4.Regular.Hilbert.Nested.KripkeSoundness where

open import BasicIS4.Regular.Hilbert.Nested public


module Ono where
  open import BasicIS4.KripkeSemantics.Ono public
  open StandardForcing public

  --   w′  R   v′
  --   ●───────●
  --   │     ⋰
  -- ≤ │   R
  --   │ ⋰
  --   ●
  --   w
  --
  -- zigR : ∀ {v′ w w′} → w′ R v′ → w ≤ w′ → w R v′

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
  eval (var i)          γ = lookup i γ
  eval (app t u)        γ = (eval t γ) refl≤ (eval u γ)
  eval ci               γ = λ _ a → a
  eval (ck {A})         γ = λ _ a ξ b → mono⊩ {A} ξ a
  eval (cs {A} {B} {C}) γ = λ _ f ξ g ξ′ a →
                            let h = ((mono⊩ {A ▷ B ▷ C} (trans≤ ξ ξ′) f) refl≤ a) refl≤
                                b = (mono⊩ {A ▷ B} ξ′ g) refl≤ a
                            in  h b
  eval (box t)          γ = λ ζ → eval t ∙
  eval cdist            γ = λ _ □f ξ □a ζ →
                            let ζ′ = zigR ζ ξ
                                f  = □f ζ′ refl≤
                                a  = □a ζ
                            in  f a
  eval cup              γ = λ _ □a ζ ζ′ → □a (transR ζ ζ′)
  eval cdown            γ = λ _ □a → □a reflR
  eval (cpair {A})      γ = λ _ a ξ b → mono⊩ {A} ξ a , b
  eval cfst             γ = λ _ s → π₁ s
  eval csnd             γ = λ _ s → π₂ s
  eval tt               γ = ∙


module BozicDosen where
  open import BasicIS4.KripkeSemantics.BozicDosen public
  open StandardForcing public

  --   w′  R   v′
  --   ●───────●
  --   │       ┊
  -- ≤ │       ┊ ≤
  --   │       ┊
  --   ●╌╌╌╌╌╌╌◌
  --   w   R   v
  --
  -- zigzagR⨾≤ : ∀ {v′ w w′} → w′ R v′ → w ≤ w′ → ∃ (λ v → w R v × v ≤ v′)

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
  eval (var i)          γ = lookup i γ
  eval (app t u)        γ = (eval t γ) refl≤ (eval u γ)
  eval ci               γ = λ _ a → a
  eval (ck {A})         γ = λ _ a ξ b → mono⊩ {A} ξ a
  eval (cs {A} {B} {C}) γ = λ _ f ξ g ξ′ a →
                            let h = ((mono⊩ {A ▷ B ▷ C} (trans≤ ξ ξ′) f) refl≤ a) refl≤
                                b = (mono⊩ {A ▷ B} ξ′ g) refl≤ a
                            in  h b
  eval (box t)          γ = λ ζ → eval t ∙
  eval cdist            γ = λ _ □f ξ □a ζ →
                            let _ , (ξ′ , ζ′) = zigzagR⨾≤ ζ ξ
                                f = □f ξ′ ζ′
                                a = □a ζ
                            in  f a
  eval cup              γ = λ _ □a ζ ζ′ → □a (transR ζ ζ′)
  eval cdown            γ = λ _ □a → □a reflR
  eval (cpair {A})      γ = λ _ a ξ b → mono⊩ {A} ξ a , b
  eval cfst             γ = λ _ s → π₁ s
  eval csnd             γ = λ _ s → π₂ s
  eval tt               γ = ∙


module Wijesekera where
  open import BasicIS4.KripkeSemantics.Wijesekera public
  open StandardForcing public

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
  eval (var i)          γ = lookup i γ
  eval (app t u)        γ = (eval t γ) refl≤ (eval u γ)
  eval ci               γ = λ _ a → a
  eval (ck {A})         γ = λ _ a ξ b → mono⊩ {A} ξ a
  eval (cs {A} {B} {C}) γ = λ _ f ξ g ξ′ a →
                            let h = ((mono⊩ {A ▷ B ▷ C} (trans≤ ξ ξ′) f) refl≤ a) refl≤
                                b = (mono⊩ {A ▷ B} ξ′ g) refl≤ a
                            in  h b
  eval (box t)          γ = λ ξ ζ → eval t ∙
  eval cdist            γ = λ _ □f ξ □a ξ′ ζ →
                            let f = □f (trans≤ ξ ξ′) ζ refl≤
                                a = □a ξ′ ζ
                            in  f a
  eval cup              γ = λ _ □a ξ ζ ξ′ ζ′ →
                            let _ , (ξ″ , ζ″) = trans≤⨾R (_ , (ξ , ζ)) (_ , (ξ′ , ζ′))
                            in  □a ξ″ ζ″
  eval cdown            γ = λ _ □a → □a refl≤ reflR
  eval (cpair {A})      γ = λ _ a ξ b → mono⊩ {A} ξ a , b
  eval cfst             γ = λ _ s → π₁ s
  eval csnd             γ = λ _ s → π₂ s
  eval tt               γ = ∙


module EwaldEtAl where
  open import BasicIS4.KripkeSemantics.EwaldEtAl public
  open StandardForcing public

  --   zap:            zagzig:
  --
  --   w′  R  v′       w′  R  v′
  --   ●╌╌╌╌╌╌╌◌       ◌╌╌╌╌╌╌╌●
  --   │       ┊       ┊       │
  -- ≤ │       ┊ ≤   ≤ ┊       │ ≤
  --   │       ┊       ┊       │
  --   ●───────●       ●───────●
  --   w   R   v       w   R   v
  --
  -- zap       : ∀ {v w w′} → w R v → w ≤ w′ → ∃ (λ v′ → w′ R v′ × v ≤ v′)
  -- zagzig≤⨾R : ∀ {w v v′} → v ≤ v′ → w R v → ∃ (λ w′ → w ≤ w′ × w′ R v′)

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
  eval (var i)          γ = lookup i γ
  eval (app t u)        γ = (eval t γ) refl≤ (eval u γ)
  eval ci               γ = λ _ a → a
  eval (ck {A})         γ = λ _ a ξ b → mono⊩ {A} ξ a
  eval (cs {A} {B} {C}) γ = λ _ f ξ g ξ′ a →
                            let h = ((mono⊩ {A ▷ B ▷ C} (trans≤ ξ ξ′) f) refl≤ a) refl≤
                                b = (mono⊩ {A ▷ B} ξ′ g) refl≤ a
                            in  h b
  eval (box t)          γ = λ ξ ζ → eval t ∙
  eval cdist            γ = λ _ □f ξ □a ξ′ ζ →
                            let f = □f (trans≤ ξ ξ′) ζ refl≤
                                a = □a ξ′ ζ
                            in  f a
  eval cup              γ = λ _ □a ξ ζ ξ′ ζ′ →
                            let _ , (ξ″ , ζ″) = trans≤⨾R (_ , (ξ , ζ)) (_ , (ξ′ , ζ′))
                            in  □a ξ″ ζ″
  eval cdown            γ = λ _ □a → □a refl≤ reflR
  eval (cpair {A})      γ = λ _ a ξ b → mono⊩ {A} ξ a , b
  eval cfst             γ = λ _ s → π₁ s
  eval csnd             γ = λ _ s → π₂ s
  eval tt               γ = ∙


module AlechinaEtAl where
  open import BasicIS4.KripkeSemantics.AlechinaEtAl public
  open StandardForcing public

  --   w′  R   v′
  --   ◌╌╌╌╌╌╌╌●
  --   ┊       │
  -- ≤ ┊       │ ≤
  --   ┊       │
  --   ●───────●
  --   w   R   v
  --
  -- zagzig≤⨾R : ∀ {w v v′} → v ≤ v′ → w R v → ∃ (λ w′ → w ≤ w′ × w′ R v′)

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
  eval (var i)          γ = lookup i γ
  eval (app t u)        γ = (eval t γ) refl≤ (eval u γ)
  eval ci               γ = λ _ a → a
  eval (ck {A})         γ = λ _ a ξ b → mono⊩ {A} ξ a
  eval (cs {A} {B} {C}) γ = λ _ f ξ g ξ′ a →
                            let h = ((mono⊩ {A ▷ B ▷ C} (trans≤ ξ ξ′) f) refl≤ a) refl≤
                                b = (mono⊩ {A ▷ B} ξ′ g) refl≤ a
                            in  h b
  eval (box t)          γ = λ ξ ζ → eval t ∙
  eval cdist            γ = λ _ □f ξ □a ξ′ ζ →
                            let f = □f (trans≤ ξ ξ′) ζ refl≤
                                a = □a ξ′ ζ
                            in  f a
  eval cup              γ = λ _ □a ξ ζ ξ′ ζ′ →
                            let _ , (ξ″ , ζ″) = trans≤⨾R (_ , (ξ , ζ)) (_ , (ξ′ , ζ′))
                            in  □a ξ″ ζ″
  eval cdown            γ = λ _ □a → □a refl≤ reflR
  eval (cpair {A})      γ = λ _ a ξ b → mono⊩ {A} ξ a , b
  eval cfst             γ = λ _ s → π₁ s
  eval csnd             γ = λ _ s → π₂ s
  eval tt               γ = ∙