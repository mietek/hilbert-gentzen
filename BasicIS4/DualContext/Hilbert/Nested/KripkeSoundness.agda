module BasicIS4.DualContext.Hilbert.Nested.KripkeSoundness where

open import BasicIS4.DualContext.Hilbert.Nested public


module Ono where
  open import BasicIS4.KripkeSemantics.Ono public

  --   w′  R  v′
  --   ●──────●
  --   │     ⋰
  -- ≤ │   R
  --   │ ⋰
  --   ●
  --   w
  --
  -- zigR : ∀ {v′ w w′} → w′ R v′ → w ≤ w′ → w R v′

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊩ A
  eval (var i)          γ δ = lookup i γ
  eval (app t u)        γ δ = (eval t γ δ) refl≤ (eval u γ δ)
  eval ci               γ δ = λ _ a → a
  eval (ck {A})         γ δ = λ _ a ξ b → mono⊩ {A} ξ a
  eval (cs {A} {B} {C}) γ δ = λ _ f ξ g ξ′ a →
    let h = ((mono⊩ {A ▷ B ▷ C} (trans≤ ξ ξ′) f) refl≤ a) refl≤
        b = (mono⊩ {A ▷ B} ξ′ g) refl≤ a
    in  h b
  eval (mvar i)         γ δ = lookup i (δ reflR)
  eval (box t)          γ δ = λ ζ → eval t ∙ (λ ζ′ → δ (transR ζ ζ′))
  eval cdist            γ δ = λ _ □f ξ □a ζ →
    let ζ′  = zigR ζ ξ
        □f′ = □f ζ′ refl≤
        □a′ = □a ζ
    in  □f′ □a′
  eval cup              γ δ = λ _ □a ζ ζ′ → □a (transR ζ ζ′)
  eval cdown            γ δ = λ _ □a → □a reflR
  eval (cpair {A})      γ δ = λ _ a ξ b → mono⊩ {A} ξ a , b
  eval cfst             γ δ = λ _ s → π₁ s
  eval csnd             γ δ = λ _ s → π₂ s
  eval tt               γ δ = ∙


module BozicDosen where
  open import BasicIS4.KripkeSemantics.BozicDosen public

  --   w′  R  v′
  --   ●──────●
  --   │      ┊
  -- ≤ │      ┊ ≤
  --   │      ┊
  --   ●╌╌╌╌╌╌◌
  --   w   R  v
  --
  -- zigzagR⨾≤ : ∀ {v′ w w′} → w′ R v′ → w ≤ w′ → ∃ (λ v → w R v × v ≤ v′)

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊩ A
  eval (var i)          γ δ = lookup i γ
  eval (app t u)        γ δ = (eval t γ δ) refl≤ (eval u γ δ)
  eval ci               γ δ = λ _ a → a
  eval (ck {A})         γ δ = λ _ a ξ b → mono⊩ {A} ξ a
  eval (cs {A} {B} {C}) γ δ = λ _ f ξ g ξ′ a →
    let h = ((mono⊩ {A ▷ B ▷ C} (trans≤ ξ ξ′) f) refl≤ a) refl≤
        b = (mono⊩ {A ▷ B} ξ′ g) refl≤ a
    in  h b
  eval (mvar i)         γ δ = lookup i (δ reflR)
  eval (box t)          γ δ = λ ζ → eval t ∙ (λ ζ′ → δ (transR ζ ζ′))
  eval cdist            γ δ = λ _ □f ξ □a ζ →
    let _ , (ξ′ , ζ′) = zigzagR⨾≤ ζ ξ
        □f′           = □f ξ′ ζ′
        □a′           = □a ζ
    in  □f′ □a′
  eval cup              γ δ = λ _ □a ζ ζ′ → □a (transR ζ ζ′)
  eval cdown            γ δ = λ _ □a → □a reflR
  eval (cpair {A})      γ δ = λ _ a ξ b → mono⊩ {A} ξ a , b
  eval cfst             γ δ = λ _ s → π₁ s
  eval csnd             γ δ = λ _ s → π₂ s
  eval tt               γ δ = ∙


module Wijesekera where
  open import BasicIS4.KripkeSemantics.Wijesekera public

  module _ {{_ : Model}} where
    -- FIXME: Read the Wijesekera paper; find the missing piece.
    postulate
      zigzag≤⨾R : ∀ {w v v′} → v ≤ v′ → w R v → ∃ (λ w′ → w ≤ w′ × w′ R v′)

    _≤⨾R_ : World → World → Set
    _≤⨾R_ = _≤_ ⨾ _R_

    refl≤⨾R : ∀ {w} → w ≤⨾R w
    refl≤⨾R {w} = w , (refl≤ , reflR)

    trans≤⨾R : ∀ {w w′ w″} → w ≤⨾R w′ → w′ ≤⨾R w″ → w ≤⨾R w″
    trans≤⨾R (a , (ξ , ζ)) (b , (ξ′ , ζ′)) = let c , (ξ″ , ζ″) = zigzag≤⨾R ξ′ ζ
                                             in  c , (trans≤ ξ ξ″ , transR ζ″ ζ′)

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊩ A
  eval (var i)          γ δ = lookup i γ
  eval (app t u)        γ δ = (eval t γ δ) refl≤ (eval u γ δ)
  eval ci               γ δ = λ _ a → a
  eval (ck {A})         γ δ = λ _ a ξ b → mono⊩ {A} ξ a
  eval (cs {A} {B} {C}) γ δ = λ _ f ξ g ξ′ a →
    let h = ((mono⊩ {A ▷ B ▷ C} (trans≤ ξ ξ′) f) refl≤ a) refl≤
        b = (mono⊩ {A ▷ B} ξ′ g) refl≤ a
    in  h b
  eval (mvar i)         γ δ = lookup i (δ refl≤ reflR)
  eval (box t)          γ δ = λ ξ ζ → eval t ∙ (λ ξ′ ζ′ →
    let _ , (ξ″ , ζ″) = zigzag≤⨾R ξ′ ζ
    in  δ (trans≤ ξ ξ″) (transR ζ″ ζ′))
  eval cdist            γ δ = λ _ □f ξ □a ξ′ ζ →
    let □f′ = □f (trans≤ ξ ξ′) ζ refl≤
        □a′ = □a ξ′ ζ
    in  □f′ □a′
  eval cup              γ δ = λ _ □a ξ ζ ξ′ ζ′ →
    let _ , (ξ″ , ζ″) = trans≤⨾R (_ , (ξ , ζ)) (_ , (ξ′ , ζ′))
    in  □a ξ″ ζ″
  eval cdown            γ δ = λ _ □a → □a refl≤ reflR
  eval (cpair {A})      γ δ = λ _ a ξ b → mono⊩ {A} ξ a , b
  eval cfst             γ δ = λ _ s → π₁ s
  eval csnd             γ δ = λ _ s → π₂ s
  eval tt               γ δ = ∙


module EwaldEtAl where
  open import BasicIS4.KripkeSemantics.EwaldEtAl public

  -- zap            zagzig
  --   w′  R  v′      w′  R  v′
  --   ●╌╌╌╌╌╌◌       ◌╌╌╌╌╌╌●
  --   │      ┊       ┊      │
  -- ≤ │      ┊ ≤   ≤ ┊      │ ≤
  --   │      ┊       ┊      │
  --   ●──────●       ●──────●
  --   w   R  v       w   R  v
  --
  -- zap       : ∀ {v w w′} → w R v → w ≤ w′ → ∃ (λ v′ → w′ R v′ × v ≤ v′)
  -- zagzig≤⨾R : ∀ {w v v′} → v ≤ v′ → w R v → ∃ (λ w′ → w ≤ w′ × w′ R v′)

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊩ A
  eval (var i)          γ δ = lookup i γ
  eval (app t u)        γ δ = (eval t γ δ) refl≤ (eval u γ δ)
  eval ci               γ δ = λ _ a → a
  eval (ck {A})         γ δ = λ _ a ξ b → mono⊩ {A} ξ a
  eval (cs {A} {B} {C}) γ δ = λ _ f ξ g ξ′ a →
    let h = ((mono⊩ {A ▷ B ▷ C} (trans≤ ξ ξ′) f) refl≤ a) refl≤
        b = (mono⊩ {A ▷ B} ξ′ g) refl≤ a
    in  h b
  eval (mvar i)         γ δ = lookup i (δ refl≤ reflR)
  eval (box {A} t)      γ δ = λ ξ ζ → eval t ∙ (λ ξ′ ζ′ →
    let _ , (ξ″ , ζ″) = zagzig≤⨾R ξ′ ζ
    in  δ (trans≤ ξ ξ″) (transR ζ″ ζ′))
  eval cdist            γ δ = λ _ □f ξ □a ξ′ ζ →
    let □f′ = □f (trans≤ ξ ξ′) ζ refl≤
        □a′ = □a ξ′ ζ
    in  □f′ □a′
  eval cup              γ δ = λ _ □a ξ ζ ξ′ ζ′ →
    let _ , (ξ″ , ζ″) = trans≤⨾R (_ , (ξ , ζ)) (_ , (ξ′ , ζ′))
    in  □a ξ″ ζ″
  eval cdown            γ δ = λ _ □a → □a refl≤ reflR
  eval (cpair {A})      γ δ = λ _ a ξ b → mono⊩ {A} ξ a , b
  eval cfst             γ δ = λ _ s → π₁ s
  eval csnd             γ δ = λ _ s → π₂ s
  eval tt               γ δ = ∙


module AlechinaEtAl where
  open import BasicIS4.KripkeSemantics.AlechinaEtAl public

  --   w′  R  v′
  --   ◌╌╌╌╌╌╌●
  --   ┊      │
  -- ≤ ┊   ₂  │ ≤
  --   ┊      │
  --   ●──────●
  --   w   R  v
  --
  -- zagzig≤⨾R : ∀ {w v v′} → v ≤ v′ → w R v → ∃ (λ w′ → w ≤ w′ × w′ R v′)

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊩ A
  eval (var i)          γ δ = lookup i γ
  eval (app t u)        γ δ = (eval t γ δ) refl≤ (eval u γ δ)
  eval ci               γ δ = λ _ a → a
  eval (ck {A})         γ δ = λ _ a ξ b → mono⊩ {A} ξ a
  eval (cs {A} {B} {C}) γ δ = λ _ f ξ g ξ′ a →
    let h = ((mono⊩ {A ▷ B ▷ C} (trans≤ ξ ξ′) f) refl≤ a) refl≤
        b = (mono⊩ {A ▷ B} ξ′ g) refl≤ a
    in  h b
  eval (mvar i)         γ δ = lookup i (δ refl≤ reflR)
  eval (box t)          γ δ = λ ξ ζ → eval t ∙ (λ ξ′ ζ′ →
    let _ , (ξ″ , ζ″) = zagzig≤⨾R ξ′ ζ
    in  δ (trans≤ ξ ξ″) (transR ζ″ ζ′))
  eval cdist            γ δ = λ _ □f ξ □a ξ′ ζ →
    let □f′ = □f (trans≤ ξ ξ′) ζ refl≤
        □a′ = □a ξ′ ζ
    in  □f′ □a′
  eval cup              γ δ = λ _ □a ξ ζ ξ′ ζ′ →
    let _ , (ξ″ , ζ″) = trans≤⨾R (_ , (ξ , ζ)) (_ , (ξ′ , ζ′))
    in  □a ξ″ ζ″
  eval cdown            γ δ = λ _ □a → □a refl≤ reflR
  eval (cpair {A})      γ δ = λ _ a ξ b → mono⊩ {A} ξ a , b
  eval cfst             γ δ = λ _ s → π₁ s
  eval csnd             γ δ = λ _ s → π₂ s
  eval tt               γ δ = ∙
