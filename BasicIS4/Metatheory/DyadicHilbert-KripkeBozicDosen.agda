module BasicIS4.Metatheory.DyadicHilbert-KripkeBozicDosen where

open import BasicIS4.Syntax.DyadicHilbert public
open import BasicIS4.Semantics.KripkeBozicDosen public


eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊩ A
eval (var i)          γ δ = lookup i γ
eval (app t u)        γ δ = (eval t γ δ refl≤) (eval u γ δ)
eval ci               γ δ = λ _ a → a
eval (ck {A})         γ δ = λ _ a ξ b → mono⊩ {A} ξ a
eval (cs {A} {B} {C}) γ δ = λ _ f ξ g ξ′ a →
                            let h = ((mono⊩ {A ▻ B ▻ C} (trans≤ ξ ξ′) f) refl≤ a) refl≤
                                b = (mono⊩ {A ▻ B} ξ′ g) refl≤ a
                            in  h b
eval (mvar i)         γ δ = lookup i (δ reflR)
eval (box t)          γ δ = λ ζ → eval t ∙ (λ ζ′ → δ (transR ζ ζ′))
eval cdist            γ δ = λ _ □f ξ □a ζ →
                            let _ , (ξ′ , ζ′) = ≤⨾R→R⨾≤ (_ , (ξ , ζ))
                                f = □f ξ′ ζ′
                                a = □a ζ
                            in  f a
eval cup              γ δ = λ _ □a ζ ζ′ → □a (transR ζ ζ′)
eval cdown            γ δ = λ _ □a → □a reflR
eval (cpair {A})      γ δ = λ _ a ξ b → mono⊩ {A} ξ a , b
eval cfst             γ δ = λ _ s → π₁ s
eval csnd             γ δ = λ _ s → π₂ s
eval tt               γ δ = ∙