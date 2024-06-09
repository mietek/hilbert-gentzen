----------------------------------------------------------------------------------------------------

-- normalization-by-evaluation to β-short weak normal form, with explicit model

module A202401.STLC-Base-WNF-NBE2 where

open import A202401.STLC-Base-WNF public
open import A202401.Kit4 public


----------------------------------------------------------------------------------------------------

record Model : Set₁ where
  field
    World  : Set
    _≤_    : World → World → Set
    refl≤  : ∀ {W} → W ≤ W
    trans≤ : ∀ {W W′ W″} → W ≤ W′ → W′ ≤ W″ → W ≤ W″
    ⟦◦⟧    : World → Set
    ren⟦◦⟧ : ∀ {W W′} → W ≤ W′ → ⟦◦⟧ W → ⟦◦⟧ W′

open Model public

module _ {ℳ : Model} where
  private
    module ℳ = Model ℳ

  infix 3 _⊩_
  _⊩_ : ℳ.World → Ty → Set
  W ⊩ ⌜◦⌝     = ℳ.⟦◦⟧ W
  W ⊩ A ⌜⊃⌝ B = ∀ {W′} → W ℳ.≤ W′ → W′ ⊩ A → W′ ⊩ B

  vren : ∀ {A W W′} → W ℳ.≤ W′ → W ⊩ A → W′ ⊩ A
  vren {⌜◦⌝}     ϱ v = ℳ.ren⟦◦⟧ ϱ v
  vren {A ⌜⊃⌝ B} ϱ v = λ ϱ′ → v (ℳ.trans≤ ϱ ϱ′)

open ModelKit (kit (λ {ℳ} → _⊩_ {ℳ}) (λ {ℳ} {A} → vren {ℳ} {A})) public

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ var i     ⟧     γ = ⟦ i ⟧∋ γ
⟦ ⌜λ⌝ t     ⟧     γ = λ ϱ v → ⟦ t ⟧ (vren§ ϱ γ , v)
⟦ t₁ ⌜$⌝ t₂ ⟧ {ℳ} γ = ⟦ t₁ ⟧ γ (refl≤ ℳ) $ ⟦ t₂ ⟧ γ


----------------------------------------------------------------------------------------------------

𝒞 : Model
𝒞 = record
      { World  = Ctx
      ; _≤_    = _⊑_
      ; refl≤  = refl⊑
      ; trans≤ = trans⊑
      ; ⟦◦⟧    = λ Γ → Σ (Γ ⊢ ⌜◦⌝) NNF
      ; ren⟦◦⟧ = λ { ϱ (_ , p) → _ , renNNF ϱ p }
      }

mutual
  ↑ : ∀ {A Γ} → Σ (Γ ⊢ A) NNF → 𝒞 / Γ ⊩ A
  ↑ {⌜◦⌝}     (_ , p)  = _ , p
  ↑ {A ⌜⊃⌝ B} (_ , p₁) = λ ϱ v₂ → let _ , p₂ = ↓ v₂
                                     in ↑ (_ , renNNF ϱ p₁ ⌜$⌝ p₂)

  ↓ : ∀ {A Γ} → 𝒞 / Γ ⊩ A → Σ (Γ ⊢ A) NF
  ↓ {⌜◦⌝}     (_ , p) = _ , nnf p
  ↓ {A ⌜⊃⌝ B} v       = let t , p = ↓ (v (wk⊑ id⊑) (↑ {A} (var zero , var-)))
                          in ⌜λ⌝ t , ⌜λ⌝-

vid§ : ∀ {Γ} → 𝒞 / Γ ⊩§ Γ
vid§ {∙}     = ∙
vid§ {Γ , A} = vren§ (wk⊑ id⊑) vid§ , ↑ {A} (var zero , var-)

⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) NF
⟦ v ⟧⁻¹ = ↓ (v vid§)

nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) NF
nbe t = ⟦ ⟦ t ⟧ ⟧⁻¹


----------------------------------------------------------------------------------------------------
