----------------------------------------------------------------------------------------------------

-- normalization-by-evaluation to β-short weak normal form, with explicit model

module A202401.STLC-Negative-WNF-NBE2 where

open import A202401.STLC-Negative-WNF public
open import A202401.Kit4 public


----------------------------------------------------------------------------------------------------

record Model : Set₁ where
  field
    World  : Set
    _≤_    : World → World → Set
    refl≤  : ∀ {W} → W ≤ W
    trans≤ : ∀ {W W′ W″} → W ≤ W′ → W′ ≤ W″ → W ≤ W″

open Model public

module _ {ℳ : Model} where
  private
    module ℳ = Model ℳ

  infix 3 _⊩_
  _⊩_ : ℳ.World → Ty → Set
  W ⊩ A ⌜⊃⌝ B = ∀ {W′} → W ℳ.≤ W′ → W′ ⊩ A → W′ ⊩ B
  W ⊩ A ⌜∧⌝ B = W ⊩ A × W ⊩ B
  W ⊩ ⌜𝟙⌝     = 𝟙

  vren : ∀ {A W W′} → W ℳ.≤ W′ → W ⊩ A → W′ ⊩ A
  vren {A ⌜⊃⌝ B} ϱ v         = λ ϱ′ → v (ℳ.trans≤ ϱ ϱ′)
  vren {A ⌜∧⌝ B} ϱ (v₁ , v₂) = vren ϱ v₁ , vren ϱ v₂
  vren {⌜𝟙⌝}     ϱ unit      = unit

open ModelKit (kit (λ {ℳ} → _⊩_ {ℳ}) (λ {ℳ} {A} → vren {ℳ} {A})) public

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ var i     ⟧     γ = ⟦ i ⟧∋ γ
⟦ ⌜λ⌝ t     ⟧     γ = λ ϱ v → ⟦ t ⟧ (vren§ ϱ γ , v)
⟦ t₁ ⌜$⌝ t₂ ⟧ {ℳ} γ = ⟦ t₁ ⟧ γ (refl≤ ℳ) $ ⟦ t₂ ⟧ γ
⟦ t₁ ⌜,⌝ t₂ ⟧     γ = ⟦ t₁ ⟧ γ , ⟦ t₂ ⟧ γ
⟦ ⌜fst⌝ t   ⟧     γ = fst (⟦ t ⟧ γ)
⟦ ⌜snd⌝ t   ⟧     γ = snd (⟦ t ⟧ γ)
⟦ ⌜unit⌝    ⟧     γ = unit


----------------------------------------------------------------------------------------------------

𝒞 : Model
𝒞 = record
      { World  = Ctx
      ; _≤_    = _⊑_
      ; refl≤  = refl⊑
      ; trans≤ = trans⊑
      }

mutual
  ↑ : ∀ {A Γ} → Σ (Γ ⊢ A) NNF → 𝒞 / Γ ⊩ A
  ↑ {A ⌜⊃⌝ B} (_ , p₁) = λ ϱ v₂ → let _ , p₂ = ↓ v₂
                                     in ↑ (_ , renNNF ϱ p₁ ⌜$⌝ p₂)
  ↑ {A ⌜∧⌝ B} (_ , p)  = ↑ (_ , ⌜fst⌝ p) , ↑ (_ , ⌜snd⌝ p)
  ↑ {⌜𝟙⌝}     (_ , p)  = unit

  ↓ : ∀ {A Γ} → 𝒞 / Γ ⊩ A → Σ (Γ ⊢ A) NF
  ↓ {A ⌜⊃⌝ B} v         = let t , p = ↓ (v (wk⊑ id⊑) (↑ (var zero , var-)))
                            in ⌜λ⌝ t , ⌜λ⌝-
  ↓ {A ⌜∧⌝ B} (v₁ , v₂) = let t₁ , p₁ = ↓ v₁
                              t₂ , p₂ = ↓ v₂
                            in t₁ ⌜,⌝ t₂ , -⌜,⌝-
  ↓ {⌜𝟙⌝}     unit      = _ , ⌜unit⌝

vid§ : ∀ {Γ} → 𝒞 / Γ ⊩§ Γ
vid§ {∙}     = ∙
vid§ {Γ , A} = vren§ (wk⊑ id⊑) vid§ , ↑ (var zero , var-)

⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) NF
⟦ v ⟧⁻¹ = ↓ (v vid§)

nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) NF
nbe t = ⟦ ⟦ t ⟧ ⟧⁻¹


----------------------------------------------------------------------------------------------------
