----------------------------------------------------------------------------------------------------

-- normalization-by-evaluation to β-short weak normal form

module A202401.STLC-Negative-WNF-NBE where

open import A202401.STLC-Negative-WNF public
open import A202401.Kit4 public


----------------------------------------------------------------------------------------------------

infix 3 _⊩_
_⊩_ : Ctx → Ty → Set
W ⊩ A ⌜⊃⌝ B = ∀ {W′} → W ⊑ W′ → W′ ⊩ A → W′ ⊩ B
W ⊩ A ⌜∧⌝ B = W ⊩ A × W ⊩ B
W ⊩ ⌜𝟙⌝     = 𝟙

vren : ∀ {A W W′} → W ⊑ W′ → W ⊩ A → W′ ⊩ A
vren {A ⌜⊃⌝ B} ϱ v         = λ ϱ′ → v (trans⊑ ϱ ϱ′)
vren {A ⌜∧⌝ B} ϱ (v₁ , v₂) = vren ϱ v₁ , vren ϱ v₂
vren {⌜𝟙⌝}     ϱ unit      = unit

open ValKit (kit _⊩_ vren) public

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ var i     ⟧ γ = ⟦ i ⟧∋ γ
⟦ ⌜λ⌝ t     ⟧ γ = λ ϱ v → ⟦ t ⟧ (vren§ ϱ γ , v)
⟦ t₁ ⌜$⌝ t₂ ⟧ γ = ⟦ t₁ ⟧ γ id⊑ $ ⟦ t₂ ⟧ γ
⟦ t₁ ⌜,⌝ t₂ ⟧ γ = ⟦ t₁ ⟧ γ , ⟦ t₂ ⟧ γ
⟦ ⌜fst⌝ t   ⟧ γ = fst (⟦ t ⟧ γ)
⟦ ⌜snd⌝ t   ⟧ γ = snd (⟦ t ⟧ γ)
⟦ ⌜unit⌝    ⟧ γ = unit


----------------------------------------------------------------------------------------------------

mutual
  ↑ : ∀ {A Γ} → Σ (Γ ⊢ A) NNF → Γ ⊩ A
  ↑ {A ⌜⊃⌝ B} (_ , p₁) = λ ϱ v₂ → let _ , p₂ = ↓ v₂
                                     in ↑ (_ , renNNF ϱ p₁ ⌜$⌝ p₂)
  ↑ {A ⌜∧⌝ B} (_ , p)  = ↑ (_ , ⌜fst⌝ p) , ↑ (_ , ⌜snd⌝ p)
  ↑ {⌜𝟙⌝}     (_ , p)  = unit

  ↓ : ∀ {A Γ} → Γ ⊩ A → Σ (Γ ⊢ A) NF
  ↓ {A ⌜⊃⌝ B} v         = let t , p = ↓ (v (wk⊑ id⊑) (↑ (var zero , var-)))
                            in ⌜λ⌝ t , ⌜λ⌝-
  ↓ {A ⌜∧⌝ B} (v₁ , v₂) = let t₁ , p₁ = ↓ v₁
                              t₂ , p₂ = ↓ v₂
                            in t₁ ⌜,⌝ t₂ , -⌜,⌝-
  ↓ {⌜𝟙⌝}     unit        = _ , ⌜unit⌝

vid§ : ∀ {Γ} → Γ ⊩§ Γ
vid§ {∙}     = ∙
vid§ {Γ , A} = vren§ (wk⊑ id⊑) vid§ , ↑ (var zero , var-)

⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) NF
⟦ v ⟧⁻¹ = ↓ (v vid§)

nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) NF
nbe t = ⟦ ⟦ t ⟧ ⟧⁻¹


----------------------------------------------------------------------------------------------------
