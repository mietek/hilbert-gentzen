----------------------------------------------------------------------------------------------------

-- normalization by evaluation to β-short weak normal form
-- with an explicit model construction

module STLC-Base-WNF-NbE2 where

open import STLC-Base-WNF public
open import Kit4 public


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
  vren {⌜◦⌝}     e v = ℳ.ren⟦◦⟧ e v
  vren {A ⌜⊃⌝ B} e v = λ e′ → v (ℳ.trans≤ e e′)

open ModelKit (kit (λ {ℳ} → _⊩_ {ℳ}) (λ {ℳ} {A} → vren {ℳ} {A})) public

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ var i     ⟧     vs = ⟦ i ⟧∋ vs
⟦ ⌜λ⌝ t     ⟧     vs = λ e v → ⟦ t ⟧ (v ∷ vrens e vs)
⟦ t₁ ⌜$⌝ t₂ ⟧ {ℳ} vs = ⟦ t₁ ⟧ vs (refl≤ ℳ) $ ⟦ t₂ ⟧ vs


----------------------------------------------------------------------------------------------------

𝒞 : Model
𝒞 = record
      { World  = Ctx
      ; _≤_    = _⊆_
      ; refl≤  = refl⊆
      ; trans≤ = trans⊆
      ; ⟦◦⟧    = λ Γ → Σ (Γ ⊢ ⌜◦⌝) NNF
      ; ren⟦◦⟧ = λ { e (_ , p) → _ , renNNF e p }
      }

mutual
  ↑ : ∀ {A Γ} → Σ (Γ ⊢ A) NNF → 𝒞 / Γ ⊩ A
  ↑ {⌜◦⌝}     (_ , p)  = _ , p
  ↑ {A ⌜⊃⌝ B} (_ , p₁) = λ e v₂ → let _ , p₂ = ↓ v₂
                                     in ↑ (_ , renNNF e p₁ ⌜$⌝ p₂)

  ↓ : ∀ {A Γ} → 𝒞 / Γ ⊩ A → Σ (Γ ⊢ A) NF
  ↓ {⌜◦⌝}     (_ , p) = _ , nnf p
  ↓ {A ⌜⊃⌝ B} v       = let t , p = ↓ (v (wk⊆ id⊆) (↑ {A} (var zero , var-)))
                          in ⌜λ⌝ t , ⌜λ⌝-

vids : ∀ {Γ} → 𝒞 / Γ ⊩* Γ
vids {[]}    = []
vids {A ∷ Γ} = ↑ {A} (var zero , var-) ∷ vrens (wk⊆ id⊆) vids

⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) NF
⟦ v ⟧⁻¹ = ↓ (v vids)

nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) NF
nbe t = ⟦ ⟦ t ⟧ ⟧⁻¹


----------------------------------------------------------------------------------------------------
