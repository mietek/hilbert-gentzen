module STLC-Base-Weak-NotEtaLong-AbstractNbE where

open import STLC-Base-Weak-NotEtaLong public


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

  -- semantic values
  infix 3 _⊩_
  _⊩_ : ℳ.World → Ty → Set
  W ⊩ ⌜◦⌝     = ℳ.⟦◦⟧ W
  W ⊩ A ⌜⊃⌝ B = ∀ {W′} → W ℳ.≤ W′ → W′ ⊩ A → W′ ⊩ B

  ren⊩ : ∀ {W W′ A} → W ℳ.≤ W′ → W ⊩ A → W′ ⊩ A
  ren⊩ {A = ⌜◦⌝}     e v = ℳ.ren⟦◦⟧ e v
  ren⊩ {A = A ⌜⊃⌝ B} e v = λ e′ → v (ℳ.trans≤ e e′)

open ModelKit (λ {ℳ} → _⊩_ {ℳ}) (λ {ℳ} {W} {W′} {A} → ren⊩ {A = A}) public

-- reflection
⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ ⌜v⌝ i     ⟧     vs = ⟦ i ⟧∋ vs
⟦ ⌜λ⌝ t     ⟧     vs = λ e v → ⟦ t ⟧ (v ∷ ren⊩* e vs)
⟦ t₁ ⌜$⌝ t₂ ⟧ {ℳ} vs = ⟦ t₁ ⟧ vs (refl≤ ℳ) $ ⟦ t₂ ⟧ vs


----------------------------------------------------------------------------------------------------

-- canonical model
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
  ↑ : ∀ {Γ A} → Σ (Γ ⊢ A) NNF → 𝒞 / Γ ⊩ A
  ↑ {A = ⌜◦⌝}     (_ , p)  = _ , p
  ↑ {A = A ⌜⊃⌝ B} (_ , p₁) = λ e v₂ → let _ , p₂ = ↓ v₂ in
                               ↑ (_ , renNNF e p₁ ⌜$⌝ p₂)

  ↓ : ∀ {Γ A} → 𝒞 / Γ ⊩ A → Σ (Γ ⊢ A) NF
  ↓ {A = ⌜◦⌝}     (_ , p) = _ , nnf p
  ↓ {A = A ⌜⊃⌝ B} v       = let t , p = ↓ (v wk⊆ (↑ (⌜v⌝ {A = A} zero , ⌜v⌝-))) in
                              ⌜λ⌝ t , ⌜λ⌝-

refl⊩* : ∀ {Γ} → 𝒞 / Γ ⊩* Γ
refl⊩* {[]}    = []
refl⊩* {A ∷ Γ} = ↑ (⌜v⌝ {A = A} zero , ⌜v⌝-) ∷ ren⊩* wk⊆ refl⊩*

-- reification
⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) NF
⟦ v ⟧⁻¹ = ↓ (v refl⊩*)

nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) NF
nbe t = ⟦ ⟦ t ⟧ ⟧⁻¹


----------------------------------------------------------------------------------------------------
