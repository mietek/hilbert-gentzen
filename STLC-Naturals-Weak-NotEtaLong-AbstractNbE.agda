module STLC-Naturals-Weak-NotEtaLong-AbstractNbE where

open import STLC-Naturals-Weak-NotEtaLong public


----------------------------------------------------------------------------------------------------

record Model : Set₁ where
  infix 4 _≤_
  field
    World  : Set
    Base   : World → Set
    _≤_    : World → World → Set
    refl≤  : ∀ {W} → W ≤ W
    trans≤ : ∀ {W W′ W″} → W ≤ W′ → W′ ≤ W″ → W ≤ W″

open Model public

module _ {ℳ : Model} where
  private
    module ℳ = Model ℳ

  -- semantic values
  infix 3 _⊩_
  _⊩_ : ℳ.World → Ty → Set
  W ⊩ A ⌜⊃⌝ B = ∀ {W′} → W ℳ.≤ W′ → W′ ⊩ A → W′ ⊩ B
  W ⊩ ⌜ℕ⌝     = ∀ {W′} → W ℳ.≤ W′ → ℳ.Base W′

  ren⊩ : ∀ {W W′ A} → W ℳ.≤ W′ → W ⊩ A → W′ ⊩ A
  ren⊩ {A = A ⌜⊃⌝ B} e v = λ e′ → v (ℳ.trans≤ e e′)
  ren⊩ {A = ⌜ℕ⌝}     e v = λ e′ → v (ℳ.trans≤ e e′)

open AbstractKit (λ {ℳ} → _⊩_ {ℳ}) (λ {_} {_} {_} {A} → ren⊩ {_} {_} {_} {A}) public


----------------------------------------------------------------------------------------------------

-- canonical model
𝒞 : Model
𝒞 = record
      { World   = Ctx
      ; Base    = λ Γ → Σ (Γ ⊢ ⌜ℕ⌝) NF
      ; _≤_     = _⊆_
      ; refl≤   = refl⊆
      ; trans≤  = trans⊆
      }

mutual
  ↑ : ∀ {Γ A} → Σ (Γ ⊢ A) NNF → 𝒞 / Γ ⊩ A
  ↑ {A = A ⌜⊃⌝ B} (t , p) = λ e v → ↑ (_ , renNNF e p ⌜$⌝ proj₂ (↓ v))
  ↑ {A = ⌜ℕ⌝}     (t , p) = λ e → _ , nnf (renNNF e p)

  ↓ : ∀ {Γ A} → 𝒞 / Γ ⊩ A → Σ (Γ ⊢ A) λ t → NF t
  ↓ {A = A ⌜⊃⌝ B} v with ↓ (v wk⊆ (↑ (⌜v⌝ zero , ⌜v⌝-)))
  ... | t , p         = ⌜λ⌝ t , ⌜λ⌝-
  ↓ {A = ⌜ℕ⌝}     v = v refl⊆

refl⊩* : ∀ {Γ} → 𝒞 / Γ ⊩* Γ
refl⊩* {[]}    = []
refl⊩* {A ∷ Γ} = ↑ (⌜v⌝ zero , ⌜v⌝-) ∷ ren⊩* wk⊆ refl⊩*

-- reification
⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) NF
⟦ v ⟧⁻¹ = ↓ (v refl⊩*)


----------------------------------------------------------------------------------------------------

-- TODO
-- -- reflection
-- ⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
-- ⟦ ⌜v⌝ i          ⟧     vs = ⟦ i ⟧∋ vs
-- ⟦ ⌜λ⌝ t          ⟧     vs = λ e v → ⟦ t ⟧ (v ∷ ren⊩* e vs)
-- ⟦ t₁ ⌜$⌝ t₂      ⟧ {ℳ} vs = ⟦ t₁ ⟧ vs (refl≤ ℳ) $ ⟦ t₂ ⟧ vs
-- ⟦ ⌜zero⌝         ⟧     vs = λ e → {!!}
-- ⟦ ⌜suc⌝ t        ⟧     vs = λ e → {!!}
-- ⟦ ⌜rec⌝ t₁ t₂ t₃ ⟧     vs = {! !}

-- nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) NF
-- nbe = ⟦_⟧⁻¹ ∘ ⟦_⟧


-- ----------------------------------------------------------------------------------------------------
