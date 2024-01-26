module STLC-Negative-Weak-NotEtaLong-ConcreteNbE where

open import STLC-Negative-Weak-NotEtaLong public


----------------------------------------------------------------------------------------------------

-- semantic values
infix 3 _⊩_
_⊩_ : Ctx → Ty → Set
W ⊩ A ⌜⊃⌝ B = ∀ {W′} → W ⊆ W′ → W′ ⊩ A → W′ ⊩ B
W ⊩ A ⌜∧⌝ B = W ⊩ A × W ⊩ B
W ⊩ ⌜𝟙⌝     = 𝟙

ren⊩ : ∀ {W W′ A} → W ⊆ W′ → W ⊩ A → W′ ⊩ A
ren⊩ {A = A ⌜⊃⌝ B} e v         = λ e′ → v (trans⊆ e e′)
ren⊩ {A = A ⌜∧⌝ B} e (v₁ , v₂) = ren⊩ e v₁ , ren⊩ e v₂
ren⊩ {A = ⌜𝟙⌝}     e unit      = unit

open ConcreteKit _⊩_ (λ {_} {_} {A} → ren⊩ {_} {_} {A}) public

-- reflection
⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ ⌜v⌝ i     ⟧ vs = ⟦ i ⟧∋ vs
⟦ ⌜λ⌝ t     ⟧ vs = λ e v → ⟦ t ⟧ (v ∷ ren⊩* e vs)
⟦ t₁ ⌜$⌝ t₂ ⟧ vs = ⟦ t₁ ⟧ vs refl⊆ $ ⟦ t₂ ⟧ vs
⟦ t₁ ⌜,⌝ t₂ ⟧ vs = ⟦ t₁ ⟧ vs , ⟦ t₂ ⟧ vs
⟦ ⌜proj₁⌝ t ⟧ vs = proj₁ (⟦ t ⟧ vs)
⟦ ⌜proj₂⌝ t ⟧ vs = proj₂ (⟦ t ⟧ vs)
⟦ ⌜unit⌝    ⟧ vs = unit


----------------------------------------------------------------------------------------------------

mutual
  ↑ : ∀ {Γ A} → Σ (Γ ⊢ A) NNF → Γ ⊩ A
  ↑ {A = A ⌜⊃⌝ B} (t , p) = λ e v → ↑ (_ , renNNF e p ⌜$⌝ proj₂ (↓ v))
  ↑ {A = A ⌜∧⌝ B} (t , p) = ↑ (_ , ⌜proj₁⌝ p) , ↑ (_ , ⌜proj₂⌝ p)
  ↑ {A = ⌜𝟙⌝}     (t , p) = unit

  ↓ : ∀ {Γ A} → Γ ⊩ A → Σ (Γ ⊢ A) λ t → NF t
  ↓ {A = A ⌜⊃⌝ B} v         with ↓ (v wk⊆ (↑ (⌜v⌝ zero , ⌜v⌝-)))
  ... | t , p                 = ⌜λ⌝ t , ⌜λ⌝-
  ↓ {A = A ⌜∧⌝ B} (v₁ , v₂) with ↓ v₁ | ↓ v₂
  ... | t₁ , p₁ | t₂ , p₂     = t₁ ⌜,⌝ t₂ , -⌜,⌝-
  ↓ {A = ⌜𝟙⌝}     unit        = ⌜unit⌝ , ⌜unit⌝

refl⊩* : ∀ {Γ} → Γ ⊩* Γ
refl⊩* {[]}    = []
refl⊩* {A ∷ Γ} = ↑ (⌜v⌝ zero , ⌜v⌝-) ∷ ren⊩* wk⊆ refl⊩*

-- reification
⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) NF
⟦ v ⟧⁻¹ = ↓ (v refl⊩*)

nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) NF
nbe = ⟦_⟧⁻¹ ∘ ⟦_⟧


----------------------------------------------------------------------------------------------------
