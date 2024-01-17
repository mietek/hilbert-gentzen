module STLC-Negative-Weak-NotEtaLong-ConcreteNbE where

open import STLC-Negative-Weak-NotEtaLong public


----------------------------------------------------------------------------------------------------

-- semantic objects
infix 3 _⊩_
_⊩_ : Ctx → Ty → Set
W ⊩ A `⊃ B = ∀ {W′} → W ⊆ W′ → W′ ⊩ A → W′ ⊩ B
W ⊩ A `∧ B = W ⊩ A × W ⊩ B
W ⊩ `𝟙     = 𝟙

ren⊩ : ∀ {W W′ A} → W ⊆ W′ → W ⊩ A → W′ ⊩ A
ren⊩ {A = A `⊃ B} e f         = λ e′ → f (trans⊆ e e′)
ren⊩ {A = A `∧ B} e (o₁ , o₂) = ren⊩ e o₁ , ren⊩ e o₂
ren⊩ {A = `𝟙}     e unit      = unit

open ConcreteKit _⊩_ (λ {_} {_} {A} → ren⊩ {_} {_} {A}) public

-- reflection
⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ `v i     ⟧ os = ⟦ i ⟧∋ os
⟦ `λ t     ⟧ os = λ e o → ⟦ t ⟧ (o ∷ ren⊩* e os)
⟦ t₁ `$ t₂ ⟧ os = ⟦ t₁ ⟧ os refl⊆ $ ⟦ t₂ ⟧ os
⟦ t₁ `, t₂ ⟧ os = ⟦ t₁ ⟧ os , ⟦ t₂ ⟧ os
⟦ `proj₁ t ⟧ os = proj₁ (⟦ t ⟧ os)
⟦ `proj₂ t ⟧ os = proj₂ (⟦ t ⟧ os)
⟦ `unit    ⟧ os = unit


----------------------------------------------------------------------------------------------------

mutual
  ↑ : ∀ {Γ A} {t : Γ ⊢ A} → NNF t → Γ ⊩ A
  ↑ {A = A `⊃ B} p = λ e o → ↑ (renNNF e p `$ proj₂ (↓ o))
  ↑ {A = A `∧ B} p = ↑ (`proj₁ p) , ↑ (`proj₂ p)
  ↑ {A = `𝟙}     p = unit

  ↓ : ∀ {Γ A} → Γ ⊩ A → Σ (Γ ⊢ A) λ t → NF t
  ↓ {A = A `⊃ B} f         with ↓ (f wk⊆ (↑ (`v {i = zero})))
  ... | t , p                = `λ t , `λ
  ↓ {A = A `∧ B} (o₁ , o₂) with ↓ o₁ | ↓ o₂
  ... | t₁ , p₁ | t₂ , p₂    = t₁ `, t₂ , _`,_
  ↓ {A = `𝟙}     unit      = `unit , `unit

refl⊩* : ∀ {Γ} → Γ ⊩* Γ
refl⊩* {[]}    = []
refl⊩* {A ∷ Γ} = ↑ (`v {i = zero}) ∷ ren⊩* wk⊆ refl⊩*

-- reification
⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) λ t′ → NF t′
⟦ o ⟧⁻¹ = ↓ (o refl⊩*)

nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) λ t′ → NF t′
nbe = ⟦_⟧⁻¹ ∘ ⟦_⟧


----------------------------------------------------------------------------------------------------
