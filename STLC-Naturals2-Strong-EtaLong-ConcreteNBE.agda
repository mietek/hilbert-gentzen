module STLC-Naturals2-Strong-EtaLong-ConcreteNBE where

open import STLC-Naturals2-Strong-EtaLong public


----------------------------------------------------------------------------------------------------

-- semantic values
infix 3 _⊩_
_⊩_ : Ctx → Ty → Set
W ⊩ A ⌜⊃⌝ B = ∀ {W′} → W ⊆ W′ → W′ ⊩ A → W′ ⊩ B
W ⊩ ⌜ℕ⌝     = W ⊢≪ ⌜ℕ⌝

vren : ∀ {W W′ A} → W ⊆ W′ → W ⊩ A → W′ ⊩ A
vren {A = A ⌜⊃⌝ B} e v = λ e′ → v (trans⊆ e e′)
vren {A = ⌜ℕ⌝}     e v = ren≪ e v

open ⊩Kit _⊩_ (λ {W} {W′} {A} → vren {A = A}) public


----------------------------------------------------------------------------------------------------

mutual
  ↑ : ∀ {Γ A} → Γ ⊢≫ A → Γ ⊩ A
  ↑ {A = A ⌜⊃⌝ B} t = λ e v → ↑ (ren≫ e t ⌜$⌝ ↓ v)
  ↑ {A = ⌜ℕ⌝}     t = nnf t

  ↓ : ∀ {Γ A} → Γ ⊩ A → Γ ⊢≪ A
  ↓ {A = A ⌜⊃⌝ B} v = ⌜λ⌝ (↓ (v wk⊆ (↑ (⌜v⌝ zero))))
  ↓ {A = ⌜ℕ⌝}     v = v

vids : ∀ {Γ} → Γ ⊩* Γ
vids {[]}    = []
vids {A ∷ Γ} = ↑ (⌜v⌝ zero) ∷ vrens wk⊆ vids

-- reification
⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Γ ⊢≪ A
⟦ v ⟧⁻¹ = ↓ (v vids)


----------------------------------------------------------------------------------------------------

⟦zero⟧ : ∀ {Γ} → Γ ⊩ ⌜ℕ⌝
⟦zero⟧ = ⌜zero⌝

⟦suc⟧ : ∀ {Γ} → Γ ⊩ ⌜ℕ⌝ ⌜⊃⌝ ⌜ℕ⌝
⟦suc⟧ e v = ⌜suc⌝ v

-- TODO: typo in Abel p.11
⟦rec⟧ : ∀ {Γ A} → Γ ⊩ ⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ (⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A) ⌜⊃⌝ A
⟦rec⟧ e ⌜zero⌝     e′ v₀ e″ vₛ = vren e″ v₀
⟦rec⟧ e (⌜suc⌝ vₙ) e′ v₀ e″ vₛ = vₛ id⊆ (ren≪ (trans⊆ e′ e″) vₙ) id⊆ (⟦rec⟧ e vₙ e′ v₀ e″ vₛ)
⟦rec⟧ e (nnf tₙ)   e′ v₀ e″ vₛ = ↑ (⌜rec⌝ (ren≫ (trans⊆ e′ e″) tₙ) (ren≪ e″ (↓ v₀)) (↓ vₛ))

⟦_⟧Con : ∀ {Γ A} → Con A → Γ ⊨ A
⟦ ⌜zero⌝ ⟧Con vs = ⟦zero⟧
⟦ ⌜suc⌝  ⟧Con vs = ⟦suc⟧
⟦ ⌜rec⌝  ⟧Con vs = ⟦rec⟧

-- reflection
⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ ⌜c⌝ k     ⟧ vs = ⟦ k ⟧Con vs
⟦ ⌜v⌝ i     ⟧ vs = ⟦ i ⟧∋ vs
⟦ ⌜λ⌝ t     ⟧ vs = λ e v → ⟦ t ⟧ (v ∷ vrens e vs)
⟦ t₁ ⌜$⌝ t₂ ⟧ vs = ⟦ t₁ ⟧ vs id⊆ $ ⟦ t₂ ⟧ vs

nbe : ∀ {Γ A} → Γ ⊢ A → Γ ⊢≪ A
nbe t = ⟦ ⟦ t ⟧ ⟧⁻¹


----------------------------------------------------------------------------------------------------
