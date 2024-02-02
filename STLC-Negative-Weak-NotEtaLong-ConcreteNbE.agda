module STLC-Negative-Weak-NotEtaLong-ConcreteNbE where

open import STLC-Negative-Weak-NotEtaLong public
open import Kit4 public


----------------------------------------------------------------------------------------------------

infix 3 _⊩_
_⊩_ : Ctx → Ty → Set
W ⊩ A ⌜⊃⌝ B = ∀ {W′} → W ⊆ W′ → W′ ⊩ A → W′ ⊩ B
W ⊩ A ⌜∧⌝ B = W ⊩ A × W ⊩ B
W ⊩ ⌜𝟙⌝     = 𝟙

vren : ∀ {W W′ A} → W ⊆ W′ → W ⊩ A → W′ ⊩ A
vren {A = A ⌜⊃⌝ B} e v         = λ e′ → v (trans⊆ e e′)
vren {A = A ⌜∧⌝ B} e (v₁ , v₂) = vren e v₁ , vren e v₂
vren {A = ⌜𝟙⌝}     e unit      = unit

vk! = valkit _⊩_ (λ {W} {W′} {A} → vren {A = A})
open ValKit vk! public

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ var i     ⟧ vs = ⟦ i ⟧∋ vs
⟦ ⌜λ⌝ t     ⟧ vs = λ e v → ⟦ t ⟧ (v ∷ vrens e vs)
⟦ t₁ ⌜$⌝ t₂ ⟧ vs = ⟦ t₁ ⟧ vs id⊆ $ ⟦ t₂ ⟧ vs
⟦ t₁ ⌜,⌝ t₂ ⟧ vs = ⟦ t₁ ⟧ vs , ⟦ t₂ ⟧ vs
⟦ ⌜proj₁⌝ t ⟧ vs = proj₁ (⟦ t ⟧ vs)
⟦ ⌜proj₂⌝ t ⟧ vs = proj₂ (⟦ t ⟧ vs)
⟦ ⌜unit⌝    ⟧ vs = unit


----------------------------------------------------------------------------------------------------

mutual
  ↑ : ∀ {Γ A} → Σ (Γ ⊢ A) NNF → Γ ⊩ A
  ↑ {A = A ⌜⊃⌝ B} (_ , p₁) = λ e v₂ → let _ , p₂ = ↓ v₂
                                         in ↑ (_ , renNNF e p₁ ⌜$⌝ p₂)
  ↑ {A = A ⌜∧⌝ B} (_ , p)  = ↑ (_ , ⌜proj₁⌝ p) , ↑ (_ , ⌜proj₂⌝ p)
  ↑ {A = ⌜𝟙⌝}     (_ , p)  = unit

  ↓ : ∀ {Γ A} → Γ ⊩ A → Σ (Γ ⊢ A) NF
  ↓ {A = A ⌜⊃⌝ B} v         = let t , p = ↓ (v wk⊆ (↑ (var zero , var-)))
                                in ⌜λ⌝ t , ⌜λ⌝-
  ↓ {A = A ⌜∧⌝ B} (v₁ , v₂) = let t₁ , p₁ = ↓ v₁
                                  t₂ , p₂ = ↓ v₂
                                in t₁ ⌜,⌝ t₂ , -⌜,⌝-
  ↓ {A = ⌜𝟙⌝}     unit        = _ , ⌜unit⌝

vids : ∀ {Γ} → Γ ⊩* Γ
vids {[]}    = []
vids {A ∷ Γ} = ↑ (var zero , var-) ∷ vrens wk⊆ vids

⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) NF
⟦ v ⟧⁻¹ = ↓ (v vids)

nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) NF
nbe t = ⟦ ⟦ t ⟧ ⟧⁻¹


----------------------------------------------------------------------------------------------------
