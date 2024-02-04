module STLC-Naturals-Weak-NotEtaLong-AbstractNbE2 where

open import STLC-Naturals-Weak-NotEtaLong public
open import Kit4 public


----------------------------------------------------------------------------------------------------

record Model : Set₁ where
  infix 4 _≤_
  field
    World  : Set
    _≤_    : World → World → Set
    refl≤  : ∀ {W} → W ≤ W
    trans≤ : ∀ {W W′ W″} → W ≤ W′ → W′ ≤ W″ → W ≤ W″
    ⟦ℕ⟧    : World → Set
    ren⟦ℕ⟧ : ∀ {W W′} → W ≤ W′ → ⟦ℕ⟧ W → ⟦ℕ⟧ W′
    ⟦zero⟧ : ∀ {W} → ⟦ℕ⟧ W
    ⟦suc⟧  : ∀ {W} → ⟦ℕ⟧ W → ⟦ℕ⟧ W

  infix 3 _⊩_
  _⊩_ : World → Ty → Set
  -- W ⊩ A ⌜⊃⌝ B = ∀ {W′} → W ≤ W′ → W′ ⊩ A → W′ ⊩ B
  -- W ⊩ ⌜ℕ⌝     = ⟦ℕ⟧ W
  W ⊩ A = recTy {X = World → Set} A
             (λ A recA B recB W → ∀ {W′} → W ≤ W′ → recA W′ → recB W′)
             (λ W → ⟦ℕ⟧ W)
             W

  field
    ⟦rec⟧ : ∀ {W A} → W ⊩ ⌜ℕ⌝ → W ⊩ A → W ⊩ ⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A → W ⊩ A

open Model public

module _ {ℳ : Model} where
  private
    module ℳ = Model ℳ

  vren : ∀ {A W W′} → W ℳ.≤ W′ → W ℳ.⊩ A → W′ ℳ.⊩ A
  vren {A ⌜⊃⌝ B} e v = λ e′ → v (ℳ.trans≤ e e′)
  vren {⌜ℕ⌝}     e v = ℳ.ren⟦ℕ⟧ e v

open ModelKit (kit (λ {ℳ} → _⊩_ ℳ) (λ {ℳ} {A} → vren {ℳ} {A})) public

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ var i                  ⟧         vs = ⟦ i ⟧∋ vs
⟦ ⌜λ⌝ t                  ⟧         vs = λ e v → ⟦ t ⟧ (v ∷ vrens e vs)
⟦ t₁ ⌜$⌝ t₂              ⟧ {ℳ = ℳ} vs = ⟦ t₁ ⟧ vs (refl≤ ℳ) $ ⟦ t₂ ⟧ vs
⟦ ⌜zero⌝                 ⟧ {ℳ = ℳ} vs = ⟦zero⟧ ℳ
⟦ ⌜suc⌝ t                ⟧ {ℳ = ℳ} vs = ⟦suc⟧ ℳ (⟦ t ⟧ vs)
⟦ ⌜rec⌝ {A = A} tₙ t₀ tₛ ⟧ {ℳ = ℳ} vs = ⟦rec⟧ ℳ {A = A} (⟦ tₙ ⟧ vs) (⟦ t₀ ⟧ vs) λ e vₙ e′ vₐ →
                                          ⟦ tₛ ⟧ (vₐ ∷ ren⟦ℕ⟧ ℳ e′ vₙ ∷ vrens (trans≤ ℳ e e′) vs)


----------------------------------------------------------------------------------------------------

-- -- canonical model
-- mutual
--   𝒞 : Model
--   𝒞 = record
--         { World  = Ctx
--         ; _≤_    = _⊆_
--         ; refl≤  = refl⊆
--         ; trans≤ = trans⊆
--         ; ⟦ℕ⟧    = λ Γ → Σ (Γ ⊢ ⌜ℕ⌝) NF
--         ; ren⟦ℕ⟧ = λ { e (_ , p) → _ , renNF e p }
--         ; ⟦zero⟧ = _ , ⌜zero⌝
--         ; ⟦suc⟧  = λ { (_ , p′) → _ , ⌜suc⌝ p′ }
--         ; ⟦rec⟧  =
--             λ {         (_ , ⌜zero⌝)   v₀ vₛ → v₀
--               ;         (_ , ⌜suc⌝ pₙ) v₀ vₛ → vₛ id⊆ (_ , pₙ) id⊆ v₀
--               ; {A = A} (_ , nnf pₙ)   v₀ vₛ → {!!}
-- --                  let _ , p₀ = ↓ {A = A} v₀
-- --                      _ , pₛ = ↓ (vₛ (wk⊆ (wk⊆ id⊆)) (↑ {⌜ℕ⌝} (var (suc zero) , var-))
-- --                                 id⊆ (↑ {A} (var zero , var-))) in
-- --                    ↑ (_ , ⌜rec⌝ pₙ p₀ pₛ)
--               }
--         }

--   ↑ : ∀ {A Γ} → Σ (Γ ⊢ A) NNF → 𝒞 / {!Γ!} ⊩ A
--   ↑ {A ⌜⊃⌝ B} (_ , p₁) = λ e v₂ → let _ , p₂ = ↓ v₂ in
--                            ↑ (_ , renNNF e p₁ ⌜$⌝ p₂)
--   ↑ {⌜ℕ⌝}     (_ , p)  = _ , nnf p

--   ↓ : ∀ {A Γ} → 𝒞 / Γ ⊩ A → Σ ({!Γ!} ⊢ A) NF
--   ↓ {A ⌜⊃⌝ B} v = let t , p = ↓ (v (wk⊆ id⊆) (↑ {A} (var zero , var-))) in
--                     ⌜λ⌝ t , ⌜λ⌝-
--   ↓ {⌜ℕ⌝}     v = v

-- vids : ∀ {Γ} → 𝒞 / Γ ⊩* Γ
-- vids {[]}    = []
-- vids {A ∷ Γ} = ↑ (var {A = A} zero , var-) ∷ vrens (wk⊆ id⊆) vids

-- ⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) NF
-- ⟦ v ⟧⁻¹ = ↓ (v vids)

-- nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) NF
-- nbe t = ⟦ ⟦ t ⟧ ⟧⁻¹


-- ----------------------------------------------------------------------------------------------------
