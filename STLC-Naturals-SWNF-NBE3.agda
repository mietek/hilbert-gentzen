----------------------------------------------------------------------------------------------------

-- normalization-by-evaluation to β-short semi-weak normal form, with explicit model

-- using an explicit recursion principle on types allows defining the model as a single record that
-- includes a `⟦rec⟧` field after the definition of `_⊩_`

-- TODO: unfortunately, defining the canonical model seems impossible

module STLC-Naturals-SWNF-NBE3 where

open import STLC-Naturals-SWNF public
open import Kit4 public


----------------------------------------------------------------------------------------------------

recTy : ∀ {𝓍} {X : Set 𝓍} → Ty → (Ty → X → Ty → X → X) → X → X
recTy (A ⌜⊃⌝ B) f⊃ fℕ = f⊃ A (recTy A f⊃ fℕ) B (recTy B f⊃ fℕ)
recTy ⌜ℕ⌝       f⊃ fℕ = fℕ

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
  vren {A ⌜⊃⌝ B} ρ v = λ ρ′ → v (ℳ.trans≤ ρ ρ′)
  vren {⌜ℕ⌝}     ρ v = ℳ.ren⟦ℕ⟧ ρ v

open ModelKit (kit (λ {ℳ} → _⊩_ ℳ) (λ {ℳ} {A} → vren {ℳ} {A})) public

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ var i                  ⟧         γ = ⟦ i ⟧∋ γ
⟦ ⌜λ⌝ t                  ⟧         γ = λ ρ v → ⟦ t ⟧ (vren§ ρ γ , v)
⟦ t₁ ⌜$⌝ t₂              ⟧ {ℳ = ℳ} γ = ⟦ t₁ ⟧ γ (refl≤ ℳ) $ ⟦ t₂ ⟧ γ
⟦ ⌜zero⌝                 ⟧ {ℳ = ℳ} γ = ⟦zero⟧ ℳ
⟦ ⌜suc⌝ t                ⟧ {ℳ = ℳ} γ = ⟦suc⟧ ℳ (⟦ t ⟧ γ)
⟦ ⌜rec⌝ {A = A} tₙ t₀ tₛ ⟧ {ℳ = ℳ} γ = ⟦rec⟧ ℳ {A = A} (⟦ tₙ ⟧ γ) (⟦ t₀ ⟧ γ) λ ρ vₙ ρ′ vₐ →
                                          ⟦ tₛ ⟧ ((vren§ (trans≤ ℳ ρ ρ′) γ , ren⟦ℕ⟧ ℳ ρ′ vₙ) , vₐ)


----------------------------------------------------------------------------------------------------

-- -- canonical model
-- mutual
--   𝒞 : Model
--   𝒞 = record
--         { World  = Ctx
--         ; _≤_    = _⊑_
--         ; refl≤  = refl⊑
--         ; trans≤ = trans⊑
--         ; ⟦ℕ⟧    = λ Γ → Σ (Γ ⊢ ⌜ℕ⌝) NF
--         ; ren⟦ℕ⟧ = λ { e (_ , p) → _ , renNF e p }
--         ; ⟦zero⟧ = _ , ⌜zero⌝
--         ; ⟦suc⟧  = λ { (_ , p) → _ , ⌜suc⌝ p }
--         ; ⟦rec⟧  =
--             λ {         (_ , ⌜zero⌝)   v₀ vₛ → v₀
--               ;         (_ , ⌜suc⌝ pₙ) v₀ vₛ → vₛ id⊑ (_ , pₙ) id⊑ v₀
--               ; {A = A} (_ , nnf pₙ)   v₀ vₛ → {!!}                                   -- hole #1
-- --                  let _ , p₀ = ↓ {A} v₀
-- --                      _ , pₛ = ↓ (vₛ (wk⊑ (wk⊑ id⊑)) (↑ {⌜ℕ⌝} (var (wk∋ zero) , var-))
-- --                                 id⊑ (↑ {A} (var zero , var-))) in
-- --                    ↑ (_ , ⌜rec⌝ pₙ p₀ pₛ)
--               }
--         }

--   ↑ : ∀ {A Γ} → Σ (Γ ⊢ A) NNF → 𝒞 / {!Γ!} ⊩ A                                      -- hole #2
--   ↑ {A ⌜⊃⌝ B} (_ , p₁) = λ e v₂ → let _ , p₂ = ↓ v₂ in
--                            ↑ (_ , renNNF e p₁ ⌜$⌝ p₂)
--   ↑ {⌜ℕ⌝}     (_ , p)  = _ , nnf p

--   ↓ : ∀ {A Γ} → 𝒞 / Γ ⊩ A → Σ ({!Γ!} ⊢ A) NF                                       -- hole #3
--   ↓ {A ⌜⊃⌝ B} v = let t , p = ↓ (v (wk⊑ id⊑) (↑ {A} (var zero , var-))) in
--                     ⌜λ⌝ t , ⌜λ⌝-
--   ↓ {⌜ℕ⌝}     v = v

-- vid§ : ∀ {Γ} → 𝒞 / Γ ⊩§ Γ
-- vid§ {∙}     = ∙
-- vid§ {Γ , A} = vren§ (wk⊑ id⊑) vid§ , ↑ {A} (var zero , var-)

-- ⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) NF
-- ⟦ v ⟧⁻¹ = ↓ (v vid§)

-- nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) NF
-- nbe t = ⟦ ⟦ t ⟧ ⟧⁻¹


-- ----------------------------------------------------------------------------------------------------
