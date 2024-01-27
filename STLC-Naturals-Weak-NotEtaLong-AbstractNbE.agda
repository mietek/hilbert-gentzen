module STLC-Naturals-Weak-NotEtaLong-AbstractNbE where

open import STLC-Naturals-Weak-NotEtaLong public


----------------------------------------------------------------------------------------------------

-- record Frame : Set₁ where
--   infix 4 _≤_
--   field
--     World  : Set
--     _≤_    : World → World → Set
--     refl≤  : ∀ {W} → W ≤ W
--     trans≤ : ∀ {W W′ W″} → W ≤ W′ → W′ ≤ W″ → W ≤ W″
--     ⟦ℕ⟧    : World → Set
--     ⟦renℕ⟧ : ∀ {W W′} → W ≤ W′ → ⟦ℕ⟧ W → ⟦ℕ⟧ W′
--     ⟦zero⟧ : ∀ {W} → ⟦ℕ⟧ W
--     ⟦suc⟧  : ∀ {W} → ⟦ℕ⟧ W → ⟦ℕ⟧ W

--   -- semantic values
--   infix 3 _⊩_
--   _⊩_ : World → Ty → Set
--   _⊩_ = λ { W (A ⌜⊃⌝ B) → ∀ {W′} → W ≤ W′ → {!!} -- W′ ⊩ A → W′ ⊩ B
--            ; W ⌜ℕ⌝       → ⟦ℕ⟧ W
--            }

--   field
--     ⟦rec⟧ : ∀ {W A} → ⟦ℕ⟧ W → W ⊩ A → (∀ {W′} → W ≤ W′ → ⟦ℕ⟧ W′ → W′ ⊩ A → W′ ⊩ A) → W ⊩ A


-- -- record Model (ℱ : Frame) : Set where
-- --   open Frame ℱ public
-- --   field
-- --     ⟦rec⟧ : ∀ {W A} → ⟦ℕ⟧ W → W ⊩ A → (∀ {W′} → W ≤ W′ → ⟦ℕ⟧ W′ → W′ ⊩ A → W′ ⊩ A) → W ⊩ A

-- -- open Model public

-- -- module _ {ℱ} {ℳ : Model ℱ} where
-- --   private
-- --     module ℳ = Model ℳ

-- --   ren⊩ : ∀ {W W′ A} → W ℳ.≤ W′ → W ℳ.⊩ A → W′ ℳ.⊩ A
-- --   ren⊩ {A = A ⌜⊃⌝ B} e v = λ e′ → v (ℳ.trans≤ e e′)
-- --   ren⊩ {A = ⌜ℕ⌝}     e v = ℳ.⟦renℕ⟧ e v

-- --   -- semantic environments
-- --   infix 3 _⊩*_
-- --   data _⊩*_ (W : ℳ.World) : Ctx → Set where
-- --     []  : W ⊩* []
-- --     _∷_ : ∀ {Δ A} (v : W ℳ.⊩ A) (vs : W ⊩* Δ) → W ⊩* A ∷ Δ

-- --   ren⊩* : ∀ {W W′ Δ} → W ℳ.≤ W′ → W ⊩* Δ → W′ ⊩* Δ
-- --   ren⊩* e []                 = []
-- --   ren⊩* e (_∷_ {A = A} v vs) = ren⊩ {A = A} e v ∷ ren⊩* e vs

-- -- infix 3 _/_⊩_
-- -- _/_⊩_ : ∀ {ℱ} (ℳ : Model ℱ) (W : World ℳ) → Ty → Set
-- -- ℳ / W ⊩ A = _⊩_ ℳ W A

-- -- infix 3 _/_⊩*_
-- -- _/_⊩*_ : ∀ {ℱ} (ℳ : Model ℱ) (W : World ℳ) → Ctx → Set
-- -- ℳ / W ⊩* Δ = {!_⊩*_!} -- _⊩*_ ℳ W Δ

-- -- -- infix 3 _⊨_
-- -- -- _⊨_ : Ctx → Ty → Set₁
-- -- -- Γ ⊨ A = ∀ {ℳ : Model} {W : World ℳ} → ℳ / W ⊩* Γ → ℳ / W ⊩ A


-- -- -- -- open AbstractKit (λ {ℳ} → _ℳ.⊩_ {ℳ}) (λ {_} {_} {_} {A} → ren⊩ {_} {_} {_} {A}) public

-- -- -- -- -- reflection
-- -- -- -- ⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
-- -- -- -- ⟦ ⌜v⌝ i          ⟧     vs = ⟦ i ⟧∋ vs
-- -- -- -- ⟦ ⌜λ⌝ t          ⟧     vs = λ e v → ⟦ t ⟧ (v ∷ ren⊩* e vs)
-- -- -- -- ⟦ t₁ ⌜$⌝ t₂      ⟧ {ℳ} vs = ⟦ t₁ ⟧ vs (refl≤ ℳ) $ ⟦ t₂ ⟧ vs
-- -- -- -- ⟦ ⌜zero⌝         ⟧ {ℳ} vs = ⟦zero⟧ ℳ
-- -- -- -- ⟦ ⌜suc⌝ t        ⟧ {ℳ} vs = ⟦suc⟧ ℳ (⟦ t ⟧ vs)
-- -- -- -- ⟦ ⌜rec⌝ tₙ t₀ tₛ ⟧ {ℳ} vs = {!!}


-- -- -- -- ----------------------------------------------------------------------------------------------------

-- -- -- -- -- canonical model
-- -- -- -- 𝒞 : Model
-- -- -- -- 𝒞 = record
-- -- -- --       { World  = Ctx
-- -- -- --       ; _≤_    = _⊆_
-- -- -- --       ; refl≤  = refl⊆
-- -- -- --       ; trans≤ = trans⊆
-- -- -- --       ; ⟦ℕ⟧    = λ Γ → Σ (Γ ⊢ ⌜ℕ⌝) NF
-- -- -- --       ; ⟦renℕ⟧ = λ { e (t , p) → ren e t , renNF e p }
-- -- -- --       ; ⟦zero⟧ = ⌜zero⌝ , ⌜zero⌝
-- -- -- --       ; ⟦suc⟧  = λ { (t , p) → ⌜suc⌝ t , ⌜suc⌝ p }
-- -- -- --       }

-- -- -- -- mutual
-- -- -- --   ↑ : ∀ {Γ A} → Σ (Γ ⊢ A) NNF → 𝒞 / Γ ⊩ A
-- -- -- --   ↑ {A = A ⌜⊃⌝ B} (t , p) = λ e v → ↑ (_ , renNNF e p ⌜$⌝ proj₂ (↓ v))
-- -- -- --   ↑ {A = ⌜ℕ⌝}     (t , p) = t , nnf p

-- -- -- --   ↓ : ∀ {Γ A} → 𝒞 / Γ ⊩ A → Σ (Γ ⊢ A) λ t → NF t
-- -- -- --   ↓ {A = A ⌜⊃⌝ B} v with ↓ (v wk⊆ (↑ (⌜v⌝ {A = A} zero , ⌜v⌝-)))
-- -- -- --   ... | t , p         = ⌜λ⌝ t , ⌜λ⌝-
-- -- -- --   ↓ {A = ⌜ℕ⌝}     v = v

-- -- -- -- refl⊩* : ∀ {Γ} → 𝒞 / Γ ⊩* Γ
-- -- -- -- refl⊩* {[]}    = []
-- -- -- -- refl⊩* {A ∷ Γ} = ↑ (⌜v⌝ {A = A} zero , ⌜v⌝-) ∷ ren⊩* wk⊆ refl⊩*

-- -- -- -- -- reification
-- -- -- -- ⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) NF
-- -- -- -- ⟦ v ⟧⁻¹ = ↓ (v refl⊩*)

-- -- -- -- nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) NF
-- -- -- -- nbe = ⟦_⟧⁻¹ ∘ ⟦_⟧


-- -- -- -- ----------------------------------------------------------------------------------------------------
