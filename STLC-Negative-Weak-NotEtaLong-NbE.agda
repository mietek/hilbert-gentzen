module STLC-Negative-Weak-NotEtaLong-NbE where

open import STLC-Negative-Weak-NotEtaLong public


----------------------------------------------------------------------------------------------------

record Model : Set₁ where
  field
    World  : Set
    _≤_    : ∀ (W W′ : World) → Set
    refl≤  : ∀ {W} → W ≤ W
    trans≤ : ∀ {W W′ W″} (e : W ≤ W′) (e′ : W′ ≤ W″) → W ≤ W″

open Model public

module _ {ℳ : Model} where
  private
    module ℳ = Model ℳ

  infix 3 _⊩_
  _⊩_ : ∀ (W : ℳ.World) (A : Ty) → Set
  W ⊩ A `⊃ B = ∀ {W′} (e : W ℳ.≤ W′) (o : W′ ⊩ A) → W′ ⊩ B
  W ⊩ A `∧ B = W ⊩ A × W ⊩ B
  W ⊩ `𝟙     = 𝟙

  mov : ∀ {W W′ A} (e : W ℳ.≤ W′) (o : W ⊩ A) → W′ ⊩ A
  mov {A = A `⊃ B} e f         = λ e′ → f (ℳ.trans≤ e e′)
  mov {A = A `∧ B} e (o₁ , o₂) = mov e o₁ , mov e o₂
  mov {A = `𝟙}     e unit      = unit

  infix 3 _⊩*_
  data _⊩*_ (W : ℳ.World) : ∀ (Δ : Ctx) → Set where
    []  : W ⊩* []
    _∷_ : ∀ {Δ A} (o : W ⊩ A) (os : W ⊩* Δ) → W ⊩* A ∷ Δ

  mov* : ∀ {W W′ Δ} (e : W ℳ.≤ W′) (os : W ⊩* Δ) → W′ ⊩* Δ
  mov* e []       = []
  mov* e (o ∷ os) = mov e o ∷ mov* e os

infix 3 _∣_⊩_
_∣_⊩_ : ∀ (ℳ : Model) (W : World ℳ) (A : Ty) → Set
ℳ ∣ W ⊩ A = _⊩_ {ℳ} W A

infix 3 _∣_⊩*_
_∣_⊩*_ : ∀ (ℳ : Model) (W : World ℳ) (Δ : Ctx) → Set
ℳ ∣ W ⊩* Δ = _⊩*_ {ℳ} W Δ

infix 3 _⊨_
_⊨_ : ∀ (Γ : Ctx) (A : Ty) → Set₁
Γ ⊨ A = ∀ {ℳ : Model} {W : World ℳ} (os : ℳ ∣ W ⊩* Γ) → ℳ ∣ W ⊩ A

⟦_⟧∋ : ∀ {Γ A} (i : Γ ∋ A) → Γ ⊨ A
⟦ zero  ⟧∋ (o ∷ os) = o
⟦ suc i ⟧∋ (o ∷ os) = ⟦ i ⟧∋ os

⟦_⟧ : ∀ {Γ A} (d : Γ ⊢ A) → Γ ⊨ A
⟦ `v i     ⟧     os = ⟦ i ⟧∋ os
⟦ `λ d     ⟧     os = λ e o → ⟦ d ⟧ (o ∷ mov* e os)
⟦ d₁ `$ d₂ ⟧ {ℳ} os = ⟦ d₁ ⟧ os (refl≤ ℳ) $ ⟦ d₂ ⟧ os
⟦ d₁ `, d₂ ⟧     os = ⟦ d₁ ⟧ os , ⟦ d₂ ⟧ os
⟦ `proj₁ d ⟧     os = proj₁ (⟦ d ⟧ os)
⟦ `proj₂ d ⟧     os = proj₂ (⟦ d ⟧ os)
⟦ `unit    ⟧     os = unit


----------------------------------------------------------------------------------------------------

-- canonical model
𝒞 : Model
𝒞 = record
      { World  = Ctx
      ; _≤_    = _⊆_
      ; refl≤  = refl⊆
      ; trans≤ = trans⊆
      }

mutual
  ↓ : ∀ {Γ A} {d : Γ ⊢ A} (p : NNF d) → 𝒞 ∣ Γ ⊩ A
  ↓ {A = A `⊃ B} p = λ e o → ↓ (renNNF e p `$ proj₂ (↑ o))
  ↓ {A = A `∧ B} p = ↓ (`proj₁ p) , ↓ (`proj₂ p)
  ↓ {A = `𝟙}     p = unit

  ↑ : ∀ {Γ A} (o : 𝒞 ∣ Γ ⊩ A) → Σ (Γ ⊢ A) λ d → NF d
  ↑ {A = A `⊃ B} f         with ↑ (f wk⊆ (↓ (`v zero)))
  ... | d , p                = `λ d , `λ d
  ↑ {A = A `∧ B} (o₁ , o₂) with ↑ o₁ | ↑ o₂
  ... | d₁ , p₁ | d₂ , p₂    = d₁ `, d₂ , d₁ `, d₂
  ↑ {A = `𝟙}     unit      = `unit , `unit

refl⊩* : ∀ {Γ} → 𝒞 ∣ Γ ⊩* Γ
refl⊩* {[]}    = []
refl⊩* {A ∷ Γ} = ↓ (`v zero) ∷ mov* wk⊆ refl⊩*

reify : ∀ {Γ A} (o : Γ ⊨ A) → Σ (Γ ⊢ A) λ d′ → NF d′
reify o = ↑ (o refl⊩*)

-- NOTE: we don't know whether d reduces to d′
nbe : ∀ {Γ A} (d : Γ ⊢ A) → Σ (Γ ⊢ A) λ d′ → NF d′
nbe = reify ∘ ⟦_⟧


----------------------------------------------------------------------------------------------------
