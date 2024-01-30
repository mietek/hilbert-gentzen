module STLC-Naturals2-Strong-EtaLong where

open import STLC-Naturals2 public


----------------------------------------------------------------------------------------------------

-- β-short η-long strong normal forms
mutual
  data NF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜λ⌝    : ∀ {A B} {t : A ∷ Γ ⊢ B} (p : NF t) → NF (⌜λ⌝ t)
    ⌜zero⌝ : NF (⌜c⌝ ⌜zero⌝)
    ⌜suc⌝  : ∀ {t : Γ ⊢ ⌜ℕ⌝} (p : NF t) → NF (⌜c⌝ ⌜suc⌝ ⌜$⌝ t)
    nnf    : ∀ {A} {t : Γ ⊢ A} (p : NNF t) → NF t

  -- neutrals
  data NNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜v⌝-  : ∀ {A} {i : Γ ∋ A} → NNF (⌜v⌝ i)
    _⌜$⌝_ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (p₁ : NNF t₁) (p₂ : NF t₂) → NNF (t₁ ⌜$⌝ t₂)
    ⌜rec⌝ : ∀ {A} {tₙ : Γ ⊢ ⌜ℕ⌝} {t₀ : Γ ⊢ A} {t₁ : Γ ⊢ ⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A} (pₙ : NNF tₙ) (p₀ : NF t₀)
              (p₁ : NF t₁) →
            NNF (⌜c⌝ ⌜rec⌝ ⌜$⌝ tₙ ⌜$⌝ t₀ ⌜$⌝ t₁)

open NFKit NF NNF public


----------------------------------------------------------------------------------------------------

-- β-short η-long strong normal forms (direct)
mutual
  infix 3 _⋘_
  data _⋘_ (Γ : Ctx) : Ty → Set where
    ⌜λ⌝    : ∀ {A B} (t : A ∷ Γ ⋘ B) → Γ ⋘ A ⌜⊃⌝ B
    ⌜zero⌝ : Γ ⋘ ⌜ℕ⌝
    ⌜suc⌝  : ∀ (t : Γ ⋘ ⌜ℕ⌝) → Γ ⋘ ⌜ℕ⌝
    nnf    : ∀ (t : Γ ⋙ ⌜ℕ⌝) → Γ ⋘ ⌜ℕ⌝

  -- neutrals
  infix 3 _⋙_
  data _⋙_ (Γ : Ctx) : Ty → Set where
    ⌜v⌝   : ∀ {A} (i : Γ ∋ A) → Γ ⋙ A
    _⌜$⌝_ : ∀ {A B} (t₁ : Γ ⋙ A ⌜⊃⌝ B) (t₂ : Γ ⋘ A) → Γ ⋙ B
    ⌜rec⌝ : ∀ {A} (tₙ : Γ ⋙ ⌜ℕ⌝) (t₀ : Γ ⋘ A) (tₛ : Γ ⋘ ⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A)  → Γ ⋙ A

-- renaming
mutual
  ren⋘ : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ⋘ A → Γ′ ⋘ A
  ren⋘ e (⌜λ⌝ t)   = ⌜λ⌝ (ren⋘ (keep e) t)
  ren⋘ e ⌜zero⌝    = ⌜zero⌝
  ren⋘ e (⌜suc⌝ t) = ren⋘ e t
  ren⋘ e (nnf t)   = nnf (ren⋙ e t)

  ren⋙ : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ⋙ A → Γ′ ⋙ A
  ren⋙ e (⌜v⌝ i)          = ⌜v⌝ (ren∋ e i)
  ren⋙ e (t₁ ⌜$⌝ t₂)      = ren⋙ e t₁ ⌜$⌝ ren⋘ e t₂
  ren⋙ e (⌜rec⌝ tₙ t₀ tₛ) = ⌜rec⌝ (ren⋙ e tₙ) (ren⋘ e t₀) (ren⋘ e tₛ)


----------------------------------------------------------------------------------------------------

-- definitional equality
infix 4 _≝_
data _≝_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
  refl≝  : ∀ {A} {t : Γ ⊢ A} → t ≝ t
  sym≝   : ∀ {A} {t t′ : Γ ⊢ A} (eq : t ≝ t′) → t′ ≝ t
  trans≝ : ∀ {A} {t t′ t″ : Γ ⊢ A} (eq : t ≝ t′) (eq′ : t′ ≝ t″) → t ≝ t″
  congλ  : ∀ {A B} {t t′ : A ∷ Γ ⊢ B} (eq : t ≝ t′) → ⌜λ⌝ t ≝ ⌜λ⌝ t′
  cong$  : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (eq₁ : t₁ ≝ t₁′) (eq₂ : t₂ ≝ t₂′) →
           t₁ ⌜$⌝ t₂ ≝ t₁′ ⌜$⌝ t₂′
  βred⊃  : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′ : Γ ⊢ B} (eq : t′ ≡ t₁ [ t₂ ]) →
           ⌜λ⌝ t₁ ⌜$⌝ t₂ ≝ t′
  βredℕ₀ : ∀ {A} {t₀ : Γ ⊢ A} {tₛ : Γ ⊢ ⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A} →
           ⌜c⌝ ⌜rec⌝ ⌜$⌝ ⌜c⌝ ⌜zero⌝ ⌜$⌝ t₀ ⌜$⌝ tₛ ≝ t₀
  βredℕₛ : ∀ {A} {tₙ : Γ ⊢ ⌜ℕ⌝} {t₀ : Γ ⊢ A} {tₛ : Γ ⊢ ⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A} →
           ⌜c⌝ ⌜rec⌝ ⌜$⌝ (⌜c⌝ ⌜suc⌝ ⌜$⌝ tₙ) ⌜$⌝ t₀ ⌜$⌝ tₛ ≝
             tₛ ⌜$⌝ tₙ ⌜$⌝ (⌜c⌝ ⌜rec⌝ ⌜$⌝ tₙ ⌜$⌝ t₀ ⌜$⌝ tₛ)
  ηexp⊃  : ∀ {A B} {t t′ : Γ ⊢ A ⌜⊃⌝ B} (eq : t′ ≡ ⌜λ⌝ (weak⊢ t ⌜$⌝ ⌜v⌝ zero)) → t ≝ t′

open ≝Kit (λ {Γ} {A} {t} → refl≝ {t = t}) sym≝ trans≝ public


----------------------------------------------------------------------------------------------------

-- uniqueness of proofs
mutual
  uniNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NF t) → p ≡ p′
  uniNF (⌜λ⌝ p)           (⌜λ⌝ p′)           = ⌜λ⌝ & uniNF p p′
  uniNF ⌜zero⌝            ⌜zero⌝             = refl
  uniNF (⌜suc⌝ p)         (⌜suc⌝ p′)         = ⌜suc⌝ & uniNF p p′
  uniNF (⌜suc⌝ p)         (nnf (() ⌜$⌝ p₂′))
  uniNF (nnf (() ⌜$⌝ p₂)) (⌜suc⌝ p′)
  uniNF (nnf p)           (nnf p′)           = nnf & uniNNF p p′

  uniNNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NNF t) → p ≡ p′
  uniNNF ⌜v⌝-                        ⌜v⌝-                         = refl
  uniNNF (p₁ ⌜$⌝ p₂)                 (p₁′ ⌜$⌝ p₂′)                = _⌜$⌝_ & uniNNF p₁ p₁′
                                                                      ⊗ uniNF p₂ p₂′
  uniNNF (((() ⌜$⌝ _) ⌜$⌝ _) ⌜$⌝ p₂) (⌜rec⌝ pₙ′ p₀′ pₛ′)
  uniNNF (⌜rec⌝ pₙ p₀ pₛ)            (((() ⌜$⌝ _) ⌜$⌝ _) ⌜$⌝ p₂′)
  uniNNF (⌜rec⌝ pₙ p₀ pₛ)            (⌜rec⌝ pₙ′ p₀′ pₛ′)          = ⌜rec⌝ & uniNNF pₙ pₙ′
                                                                      ⊗ uniNF p₀ p₀′ ⊗ uniNF pₛ pₛ′


----------------------------------------------------------------------------------------------------

-- stability under renaming
mutual
  ren⊢NF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NF t → NF (ren⊢ e t)
  ren⊢NF e (⌜λ⌝ p)   = ⌜λ⌝ (ren⊢NF (keep e) p)
  ren⊢NF e ⌜zero⌝    = ⌜zero⌝
  ren⊢NF e (⌜suc⌝ p) = ⌜suc⌝ (ren⊢NF e p)
  ren⊢NF e (nnf p)   = nnf (ren⊢NNF e p)

  ren⊢NNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NNF t → NNF (ren⊢ e t)
  ren⊢NNF e ⌜v⌝-             = ⌜v⌝-
  ren⊢NNF e (p₁ ⌜$⌝ p₂)      = ren⊢NNF e p₁ ⌜$⌝ ren⊢NF e p₂
  ren⊢NNF e (⌜rec⌝ pₙ p₀ pₛ) = ⌜rec⌝ (ren⊢NNF e pₙ) (ren⊢NF e p₀) (ren⊢NF e pₛ)


----------------------------------------------------------------------------------------------------
