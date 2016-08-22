-- Tarski-style semantics with explicit Hilbert-style closed syntax representation.

module BasicIS4.Semantics.TarskiClosedHilbert where

open import BasicIS4.Syntax.Common public


-- Tarski models.

record Model : Set₁ where
  infix 3 ⊩ᵅ_ [⊢]_
  field
    -- Forcing for atomic propositions.
    ⊩ᵅ_ : Atom → Set

    -- Hilbert-style closed syntax representation.
    [⊢]_   : Ty → Set
    [app]   : ∀ {A B}   → [⊢] A ▻ B → [⊢] A → [⊢] B
    [ci]    : ∀ {A}     → [⊢] A ▻ A
    [ck]    : ∀ {A B}   → [⊢] A ▻ B ▻ A
    [cs]    : ∀ {A B C} → [⊢] (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
    [box]   : ∀ {A}     → [⊢] A  → [⊢] □ A
    [cdist] : ∀ {A B}   → [⊢] □ (A ▻ B) ▻ □ A ▻ □ B
    [cup]   : ∀ {A}     → [⊢] □ A ▻ □ □ A
    [cdown] : ∀ {A}     → [⊢] □ A ▻ A
    [cpair] : ∀ {A B}   → [⊢] A ▻ B ▻ A ∧ B
    [cfst]  : ∀ {A B}   → [⊢] A ∧ B ▻ A
    [csnd]  : ∀ {A B}   → [⊢] A ∧ B ▻ B
    [tt]    : [⊢] ⊤

  infix 3 [⊢]⋆_
  [⊢]⋆_ : Cx Ty → Set
  [⊢]⋆ ⌀     = 𝟙
  [⊢]⋆ Π , A = [⊢]⋆ Π × [⊢] A

open Model {{…}} public


-- Forcing in a particular model.

module _ {{_ : Model}} where
  infix 3 ⊩_
  ⊩_ : Ty → Set
  ⊩ α P   = [⊢] α P × ⊩ᵅ P
  ⊩ A ▻ B = [⊢] A ▻ B × (⊩ A → ⊩ B)
  ⊩ □ A   = [⊢] □ A × ⊩ A
  ⊩ A ∧ B = ⊩ A × ⊩ B
  ⊩ ⊤    = 𝟙

  infix 3 ⊩⋆_
  ⊩⋆_ : Cx Ty → Set
  ⊩⋆ ⌀     = 𝟙
  ⊩⋆ Π , A = ⊩⋆ Π × ⊩ A


-- Entailment, or forcing in all models.

infix 3 ⊨_
⊨_ : Ty → Set₁
⊨ A = ∀ {{_ : Model}} → ⊩ A


-- Completeness with respect to the syntax representation in a particular model.

module _ {{_ : Model}} where
  reifyʳ : ∀ {A} → ⊩ A → [⊢] A
  reifyʳ {α P}   (t , s) = t
  reifyʳ {A ▻ B} (t , f) = t
  reifyʳ {□ A}   (t , a) = t
  reifyʳ {A ∧ B} (a , b) = [app] ([app] [cpair] (reifyʳ {A} a)) (reifyʳ {B} b)
  reifyʳ {⊤}    ∙       = [tt]

  reifyʳ⋆ : ∀ {Π} → ⊩⋆ Π → [⊢]⋆ Π
  reifyʳ⋆ {⌀}     ∙        = ∙
  reifyʳ⋆ {Π , A} (ts , t) = reifyʳ⋆ ts , reifyʳ t


-- Additional useful equipment.

module _ {{_ : Model}} where
  _⟪$⟫_ : ∀ {A B} → ⊩ A ▻ B → ⊩ A → ⊩ B
  (t , f) ⟪$⟫ a = f a

  ⟪K⟫ : ∀ {A B} → ⊩ A → ⊩ B ▻ A
  ⟪K⟫ a = [app] [ck] (reifyʳ a) , K a

  ⟪S⟫ : ∀ {A B C} → ⊩ A ▻ B ▻ C → ⊩ A ▻ B → ⊩ A → ⊩ C
  ⟪S⟫ (t , f) (u , g) a = let (_ , h) = f a in h (g a)

  ⟪S⟫′ : ∀ {A B C} → ⊩ A ▻ B ▻ C → ⊩ (A ▻ B) ▻ A ▻ C
  ⟪S⟫′ f = [app] [cs] (reifyʳ f) , λ g →
             [app] ([app] [cs] (reifyʳ f)) (reifyʳ g) , ⟪S⟫ f g

  _⟪D⟫_ : ∀ {A B} → ⊩ □ (A ▻ B) → ⊩ □ A → ⊩ □ B
  (t , f) ⟪D⟫ (u , a) = [app] ([app] [cdist] t) u , f ⟪$⟫ a

  _⟪D⟫′_ : ∀ {A B} → ⊩ □ (A ▻ B) → ⊩ □ A ▻ □ B
  _⟪D⟫′_ s = [app] [cdist] (reifyʳ s) , _⟪D⟫_ s

  ⟪↑⟫ : ∀ {A} → ⊩ □ A → ⊩ □ □ A
  ⟪↑⟫ (t , a) = [box] t , (t , a)

  ⟪↓⟫ : ∀ {A} → ⊩ □ A → ⊩ A
  ⟪↓⟫ (t , a) = a

  _⟪,⟫′_ : ∀ {A B} → ⊩ A → ⊩ B ▻ A ∧ B
  _⟪,⟫′_ a = [app] [cpair] (reifyʳ a) , _,_ a


-- Forcing in a particular model, for sequents.

module _ {{_ : Model}} where
  infix 3 ⊩_⇒_
  ⊩_⇒_ : Cx Ty → Ty → Set
  ⊩ Γ ⇒ A = ⊩⋆ Γ → ⊩ A

  infix 3 ⊩_⇒⋆_
  ⊩_⇒⋆_ : Cx Ty → Cx Ty → Set
  ⊩ Γ ⇒⋆ Π = ⊩⋆ Γ → ⊩⋆ Π


-- Entailment, or forcing in all models, for sequents.

infix 3 _⊨_
_⊨_ : Cx Ty → Ty → Set₁
Γ ⊨ A = ∀ {{_ : Model}} → ⊩ Γ ⇒ A

infix 3 _⊨⋆_
_⊨⋆_ : Cx Ty → Cx Ty → Set₁
Γ ⊨⋆ Π = ∀ {{_ : Model}} → ⊩ Γ ⇒⋆ Π


-- Additional useful equipment, for sequents.

module _ {{_ : Model}} where
  lookup : ∀ {A Γ} → A ∈ Γ → ⊩ Γ ⇒ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ

  ⟦λ⟧ : ∀ {A B Γ} → [⊢] A ▻ B → ⊩ Γ , A ⇒ B → ⊩ Γ ⇒ A ▻ B
  ⟦λ⟧ t f γ = t , λ a → f (γ , a)

  _⟦$⟧_ : ∀ {A B Γ} → ⊩ Γ ⇒ A ▻ B → ⊩ Γ ⇒ A → ⊩ Γ ⇒ B
  (f ⟦$⟧ g) γ = f γ ⟪$⟫ g γ

  ⟦S⟧ : ∀ {A B C Γ} → ⊩ Γ ⇒ A ▻ B ▻ C → ⊩ Γ ⇒ A ▻ B → ⊩ Γ ⇒ A → ⊩ Γ ⇒ C
  ⟦S⟧ f g a γ = ⟪S⟫ (f γ) (g γ) (a γ)

  _⟦D⟧_ : ∀ {A B Γ} → ⊩ Γ ⇒ □ (A ▻ B) → ⊩ Γ ⇒ □ A → ⊩ Γ ⇒ □ B
  (s₁ ⟦D⟧ s₂) γ = (s₁ γ) ⟪D⟫ (s₂ γ)

  ⟦↑⟧ : ∀ {A Γ} → ⊩ Γ ⇒ □ A → ⊩ Γ ⇒ □ □ A
  ⟦↑⟧ s γ = ⟪↑⟫ (s γ)

  ⟦↓⟧ : ∀ {A Γ} → ⊩ Γ ⇒ □ A → ⊩ Γ ⇒ A
  ⟦↓⟧ s γ = ⟪↓⟫ (s γ)

  _⟦,⟧_ : ∀ {A B Γ} → ⊩ Γ ⇒ A → ⊩ Γ ⇒ B → ⊩ Γ ⇒ A ∧ B
  (a ⟦,⟧ b) γ = a γ , b γ

  ⟦π₁⟧ : ∀ {A B Γ} → ⊩ Γ ⇒ A ∧ B → ⊩ Γ ⇒ A
  ⟦π₁⟧ s γ = π₁ (s γ)

  ⟦π₂⟧ : ∀ {A B Γ} → ⊩ Γ ⇒ A ∧ B → ⊩ Γ ⇒ B
  ⟦π₂⟧ s γ = π₂ (s γ)
