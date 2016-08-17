-- Tarski-style semantics with a closed syntactic component, after Gabbay-Nanevski.

module BasicIS4.Semantics.TarskiClosedGabbayNanevski where

open import BasicIS4.Syntax.Common public


-- Tarski models.

record Model : Set₁ where
  infix 3 ⊨ᵅ_
  field
    -- Satisfaction for atomic propositions.
    ⊨ᵅ_ : Atom → Set

open Model {{…}} public




module SyntacticComponent ([_] : Ty → Set) where


  -- Satisfaction in a particular model.

  module _ {{_ : Model}} where
    infix 3 ⊨_
    ⊨_ : Ty → Set
    ⊨ α P   = [ α P ] × ⊨ᵅ P
    ⊨ A ▻ B = [ A ▻ B ] × (⊨ A → ⊨ B)
    ⊨ □ A   = [ A ] × ⊨ A
    ⊨ A ∧ B = ⊨ A × ⊨ B
    ⊨ ⊤    = 𝟙

    infix 3 ⊨⋆_
    ⊨⋆_ : Cx Ty → Set
    ⊨⋆ ⌀     = 𝟙
    ⊨⋆ Π , A = ⊨⋆ Π × ⊨ A


  -- Satisfaction in all models.

  ∀ᴹ⊨_ : Ty → Set₁
  ∀ᴹ⊨ A = ∀ {{_ : Model}} → ⊨ A


  -- Additional useful equipment.

  module _ {{_ : Model}} where
    _⟪$⟫_ : ∀ {A B} → ⊨ A ▻ B → ⊨ A → ⊨ B
    (t , f) ⟪$⟫ a = f a

    ⟪ap⟫ : ∀ {A B C} → ⊨ A ▻ B ▻ C → ⊨ A ▻ B → ⊨ A → ⊨ C
    ⟪ap⟫ (t , f) (u , g) a = let (_ , h) = f a in h (g a)

    ⟪⇓⟫ : ∀ {A} → ⊨ □ A → ⊨ A
    ⟪⇓⟫ (t , a) = a


  -- Satisfaction in a particular model, for sequents.

  module _ {{_ : Model}} where
    infix 3 ⊨_⇒_
    ⊨_⇒_ : Cx Ty → Ty → Set
    ⊨ Γ ⇒ A = ⊨⋆ Γ → ⊨ A

    infix 3 ⊨_⇒⋆_
    ⊨_⇒⋆_ : Cx Ty → Cx Ty → Set
    ⊨ Γ ⇒⋆ Π = ⊨⋆ Γ → ⊨⋆ Π


  -- Satisfaction in all models, for sequents.

  ∀ᴹ⊨_⇒_ : Cx Ty → Ty → Set₁
  ∀ᴹ⊨ Γ ⇒ A = ∀ {{_ : Model}} → ⊨ Γ ⇒ A

  ∀ᴹ⊨_⇒⋆_ : Cx Ty → Cx Ty → Set₁
  ∀ᴹ⊨ Γ ⇒⋆ Π = ∀ {{_ : Model}} → ⊨ Γ ⇒⋆ Π


  -- Additional useful equipment, for sequents.

  module _ {{_ : Model}} where
    lookup : ∀ {A Γ} → A ∈ Γ → ⊨ Γ ⇒ A
    lookup top     (γ , a) = a
    lookup (pop i) (γ , b) = lookup i γ

    ⟦λ⟧ : ∀ {A B Γ} → [ A ▻ B ] → ⊨ Γ , A ⇒ B → ⊨ Γ ⇒ A ▻ B
    ⟦λ⟧ t f γ = t , λ a → f (γ , a)

    _⟦$⟧_ : ∀ {A B Γ} → ⊨ Γ ⇒ A ▻ B → ⊨ Γ ⇒ A → ⊨ Γ ⇒ B
    (f ⟦$⟧ g) γ = f γ ⟪$⟫ g γ

    ⟦ap⟧ : ∀ {A B C Γ} → ⊨ Γ ⇒ A ▻ B ▻ C → ⊨ Γ ⇒ A ▻ B → ⊨ Γ ⇒ A → ⊨ Γ ⇒ C
    ⟦ap⟧ f g a γ = ⟪ap⟫ (f γ) (g γ) (a γ)

    ⟦⇓⟧ : ∀ {A Γ} → ⊨ Γ ⇒ □ A → ⊨ Γ ⇒ A
    ⟦⇓⟧ s γ = ⟪⇓⟫ (s γ)

    _⟦,⟧_ : ∀ {A B Γ} → ⊨ Γ ⇒ A → ⊨ Γ ⇒ B → ⊨ Γ ⇒ A ∧ B
    (a ⟦,⟧ b) γ = a γ , b γ

    ⟦π₁⟧ : ∀ {A B Γ} → ⊨ Γ ⇒ A ∧ B → ⊨ Γ ⇒ A
    ⟦π₁⟧ s γ = π₁ (s γ)

    ⟦π₂⟧ : ∀ {A B Γ} → ⊨ Γ ⇒ A ∧ B → ⊨ Γ ⇒ B
    ⟦π₂⟧ s γ = π₂ (s γ)
