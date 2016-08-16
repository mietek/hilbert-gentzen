-- Standard Kripke-style possible worlds semantics, based on the McKinsey-Tarski translation.

module New.BasicIPC.Semantics.Kripke.McKinseyTarski where

open import New.BasicIPC.Syntax.Common public


-- Intuitionistic Kripke-McKinsey-Tarski models.

record Model : Set₁ where
  infix 3 _⊩ᵅ_
  field
    World : Set

    -- Intuitionistic accessibility; preorder.
    _≤_    : World → World → Set
    refl≤  : ∀ {w} → w ≤ w
    trans≤ : ∀ {w w′ w″} → w ≤ w′ → w′ ≤ w″ → w ≤ w″

    -- Forcing for atomic propositions; monotonic.
    _⊩ᵅ_   : World → Atom → Set
    mono⊩ᵅ : ∀ {P w w′} → w ≤ w′ → w ⊩ᵅ P → w′ ⊩ᵅ P

open Model {{…}} public


-- Forcing in a particular world of a particular model.

module _ {{_ : Model}} where
  infix 3 _⊩_
  _⊩_ : World → Ty → Set
  w ⊩ α P   = w ⊩ᵅ P
  w ⊩ A ▻ B = ∀ {w′} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B
  w ⊩ A ∧ B = w ⊩ A × w ⊩ B
  w ⊩ ⊤    = 𝟙

  infix 3 _⊩⋆_
  _⊩⋆_ : World → Cx Ty → Set
  w ⊩⋆ ⌀     = 𝟙
  w ⊩⋆ Γ , A = w ⊩⋆ Γ × w ⊩ A


-- Monotonicity with respect to intuitionistic accessibility.

module _ {{_ : Model}} where
  mono⊩ : ∀ {A w w′} → w ≤ w′ → w ⊩ A → w′ ⊩ A
  mono⊩ {α P}   ξ s       = mono⊩ᵅ ξ s
  mono⊩ {A ▻ B} ξ f       = λ ξ′ a → f (trans≤ ξ ξ′) a
  mono⊩ {A ∧ B} ξ (a , b) = mono⊩ {A} ξ a , mono⊩ {B} ξ b
  mono⊩ {⊤}    ξ ∙       = ∙

  mono⊩⋆ : ∀ {Γ w w′} → w ≤ w′ → w ⊩⋆ Γ → w′ ⊩⋆ Γ
  mono⊩⋆ {⌀}     ξ ∙       = ∙
  mono⊩⋆ {Γ , A} ξ (γ , a) = mono⊩⋆ {Γ} ξ γ , mono⊩ {A} ξ a


-- Additional useful equipment.

module _ {{_ : Model}} where
  _⟪$⟫_ : ∀ {A B w} → w ⊩ A ▻ B → w ⊩ A → w ⊩ B
  f ⟪$⟫ a = f refl≤ a

  ⟪const⟫ : ∀ {A B w} → w ⊩ A → w ⊩ B ▻ A
  ⟪const⟫ {A} a ξ = const (mono⊩ {A} ξ a)

  ⟪ap⟫ : ∀ {A B C w} → w ⊩ A ▻ B ▻ C
         → ∀ {w′} → w ≤ w′ → w′ ⊩ A ▻ B
         → ∀ {w″} → w′ ≤ w″ → w″ ⊩ A
         → w″ ⊩ C
  ⟪ap⟫ {A} {B} {C} f ξ g ξ′ a = let f′ = mono⊩ {A ▻ B ▻ C} (trans≤ ξ ξ′) f
                                    g′ = mono⊩ {A ▻ B} ξ′ g
                                in  (f′ refl≤ a) refl≤ (g′ refl≤ a)

  ⟪ap⟫′ : ∀ {A B C w} → w ⊩ A ▻ B ▻ C → w ⊩ A ▻ B → w ⊩ A → w ⊩ C
  ⟪ap⟫′ {A} {B} {C} f g a = ⟪ap⟫ {A} {B} {C} f refl≤ g refl≤ a

  _⟪,⟫_ : ∀ {A B w} → w ⊩ A
          → ∀ {w′} → w ≤ w′ → w′ ⊩ B
          → w′ ⊩ A ∧ B
  _⟪,⟫_ {A} {B} a ξ b = let a′ = mono⊩ {A} ξ a
                        in  a′ , b

  _⟪,⟫′_ : ∀ {A B w} → w ⊩ A → w ⊩ B → w ⊩ A ∧ B
  _⟪,⟫′_ {A} {B} a b = _⟪,⟫_ {A} {B} a refl≤ b


-- Forcing in a particular world of a particular model, for open syntax.

module _ {{_ : Model}} where
  infix 3 _⊩_⇒_
  _⊩_⇒_ : World → Cx Ty → Ty → Set
  w ⊩ Γ ⇒ A = w ⊩⋆ Γ → w ⊩ A

  infix 3 _⊩_⇒⋆_
  _⊩_⇒⋆_ : World → Cx Ty → Cx Ty → Set
  w ⊩ Γ ⇒⋆ Π = w ⊩⋆ Γ → w ⊩⋆ Π


-- Forcing in all worlds of all models, for open syntax.

infix 3 ∀ᴹʷ⊩_⇒_
∀ᴹʷ⊩_⇒_ : Cx Ty → Ty → Set₁
∀ᴹʷ⊩ Γ ⇒ A = ∀ {{_ : Model}} {w : World} → w ⊩ Γ ⇒ A

infix 3 ∀ᴹʷ⊩_⇒⋆_
∀ᴹʷ⊩_⇒⋆_ : Cx Ty → Cx Ty → Set₁
∀ᴹʷ⊩ Γ ⇒⋆ Π = ∀ {{_ : Model}} {w : World} → w ⊩ Γ ⇒⋆ Π


-- Additional useful equipment, for open syntax.

module _ {{_ : Model}} where
  lookup : ∀ {A Γ w} → A ∈ Γ → w ⊩ Γ ⇒ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ

  ⟦λ⟧ : ∀ {A B Γ w} → (∀ {w′} → w′ ⊩ Γ , A ⇒ B) → w ⊩ Γ ⇒ A ▻ B
  ⟦λ⟧ f γ = λ ξ a → f (mono⊩⋆ ξ γ , a)

  _⟦$⟧_ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A ▻ B → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ B
  _⟦$⟧_ {A} {B} f g γ = _⟪$⟫_ {A} {B} (f γ) (g γ)

  ⟦const⟧ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ B ▻ A
  ⟦const⟧ {A} {B} a γ = ⟪const⟫ {A} {B} (a γ)

  ⟦ap⟧ : ∀ {A B C Γ w} → w ⊩ Γ ⇒ A ▻ B ▻ C → w ⊩ Γ ⇒ A ▻ B → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ C
  ⟦ap⟧ {A} {B} {C} f g a γ = ⟪ap⟫′ {A} {B} {C} (f γ) (g γ) (a γ)

  _⟦,⟧_ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ B → w ⊩ Γ ⇒ A ∧ B
  _⟦,⟧_ {A} {B} a b γ = _⟪,⟫′_ {A} {B} (a γ) (b γ)

  ⟦π₁⟧ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A ∧ B → w ⊩ Γ ⇒ A
  ⟦π₁⟧ s γ = π₁ (s γ)

  ⟦π₂⟧ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A ∧ B → w ⊩ Γ ⇒ B
  ⟦π₂⟧ s γ = π₂ (s γ)
