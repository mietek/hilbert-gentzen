-- Basic intuitionistic modal logic S4, without ∨, ⊥, or ◇.
-- Gentzen-style formalisation of syntax with context pairs, after Pfenning-Davies.
-- Normal forms, neutrals, and spines.

module BasicIS4.Syntax.DyadicGentzenSpinalNormalForm where

open import BasicIS4.Syntax.DyadicGentzen public


-- Commuting propositions for neutrals.

data Tyⁿᵉ : Ty → Set where
  α_ : (P : Atom) → Tyⁿᵉ (α P)
  □_ : (A : Ty) → Tyⁿᵉ (□ A)


-- Derivations.

mutual
  -- Normal forms, or introductions.
  infix 3 _⊢ⁿᶠ_
  data _⊢ⁿᶠ_ : Cx² Ty Ty → Ty → Set where
    neⁿᶠ   : ∀ {A Γ Δ}   → Γ ⁏ Δ ⊢ⁿᵉ A → {{_ : Tyⁿᵉ A}} → Γ ⁏ Δ ⊢ⁿᶠ A
    lamⁿᶠ  : ∀ {A B Γ Δ} → Γ , A ⁏ Δ ⊢ⁿᶠ B → Γ ⁏ Δ ⊢ⁿᶠ A ▻ B
    boxⁿᶠ  : ∀ {A Γ Δ}   → ∅ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ⁿᶠ □ A
    pairⁿᶠ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ⁿᶠ B → Γ ⁏ Δ ⊢ⁿᶠ A ∧ B
    unitⁿᶠ : ∀ {Γ Δ}     → Γ ⁏ Δ ⊢ⁿᶠ ⊤

  -- Neutrals, or eliminations.
  infix 3 _⊢ⁿᵉ_
  data _⊢ⁿᵉ_ : Cx² Ty Ty → Ty → Set where
    spⁿᵉ  : ∀ {A B C Γ Δ} → A ∈ Γ → Γ ⁏ Δ ⊢ˢᵖ A ⦙ B → Γ ⁏ Δ ⊢ᵗᵖ B ⦙ C → Γ ⁏ Δ ⊢ⁿᵉ C
    mspⁿᵉ : ∀ {A B C Γ Δ} → A ∈ Δ → Γ ⁏ Δ ⊢ˢᵖ A ⦙ B → Γ ⁏ Δ ⊢ᵗᵖ B ⦙ C → Γ ⁏ Δ ⊢ⁿᵉ C

  -- Spines.
  infix 3 _⊢ˢᵖ_⦙_
  data _⊢ˢᵖ_⦙_ : Cx² Ty Ty → Ty → Ty → Set where
    nilˢᵖ : ∀ {C Γ Δ} → Γ ⁏ Δ ⊢ˢᵖ C ⦙ C
    appˢᵖ : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊢ˢᵖ B ⦙ C → Γ ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ˢᵖ A ▻ B ⦙ C
    fstˢᵖ : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊢ˢᵖ A ⦙ C → Γ ⁏ Δ ⊢ˢᵖ A ∧ B ⦙ C
    sndˢᵖ : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊢ˢᵖ B ⦙ C → Γ ⁏ Δ ⊢ˢᵖ A ∧ B ⦙ C

  -- Spine tips.
  infix 3 _⊢ᵗᵖ_⦙_
  data _⊢ᵗᵖ_⦙_ : Cx² Ty Ty → Ty → Ty → Set where
    nilᵗᵖ   : ∀ {C Γ Δ} → Γ ⁏ Δ ⊢ᵗᵖ C ⦙ C
    unboxᵗᵖ : ∀ {A C Γ Δ} → Γ ⁏ Δ , A ⊢ⁿᶠ C → Γ ⁏ Δ ⊢ᵗᵖ □ A ⦙ C


-- Translation to simple terms.

mutual
  nf→tm : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ A
  nf→tm (neⁿᶠ t)     = ne→tm t
  nf→tm (lamⁿᶠ t)    = lam (nf→tm t)
  nf→tm (boxⁿᶠ t)    = box t
  nf→tm (pairⁿᶠ t u) = pair (nf→tm t) (nf→tm u)
  nf→tm unitⁿᶠ       = unit

  ne→tm : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ⁿᵉ A → Γ ⁏ Δ ⊢ A
  ne→tm (spⁿᵉ i xs y)  = tp→tm (var i) xs y
  ne→tm (mspⁿᵉ i xs y) = tp→tm (mvar i) xs y

  sp→tm : ∀ {A C Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ˢᵖ A ⦙ C → Γ ⁏ Δ ⊢ C
  sp→tm t nilˢᵖ        = t
  sp→tm t (appˢᵖ xs u) = sp→tm (app t (nf→tm u)) xs
  sp→tm t (fstˢᵖ xs)   = sp→tm (fst t) xs
  sp→tm t (sndˢᵖ xs)   = sp→tm (snd t) xs

  tp→tm : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ˢᵖ A ⦙ B → Γ ⁏ Δ ⊢ᵗᵖ B ⦙ C → Γ ⁏ Δ ⊢ C
  tp→tm t xs nilᵗᵖ       = sp→tm t xs
  tp→tm t xs (unboxᵗᵖ u) = unbox (sp→tm t xs) (nf→tm u)


-- Monotonicity with respect to context inclusion.

mutual
  mono⊢ⁿᶠ : ∀ {A Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊢ⁿᶠ A → Γ′ ⁏ Δ ⊢ⁿᶠ A
  mono⊢ⁿᶠ η (neⁿᶠ t)     = neⁿᶠ (mono⊢ⁿᵉ η t)
  mono⊢ⁿᶠ η (lamⁿᶠ t)    = lamⁿᶠ (mono⊢ⁿᶠ (keep η) t)
  mono⊢ⁿᶠ η (boxⁿᶠ t)    = boxⁿᶠ t
  mono⊢ⁿᶠ η (pairⁿᶠ t u) = pairⁿᶠ (mono⊢ⁿᶠ η t) (mono⊢ⁿᶠ η u)
  mono⊢ⁿᶠ η unitⁿᶠ       = unitⁿᶠ

  mono⊢ⁿᵉ : ∀ {A Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊢ⁿᵉ A → Γ′ ⁏ Δ ⊢ⁿᵉ A
  mono⊢ⁿᵉ η (spⁿᵉ i xs y)  = spⁿᵉ (mono∈ η i) (mono⊢ˢᵖ η xs) (mono⊢ᵗᵖ η y)
  mono⊢ⁿᵉ η (mspⁿᵉ i xs y) = mspⁿᵉ i (mono⊢ˢᵖ η xs) (mono⊢ᵗᵖ η y)

  mono⊢ˢᵖ : ∀ {A C Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊢ˢᵖ A ⦙ C → Γ′ ⁏ Δ ⊢ˢᵖ A ⦙ C
  mono⊢ˢᵖ η nilˢᵖ        = nilˢᵖ
  mono⊢ˢᵖ η (appˢᵖ xs u) = appˢᵖ (mono⊢ˢᵖ η xs) (mono⊢ⁿᶠ η u)
  mono⊢ˢᵖ η (fstˢᵖ xs)   = fstˢᵖ (mono⊢ˢᵖ η xs)
  mono⊢ˢᵖ η (sndˢᵖ xs)   = sndˢᵖ (mono⊢ˢᵖ η xs)

  mono⊢ᵗᵖ : ∀ {A C Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊢ᵗᵖ A ⦙ C → Γ′ ⁏ Δ ⊢ᵗᵖ A ⦙ C
  mono⊢ᵗᵖ η nilᵗᵖ       = nilᵗᵖ
  mono⊢ᵗᵖ η (unboxᵗᵖ u) = unboxᵗᵖ (mono⊢ⁿᶠ η u)


-- Monotonicity with respect to modal context inclusion.

mutual
  mmono⊢ⁿᶠ : ∀ {A Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ′ ⊢ⁿᶠ A
  mmono⊢ⁿᶠ θ (neⁿᶠ t)     = neⁿᶠ (mmono⊢ⁿᵉ θ t)
  mmono⊢ⁿᶠ θ (lamⁿᶠ t)    = lamⁿᶠ (mmono⊢ⁿᶠ θ t)
  mmono⊢ⁿᶠ θ (boxⁿᶠ t)    = boxⁿᶠ (mmono⊢ θ t)
  mmono⊢ⁿᶠ θ (pairⁿᶠ t u) = pairⁿᶠ (mmono⊢ⁿᶠ θ t) (mmono⊢ⁿᶠ θ u)
  mmono⊢ⁿᶠ θ unitⁿᶠ       = unitⁿᶠ

  mmono⊢ⁿᵉ : ∀ {A Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊢ⁿᵉ A → Γ ⁏ Δ′ ⊢ⁿᵉ A
  mmono⊢ⁿᵉ θ (spⁿᵉ i xs y)  = spⁿᵉ i (mmono⊢ˢᵖ θ xs) (mmono⊢ᵗᵖ θ y)
  mmono⊢ⁿᵉ θ (mspⁿᵉ i xs y) = mspⁿᵉ (mono∈ θ i) (mmono⊢ˢᵖ θ xs) (mmono⊢ᵗᵖ θ y)

  mmono⊢ˢᵖ : ∀ {A C Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊢ˢᵖ A ⦙ C → Γ ⁏ Δ′ ⊢ˢᵖ A ⦙ C
  mmono⊢ˢᵖ θ nilˢᵖ        = nilˢᵖ
  mmono⊢ˢᵖ θ (appˢᵖ xs u) = appˢᵖ (mmono⊢ˢᵖ θ xs) (mmono⊢ⁿᶠ θ u)
  mmono⊢ˢᵖ θ (fstˢᵖ xs)   = fstˢᵖ (mmono⊢ˢᵖ θ xs)
  mmono⊢ˢᵖ θ (sndˢᵖ xs)   = sndˢᵖ (mmono⊢ˢᵖ θ xs)

  mmono⊢ᵗᵖ : ∀ {A C Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊢ᵗᵖ A ⦙ C → Γ ⁏ Δ′ ⊢ᵗᵖ A ⦙ C
  mmono⊢ᵗᵖ θ nilᵗᵖ       = nilᵗᵖ
  mmono⊢ᵗᵖ θ (unboxᵗᵖ u) = unboxᵗᵖ (mmono⊢ⁿᶠ (keep θ) u)


-- Monotonicity using context pairs.

mono²⊢ⁿᶠ : ∀ {A Π Π′} → Π ⊆² Π′ → Π ⊢ⁿᶠ A → Π′ ⊢ⁿᶠ A
mono²⊢ⁿᶠ (η , θ) = mono⊢ⁿᶠ η ∘ mmono⊢ⁿᶠ θ

mono²⊢ⁿᵉ : ∀ {A Π Π′} → Π ⊆² Π′ → Π ⊢ⁿᵉ A → Π′ ⊢ⁿᵉ A
mono²⊢ⁿᵉ (η , θ) = mono⊢ⁿᵉ η ∘ mmono⊢ⁿᵉ θ

mono²⊢ˢᵖ : ∀ {A C Π Π′} → Π ⊆² Π′ → Π ⊢ˢᵖ A ⦙ C → Π′ ⊢ˢᵖ A ⦙ C
mono²⊢ˢᵖ (η , θ) = mono⊢ˢᵖ η ∘ mmono⊢ˢᵖ θ

mono²⊢ᵗᵖ : ∀ {A C Π Π′} → Π ⊆² Π′ → Π ⊢ᵗᵖ A ⦙ C → Π′ ⊢ᵗᵖ A ⦙ C
mono²⊢ᵗᵖ (η , θ) = mono⊢ᵗᵖ η ∘ mmono⊢ᵗᵖ θ
