-- Normal forms of tree-shaped Gentzen-style derivations.

module New.BasicIPC.Syntax.OpenGentzenNormalForm where

open import New.BasicIPC.Syntax.OpenGentzen public


-- Derivations.

mutual
  -- Normal forms, or introductions.
  infix 3 _⊢ⁿᶠ_
  data _⊢ⁿᶠ_ (Γ : Cx Ty) : Ty → Set where
    neⁿᶠ   : ∀ {A}   → Γ ⊢ⁿᵉ A → Γ ⊢ⁿᶠ A
    lamⁿᶠ  : ∀ {A B} → Γ , A ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ▻ B
    pairⁿᶠ : ∀ {A B} → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ∧ B
    ttⁿᶠ   : Γ ⊢ⁿᶠ ⊤

  -- Neutrals, or eliminations.
  infix 3 _⊢ⁿᵉ_
  data _⊢ⁿᵉ_ (Γ : Cx Ty) : Ty → Set where
    varⁿᵉ : ∀ {A}   → A ∈ Γ → Γ ⊢ⁿᵉ A
    appⁿᵉ : ∀ {A B} → Γ ⊢ⁿᵉ A ▻ B → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᵉ B
    fstⁿᵉ : ∀ {A B} → Γ ⊢ⁿᵉ A ∧ B → Γ ⊢ⁿᵉ A
    sndⁿᵉ : ∀ {A B} → Γ ⊢ⁿᵉ A ∧ B → Γ ⊢ⁿᵉ B

infix 3 _⊢⋆ⁿᶠ_
_⊢⋆ⁿᶠ_ : Cx Ty → Cx Ty → Set
Γ ⊢⋆ⁿᶠ ⌀     = 𝟙
Γ ⊢⋆ⁿᶠ Π , A = Γ ⊢⋆ⁿᶠ Π × Γ ⊢ⁿᶠ A

infix 3 _⊢⋆ⁿᵉ_
_⊢⋆ⁿᵉ_ : Cx Ty → Cx Ty → Set
Γ ⊢⋆ⁿᵉ ⌀     = 𝟙
Γ ⊢⋆ⁿᵉ Π , A = Γ ⊢⋆ⁿᵉ Π × Γ ⊢ⁿᵉ A


-- Translation to simple terms.

mutual
  nf→tm : ∀ {A Γ} → Γ ⊢ⁿᶠ A → Γ ⊢ A
  nf→tm (neⁿᶠ t)     = ne→tm t
  nf→tm (lamⁿᶠ t)    = lam (nf→tm t)
  nf→tm (pairⁿᶠ t u) = pair (nf→tm t) (nf→tm u)
  nf→tm ttⁿᶠ         = tt

  ne→tm : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊢ A
  ne→tm (varⁿᵉ i)   = var i
  ne→tm (appⁿᵉ t u) = app (ne→tm t) (nf→tm u)
  ne→tm (fstⁿᵉ t)   = fst (ne→tm t)
  ne→tm (sndⁿᵉ t)   = snd (ne→tm t)

nf→tm⋆ : ∀ {Π Γ} → Γ ⊢⋆ⁿᶠ Π → Γ ⊢⋆ Π
nf→tm⋆ {⌀}     ∙        = ∙
nf→tm⋆ {Π , A} (ts , t) = nf→tm⋆ ts , nf→tm t

ne→tm⋆ : ∀ {Π Γ} → Γ ⊢⋆ⁿᵉ Π → Γ ⊢⋆ Π
ne→tm⋆ {⌀}     ∙        = ∙
ne→tm⋆ {Π , A} (ts , t) = ne→tm⋆ ts , ne→tm t


-- Monotonicity with respect to context inclusion.

mutual
  mono⊢ⁿᶠ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ⁿᶠ A → Γ′ ⊢ⁿᶠ A
  mono⊢ⁿᶠ η (neⁿᶠ t)     = neⁿᶠ (mono⊢ⁿᵉ η t)
  mono⊢ⁿᶠ η (lamⁿᶠ t)    = lamⁿᶠ (mono⊢ⁿᶠ (keep η) t)
  mono⊢ⁿᶠ η (pairⁿᶠ t u) = pairⁿᶠ (mono⊢ⁿᶠ η t) (mono⊢ⁿᶠ η u)
  mono⊢ⁿᶠ η ttⁿᶠ         = ttⁿᶠ

  mono⊢ⁿᵉ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ⁿᵉ A → Γ′ ⊢ⁿᵉ A
  mono⊢ⁿᵉ η (varⁿᵉ i)   = varⁿᵉ (mono∈ η i)
  mono⊢ⁿᵉ η (appⁿᵉ t u) = appⁿᵉ (mono⊢ⁿᵉ η t) (mono⊢ⁿᶠ η u)
  mono⊢ⁿᵉ η (fstⁿᵉ t)   = fstⁿᵉ (mono⊢ⁿᵉ η t)
  mono⊢ⁿᵉ η (sndⁿᵉ t)   = sndⁿᵉ (mono⊢ⁿᵉ η t)

mono⊢⋆ⁿᶠ : ∀ {Π Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢⋆ⁿᶠ Π → Γ′ ⊢⋆ⁿᶠ Π
mono⊢⋆ⁿᶠ {⌀}     η ∙        = ∙
mono⊢⋆ⁿᶠ {Π , A} η (ts , t) = mono⊢⋆ⁿᶠ η ts , mono⊢ⁿᶠ η t

mono⊢⋆ⁿᵉ : ∀ {Π Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢⋆ⁿᵉ Π → Γ′ ⊢⋆ⁿᵉ Π
mono⊢⋆ⁿᵉ {⌀}     η ∙        = ∙
mono⊢⋆ⁿᵉ {Π , A} η (ts , t) = mono⊢⋆ⁿᵉ η ts , mono⊢ⁿᵉ η t
