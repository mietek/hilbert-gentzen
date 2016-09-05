-- Basic intuitionistic propositional calculus, without ∨ or ⊥.
-- Tarski-style semantics with contexts as concrete worlds, and glueing for α and ▻.
-- Gentzen-style syntax.

module BasicIPC.Semantics.TarskiGluedGentzen where

open import BasicIPC.Syntax.Common public
open import Common.Semantics public


-- Intuitionistic Tarski models.

record Model : Set₁ where
  infix 3 _⊩ᵅ_ _[⊢]_
  field
    -- Forcing for atomic propositions; monotonic.
    _⊩ᵅ_   : Cx Ty → Atom → Set
    mono⊩ᵅ : ∀ {P Γ Γ′} → Γ ⊆ Γ′ → Γ ⊩ᵅ P → Γ′ ⊩ᵅ P

    -- Gentzen-style syntax representation; monotonic.
    _[⊢]_   : Cx Ty → Ty → Set
    mono[⊢] : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ [⊢] A → Γ′ [⊢] A
    [var]    : ∀ {A Γ}    → A ∈ Γ → Γ [⊢] A
    [lam]    : ∀ {A B Γ}  → Γ , A [⊢] B → Γ [⊢] A ▻ B
    [app]    : ∀ {A B Γ}  → Γ [⊢] A ▻ B → Γ [⊢] A → Γ [⊢] B
    [pair]   : ∀ {A B Γ}  → Γ [⊢] A → Γ [⊢] B → Γ [⊢] A ∧ B
    [fst]    : ∀ {A B Γ}  → Γ [⊢] A ∧ B → Γ [⊢] A
    [snd]    : ∀ {A B Γ}  → Γ [⊢] A ∧ B → Γ [⊢] B
    [unit]   : ∀ {Γ}      → Γ [⊢] ⊤

  infix 3 _[⊢]⋆_
  _[⊢]⋆_ : Cx Ty → Cx Ty → Set
  Γ [⊢]⋆ ∅     = 𝟙
  Γ [⊢]⋆ Ξ , A = Γ [⊢]⋆ Ξ × Γ [⊢] A

open Model {{…}} public


-- Forcing in a particular model.

module _ {{_ : Model}} where
  infix 3 _⊩_
  _⊩_ : Cx Ty → Ty → Set
  Γ ⊩ α P   = Glue (Γ [⊢] α P) (Γ ⊩ᵅ P)
  Γ ⊩ A ▻ B = ∀ {Γ′} → Γ ⊆ Γ′ → Glue (Γ′ [⊢] A ▻ B) (Γ′ ⊩ A → Γ′ ⊩ B)
  Γ ⊩ A ∧ B = Γ ⊩ A × Γ ⊩ B
  Γ ⊩ ⊤    = 𝟙

  infix 3 _⊩⋆_
  _⊩⋆_ : Cx Ty → Cx Ty → Set
  Γ ⊩⋆ ∅     = 𝟙
  Γ ⊩⋆ Ξ , A = Γ ⊩⋆ Ξ × Γ ⊩ A


-- Monotonicity with respect to context inclusion.

module _ {{_ : Model}} where
  mono⊩ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊩ A → Γ′ ⊩ A
  mono⊩ {α P}   η s = mono[⊢] η (syn s) ⅋ mono⊩ᵅ η (sem s)
  mono⊩ {A ▻ B} η s = λ η′ → s (trans⊆ η η′)
  mono⊩ {A ∧ B} η s = mono⊩ {A} η (π₁ s) , mono⊩ {B} η (π₂ s)
  mono⊩ {⊤}    η s = ∙

  mono⊩⋆ : ∀ {Ξ Γ Γ′} → Γ ⊆ Γ′ → Γ ⊩⋆ Ξ → Γ′ ⊩⋆ Ξ
  mono⊩⋆ {∅}     η ∙        = ∙
  mono⊩⋆ {Ξ , A} η (ts , t) = mono⊩⋆ {Ξ} η ts , mono⊩ {A} η t


-- Extraction of syntax representation in a particular model.

module _ {{_ : Model}} where
  reifyʳ : ∀ {A Γ} → Γ ⊩ A → Γ [⊢] A
  reifyʳ {α P}   s = syn s
  reifyʳ {A ▻ B} s = syn (s refl⊆)
  reifyʳ {A ∧ B} s = [pair] (reifyʳ (π₁ s)) (reifyʳ (π₂ s))
  reifyʳ {⊤}    s = [unit]

  reifyʳ⋆ : ∀ {Ξ Γ} → Γ ⊩⋆ Ξ → Γ [⊢]⋆ Ξ
  reifyʳ⋆ {∅}     ∙        = ∙
  reifyʳ⋆ {Ξ , A} (ts , t) = reifyʳ⋆ ts , reifyʳ t


-- Shorthand for variables.

module _ {{_ : Model}} where
  [v₀] : ∀ {A Γ} → Γ , A [⊢] A
  [v₀] = [var] i₀

  [v₁] : ∀ {A B Γ} → Γ , A , B [⊢] A
  [v₁] = [var] i₁

  [v₂] : ∀ {A B C Γ} → Γ , A , B , C [⊢] A
  [v₂] = [var] i₂


-- Useful theorems in functional form.

module _ {{_ : Model}} where
  [multicut] : ∀ {Ξ A Γ} → Γ [⊢]⋆ Ξ → Ξ [⊢] A → Γ [⊢] A
  [multicut] {∅}     ∙        u = mono[⊢] bot⊆ u
  [multicut] {Ξ , B} (ts , t) u = [app] ([multicut] ts ([lam] u)) t


-- Useful theorems in combinatory form.

module _ {{_ : Model}} where
  [ci] : ∀ {A Γ} → Γ [⊢] A ▻ A
  [ci] = [lam] [v₀]

  [ck] : ∀ {A B Γ} → Γ [⊢] A ▻ B ▻ A
  [ck] = [lam] ([lam] [v₁])

  [cs] : ∀ {A B C Γ} → Γ [⊢] (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
  [cs] = [lam] ([lam] ([lam] ([app] ([app] [v₂] [v₀]) ([app] [v₁] [v₀]))))

  [cpair] : ∀ {A B Γ} → Γ [⊢] A ▻ B ▻ A ∧ B
  [cpair] = [lam] ([lam] ([pair] [v₁] [v₀]))

  [cfst] : ∀ {A B Γ} → Γ [⊢] A ∧ B ▻ A
  [cfst] = [lam] ([fst] [v₀])

  [csnd] : ∀ {A B Γ} → Γ [⊢] A ∧ B ▻ B
  [csnd] = [lam] ([snd] [v₀])


-- Additional useful equipment.

module _ {{_ : Model}} where
  _⟪$⟫_ : ∀ {A B Γ} → Γ ⊩ A ▻ B → Γ ⊩ A → Γ ⊩ B
  s ⟪$⟫ a = sem (s refl⊆) a

  ⟪K⟫ : ∀ {A B Γ} → Γ ⊩ A → Γ ⊩ B ▻ A
  ⟪K⟫ {A} a η = let a′ = mono⊩ {A} η a
                in  [app] [ck] (reifyʳ a′) ⅋ K a′

  ⟪S⟫ : ∀ {A B C Γ} → Γ ⊩ A ▻ B ▻ C → Γ ⊩ A ▻ B → Γ ⊩ A → Γ ⊩ C
  ⟪S⟫ s₁ s₂ a = (s₁ ⟪$⟫ a) ⟪$⟫ (s₂ ⟪$⟫ a)

  ⟪S⟫′ : ∀ {A B C Γ} → Γ ⊩ A ▻ B ▻ C → Γ ⊩ (A ▻ B) ▻ A ▻ C
  ⟪S⟫′ {A} {B} {C} s₁ η = let s₁′ = mono⊩ {A ▻ B ▻ C} η s₁
                              t   = syn (s₁′ refl⊆)
                          in  [app] [cs] t ⅋ λ s₂ η′ →
                                let s₁″ = mono⊩ {A ▻ B ▻ C} (trans⊆ η η′) s₁
                                    s₂′ = mono⊩ {A ▻ B} η′ s₂
                                    t′  = syn (s₁″ refl⊆)
                                    u   = syn (s₂′ refl⊆)
                                in  [app] ([app] [cs] t′) u ⅋ ⟪S⟫ s₁″ s₂′

  _⟪,⟫′_ : ∀ {A B Γ} → Γ ⊩ A → Γ ⊩ B ▻ A ∧ B
  _⟪,⟫′_ {A} a η = let a′ = mono⊩ {A} η a
                   in  [app] [cpair] (reifyʳ a′) ⅋ _,_ a′


-- Forcing in a particular world of a particular model, for sequents.

module _ {{_ : Model}} where
  infix 3 _⊩_⇒_
  _⊩_⇒_ : Cx Ty → Cx Ty → Ty → Set
  w ⊩ Γ ⇒ A = w ⊩⋆ Γ → w ⊩ A

  infix 3 _⊩_⇒⋆_
  _⊩_⇒⋆_ : Cx Ty → Cx Ty → Cx Ty → Set
  w ⊩ Γ ⇒⋆ Ξ = w ⊩⋆ Γ → w ⊩⋆ Ξ


-- Entailment, or forcing in all worlds of all models, for sequents.

infix 3 _⊨_
_⊨_ : Cx Ty → Ty → Set₁
Γ ⊨ A = ∀ {{_ : Model}} {w : Cx Ty} → w ⊩ Γ ⇒ A

infix 3 _⊨⋆_
_⊨⋆_ : Cx Ty → Cx Ty → Set₁
Γ ⊨⋆ Ξ = ∀ {{_ : Model}} {w : Cx Ty} → w ⊩ Γ ⇒⋆ Ξ


-- Additional useful equipment, for sequents.

module _ {{_ : Model}} where
  lookup : ∀ {A Γ w} → A ∈ Γ → w ⊩ Γ ⇒ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ

  _⟦$⟧_ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A ▻ B → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ B
  (s₁ ⟦$⟧ s₂) γ = s₁ γ ⟪$⟫ s₂ γ

  ⟦K⟧ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ B ▻ A
  ⟦K⟧ {A} {B} a γ = ⟪K⟫ {A} {B} (a γ)

  ⟦S⟧ : ∀ {A B C Γ w} → w ⊩ Γ ⇒ A ▻ B ▻ C → w ⊩ Γ ⇒ A ▻ B → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ C
  ⟦S⟧ s₁ s₂ a γ = ⟪S⟫ (s₁ γ) (s₂ γ) (a γ)

  _⟦,⟧_ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ B → w ⊩ Γ ⇒ A ∧ B
  (a ⟦,⟧ b) γ = a γ , b γ

  ⟦π₁⟧ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A ∧ B → w ⊩ Γ ⇒ A
  ⟦π₁⟧ s γ = π₁ (s γ)

  ⟦π₂⟧ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A ∧ B → w ⊩ Γ ⇒ B
  ⟦π₂⟧ s γ = π₂ (s γ)
