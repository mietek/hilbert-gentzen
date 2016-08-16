-- Kripke-style possible worlds semantics, after Božić-Došen.

module BasicIS4.Semantics.KripkeBozicDosen where

open import BasicIS4.Syntax.Common public


-- Intuitionistic modal Kripke models, with Božić-Došen frame conditions.

record Model : Set₁ where
  infix 3 _⊩ᵅ_
  field
    World : Set

    -- Intuitionistic accessibility; preorder.
    _≤_    : World → World → Set
    refl≤  : ∀ {w} → w ≤ w
    trans≤ : ∀ {w w′ w″} → w ≤ w′ → w′ ≤ w″ → w ≤ w″

    -- Modal accessibility; preorder.
    _R_    : World → World → Set
    reflR  : ∀ {w} → w R w
    transR : ∀ {w w′ w″} → w R w′ → w′ R w″ → w R w″

    -- Forcing for atomic propositions; monotonic.
    _⊩ᵅ_   : World → Atom → Set
    mono⊩ᵅ : ∀ {P w w′} → w ≤ w′ → w ⊩ᵅ P → w′ ⊩ᵅ P


    -- Minor persistence condition.
    --
    --   w′      v′  →           v′
    --   ◌───R───●   →           ●
    --   │           →           │
    --   ≤  ξ,ζ      →           ≤
    --   │           →           │
    --   ●           →   ●───R───◌
    --   w           →   w       v
    --
    --                   w″  →                   w″
    --                   ●   →                   ●
    --                   │   →                   │
    --             ξ′,ζ′ ≤   →                   │
    --                   │   →                   │
    --           ●───R───◌   →                   ≤
    --           │       v′  →                   │
    --      ξ,ζ  ≤           →                   │
    --           │           →                   │
    --   ●───R───◌           →   ●───────R───────◌
    --   w       v           →   w               v″

    ≤⨾R→R⨾≤ : ∀ {v′ w} → (_≤_ ⨾ _R_) w v′ → (_R_ ⨾ _≤_) w v′

  _R⨾≤_ : World → World → Set
  _R⨾≤_ = _R_ ⨾ _≤_

  reflR⨾≤ : ∀ {w} → w R⨾≤ w
  reflR⨾≤ {w} = w , (reflR , refl≤)

  transR⨾≤ : ∀ {w′ w w″} → w R⨾≤ w′ → w′ R⨾≤ w″ → w R⨾≤ w″
  transR⨾≤ {w′} (v , (ζ , ξ)) (v′ , (ζ′ , ξ′)) =
    let v″ , (ζ″ , ξ″) = ≤⨾R→R⨾≤ (w′ , (ξ , ζ′))
    in  v″ , (transR ζ ζ″ , trans≤ ξ″ ξ′)

open Model {{…}} public


module _ {{_ : Model}} where
  infix 3 _⊩_
  _⊩_ : World → Ty → Set
  w ⊩ α P   = w ⊩ᵅ P
  w ⊩ A ▻ B = ∀ {w′} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B
  -- NOTE: Only modal accessibility here.
  w ⊩ □ A   = ∀ {v′} → w R v′ → v′ ⊩ A
  w ⊩ A ∧ B = w ⊩ A × w ⊩ B
  w ⊩ ⊤    = 𝟙

  infix 3 _⊩⋆_
  _⊩⋆_ : World → Cx Ty → Set
  w ⊩⋆ ⌀     = 𝟙
  w ⊩⋆ Γ , A = w ⊩⋆ Γ × w ⊩ A


  -- Monotonicity with respect to intuitionistic accessibility.

  mono⊩ : ∀ {A w w′} → w ≤ w′ → w ⊩ A → w′ ⊩ A
  mono⊩ {α P}   ξ s       = mono⊩ᵅ ξ s
  mono⊩ {A ▻ B} ξ f       = λ ξ′ a → f (trans≤ ξ ξ′) a
  mono⊩ {□ A}   ξ □f      = λ ζ → let v , (ζ′ , ξ′) = ≤⨾R→R⨾≤ (_ , (ξ , ζ))
                                    in  mono⊩ {A} ξ′ (□f ζ′)
  mono⊩ {A ∧ B} ξ (a , b) = mono⊩ {A} ξ a , mono⊩ {B} ξ b
  mono⊩ {⊤}    ξ ∙       = ∙

  mono⊩⋆ : ∀ {Γ w w′} → w ≤ w′ → w ⊩⋆ Γ → w′ ⊩⋆ Γ
  mono⊩⋆ {⌀}     ξ ∙       = ∙
  mono⊩⋆ {Γ , A} ξ (γ , a) = mono⊩⋆ {Γ} ξ γ , mono⊩ {A} ξ a


-- Forcing in all models.

infix 3 _ᴹ⊩_
_ᴹ⊩_ : Cx Ty → Ty → Set₁
Γ ᴹ⊩ A = ∀ {{_ : Model}} {w : World} → w ⊩⋆ Γ → w ⊩ A

infix 3 _ᴹ⊩⋆_
_ᴹ⊩⋆_ : Cx Ty → Cx Ty → Set₁
Γ ᴹ⊩⋆ Π = ∀ {{_ : Model}} {w : World} → w ⊩⋆ Γ → w ⊩⋆ Π

infix 3 _⁏_ᴹ⊩_
_⁏_ᴹ⊩_ : Cx Ty → Cx Ty → Ty → Set₁
Γ ⁏ Δ ᴹ⊩ A = ∀ {{_ : Model}} {w : World}
              → w ⊩⋆ Γ → (∀ {v′} → w R v′ → v′ ⊩⋆ Δ) → w ⊩ A

-- Additional useful equipment.

lookup : ∀ {A Γ} → A ∈ Γ → Γ ᴹ⊩ A
lookup top     (γ , a) = a
lookup (pop i) (γ , b) = lookup i γ
