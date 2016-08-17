-- Non-canonical model equipment for Kripke-style semantics.

module BasicIS4.Semantics.KripkeDyadicNonCanonicalModelEquipment where

open import Common.ContextPair public
open import BasicIS4.Syntax.Common public




module SyntacticComponent
    (_⁏_⊢_  : Cx Ty → Cx Ty → Ty → Set)
    (mono²⊢ : ∀ {A Γ Γ′ Δ Δ′} → (Γ , Δ) ⊆² (Γ′ , Δ′) → Γ ⁏ Δ ⊢ A → Γ′ ⁏ Δ′ ⊢ A)
    (up      : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ (□ A) → Γ ⁏ Δ ⊢ (□ □ A))
    (down    : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ (□ A) → Γ ⁏ Δ ⊢ A)
    (lift    : ∀ {Γ A Δ} → Γ ⁏ Δ ⊢ A → (□⋆ Γ) ⁏ Δ ⊢ (□ A)) where


  -- Worlds.

  Worldᶜ : Set
  Worldᶜ = Cx² Ty


  -- Intuitionistic accessibility.

  infix 3 _≤ᶜ_
  _≤ᶜ_ : Worldᶜ → Worldᶜ → Set
  _≤ᶜ_ = _⊆²_

  refl≤ᶜ : ∀ {w} → w ≤ᶜ w
  refl≤ᶜ = refl⊆²

  trans≤ᶜ : ∀ {w w′ w″} → w ≤ᶜ w′ → w′ ≤ᶜ w″ → w ≤ᶜ w″
  trans≤ᶜ = trans⊆²

  bot≤ᶜ : ∀ {w} → ⌀² ≤ᶜ w
  bot≤ᶜ = bot⊆²


  -- Not the canonical modal accessibility, based on the 4 axiom.

  infix 3 _Яᶜ_
  _Яᶜ_ : Worldᶜ → Worldᶜ → Set
  (Γ , Δ) Яᶜ (Γ′ , Δ′) = ∀ {A} → Γ ⁏ Δ ⊢ (□ A) → Γ′ ⁏ Δ′ ⊢ (□ □ A)

  reflЯᶜ : ∀ {w} → w Яᶜ w
  reflЯᶜ = up

  transЯᶜ : ∀ {w w′ w″} → w Яᶜ w′ → w′ Яᶜ w″ → w Яᶜ w″
  transЯᶜ ζ ζ′ = down ∘ ζ′ ∘ ζ

  botЯᶜ : ∀ {w} → ⌀² Яᶜ w
  botЯᶜ = mono²⊢ bot≤ᶜ ∘ up

  liftЯᶜ : ∀ {Γ Δ} → (Γ , Δ) Яᶜ (□⋆ Γ , Δ)
  liftЯᶜ = down ∘ lift ∘ up


  -- Composition of accessibility.

  infix 3 _≤⨾Яᶜ_
  _≤⨾Яᶜ_ : Worldᶜ → Worldᶜ → Set
  _≤⨾Яᶜ_ = _≤ᶜ_ ⨾ _Яᶜ_

  infix 3 _Я⨾≤ᶜ_
  _Я⨾≤ᶜ_ : Worldᶜ → Worldᶜ → Set
  _Я⨾≤ᶜ_ = _Яᶜ_ ⨾ _≤ᶜ_

  refl≤⨾Яᶜ : ∀ {w} → w ≤⨾Яᶜ w
  refl≤⨾Яᶜ {w} = w , (refl≤ᶜ , reflЯᶜ)

  reflЯ⨾≤ᶜ : ∀ {w} → w Я⨾≤ᶜ w
  reflЯ⨾≤ᶜ {w} = w , (reflЯᶜ , refl≤ᶜ)


  -- Persistence condition, after Iemhoff; included by Ono.
  --
  --   w′      v′  →           v′
  --   ◌───Я───●   →           ●
  --   │           →         ╱
  --   ≤  ξ,ζ      →       Я
  --   │           →     ╱
  --   ●           →   ●
  --   w           →   w

  ≤⨾Я→Яᶜ : ∀ {v′ w} → w ≤⨾Яᶜ v′ → w Яᶜ v′
  ≤⨾Я→Яᶜ (w′ , (ξ , ζ)) = ζ ∘ mono²⊢ ξ


  -- Brilliance condition, after Iemhoff.
  --
  --           v′  →           v′
  --           ●   →           ●
  --           │   →         ╱
  --      ζ,ξ  ≤   →       Я
  --           │   →     ╱
  --   ●───Я───◌   →   ●
  --   w       v   →   w

  Я⨾≤→Яᶜ : ∀ {w v′} → w Я⨾≤ᶜ v′ → w Яᶜ v′
  Я⨾≤→Яᶜ (v , (ζ , ξ)) = mono²⊢ ξ ∘ ζ


  -- Minor persistence condition, included by Božić and Došen.
  --
  --   w′      v′  →           v′
  --   ◌───Я───●   →           ●
  --   │           →           │
  --   ≤  ξ,ζ      →           ≤
  --   │           →           │
  --   ●           →   ●───Я───◌
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

  ≤⨾Я→Я⨾≤ᶜ : ∀ {v′ w} → w ≤⨾Яᶜ v′ → w Я⨾≤ᶜ v′
  ≤⨾Я→Я⨾≤ᶜ {v′} ξ,ζ = v′ , (≤⨾Я→Яᶜ ξ,ζ , refl≤ᶜ)

  transЯ⨾≤ᶜ : ∀ {w′ w w″} → w Я⨾≤ᶜ w′ → w′ Я⨾≤ᶜ w″ → w Я⨾≤ᶜ w″
  transЯ⨾≤ᶜ {w′} (v , (ζ , ξ)) (v′ , (ζ′ , ξ′)) =
    let v″ , (ζ″ , ξ″) = ≤⨾Я→Я⨾≤ᶜ (w′ , (ξ , ζ′))
    in  v″ , (transЯᶜ ζ ζ″ , trans≤ᶜ ξ″ ξ′)

  ≤→Яᶜ : ∀ {v′ w} → w ≤ᶜ v′ → w Яᶜ v′
  ≤→Яᶜ {v′} ξ = ≤⨾Я→Яᶜ (v′ , (ξ , reflЯᶜ))


  -- Minor brilliance condition, included by Ewald and Alechina et al.
  --
  --           v′  →   w′      v′
  --           ●   →   ◌───Я───●
  --           │   →   │
  --      ζ,ξ  ≤   →   ≤
  --           │   →   │
  --   ●───Я───◌   →   ●
  --   w       v   →   w
  --
  --           v′      w″  →   v″              w″
  --           ◌───R───●   →   ◌───────R───────●
  --           │           →   │
  --           ≤  ξ′,ζ′    →   │
  --   v       │           →   │
  --   ◌───R───●           →   ≤
  --   │       w′          →   │
  --   ≤  ξ,ζ              →   │
  --   │                   →   │
  --   ●                   →   ●
  --   w                   →   w

  Я⨾≤→≤⨾Яᶜ : ∀ {w v′} → w Я⨾≤ᶜ v′ → w ≤⨾Яᶜ v′
  Я⨾≤→≤⨾Яᶜ {w} ζ,ξ = w , (refl≤ᶜ , Я⨾≤→Яᶜ ζ,ξ)

  trans≤⨾Яᶜ : ∀ {w′ w w″} → w ≤⨾Яᶜ w′ → w′ ≤⨾Яᶜ w″ → w ≤⨾Яᶜ w″
  trans≤⨾Яᶜ {w′} (v , (ξ , ζ)) (v′ , (ξ′ , ζ′)) =
    let v″ , (ξ″ , ζ″) = Я⨾≤→≤⨾Яᶜ (w′ , (ζ , ξ′))
    in  v″ , (trans≤ᶜ ξ ξ″ , transЯᶜ ζ″ ζ′)

  ≤→Яᶜ′ : ∀ {w v′} → w ≤ᶜ v′ → w Яᶜ v′
  ≤→Яᶜ′ {w} ξ = Я⨾≤→Яᶜ (w , (reflЯᶜ , ξ))


  -- Infimum (greatest lower bound) of accessibility.
  --
  --   w′
  --   ●
  --   │
  --   ≤  ξ,ζ
  --   │
  --   ◌───R───●
  --   w       v

  infix 3 _≤⊓Яᶜ_
  _≤⊓Яᶜ_ : Worldᶜ → Worldᶜ → Set
  _≤⊓Яᶜ_ = _≤ᶜ_ ⊓ _Яᶜ_

  infix 3 _Я⊓≤ᶜ_
  _Я⊓≤ᶜ_ : Worldᶜ → Worldᶜ → Set
  _Я⊓≤ᶜ_ = _Яᶜ_ ⊓ _≤ᶜ_

  ≤⊓Я→Я⊓≤ᶜ : ∀ {w′ v} → w′ ≤⊓Яᶜ v → v Я⊓≤ᶜ w′
  ≤⊓Я→Я⊓≤ᶜ (w , (ξ , ζ)) = w , (ζ , ξ)

  Я⊓≤→≤⊓Яᶜ : ∀ {w′ v} → v Я⊓≤ᶜ w′ → w′ ≤⊓Яᶜ v
  Я⊓≤→≤⊓Яᶜ (w , (ζ , ξ)) = w , (ξ , ζ)


  -- Supremum (least upper bound) of accessibility.
  --
  --   w′      v′
  --   ●───R───◌
  --           │
  --      ξ,ζ  ≤
  --           │
  --           ●
  --           v

  infix 3 _≤⊔Яᶜ_
  _≤⊔Яᶜ_ : Worldᶜ → Worldᶜ → Set
  _≤⊔Яᶜ_ = _≤ᶜ_ ⊔ _Яᶜ_

  infix 3 _Я⊔≤ᶜ_
  _Я⊔≤ᶜ_ : Worldᶜ → Worldᶜ → Set
  _Я⊔≤ᶜ_ = _Яᶜ_ ⊔ _≤ᶜ_

  ≤⊔Я→Я⊔≤ᶜ : ∀ {w′ v} → w′ ≤⊔Яᶜ v → v Я⊔≤ᶜ w′
  ≤⊔Я→Я⊔≤ᶜ (v′ , (ξ , ζ)) = v′ , (ζ , ξ)

  Я⊔≤→≤⊔Яᶜ : ∀ {w′ v} → v Я⊔≤ᶜ w′ → w′ ≤⊔Яᶜ v
  Я⊔≤→≤⊔Яᶜ (v′ , (ζ , ξ)) = v′ , (ξ , ζ)


  -- Infimum-to-supremum condition, included by Ewald.
  --
  --   w′          →   w′      v′
  --   ●           →   ●───Я───◌
  --   │           →           │
  --   ≤  ξ,ζ      →           ≤
  --   │           →           │
  --   ◌───Я───●   →           ●
  --   w       v   →           v

  -- NOTE: This could be more precise.
  ≤⊓Я→≤⊔Яᶜ : ∀ {v w′} → w′ ≤⊓Яᶜ v → v ≤⊔Яᶜ w′
  ≤⊓Я→≤⊔Яᶜ {v} {w′} (w , (ξ , ζ)) =
    (w′ ⧺² v) , (weak⊆²⧺ᵣ , mono²⊢ (weak⊆²⧺ₗ v) ∘ up)


  -- Supremum-to-infimum condition.
  --
  --   w′      v′  →   w′
  --   ●───Я───◌   →   ●
  --           │   →   │
  --      ξ,ζ  ≤   →   ≤
  --           │   →   │
  --           ●   →   ◌───Я───●
  --           v   →   w       v

  -- NOTE: This could be more precise.
  ≤⊔Я→≤⊓Яᶜ : ∀ {w′ v} → v ≤⊔Яᶜ w′ → w′ ≤⊓Яᶜ v
  ≤⊔Я→≤⊓Яᶜ (v′ , (ξ , ζ)) = ⌀² , (bot≤ᶜ , botЯᶜ)
