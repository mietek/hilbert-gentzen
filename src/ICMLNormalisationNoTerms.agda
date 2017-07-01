module ICMLNormalisationNoTerms where

open import ICMLSemanticsNoTerms public


-- Absolute values.

infix 3 _⊨_
_⊨_ : Cx → Ty → Set₁
Δ ⁏ Γ ⊨ A = ∀ {{_ : Model}} {w} →
               (∀ {w′} → w′ Я w → π₁ (peek w′) ⁏ ∅ ⊢⧆ Δ) →
               (∀ {w′} → w′ Я w → w′ ⊩⧆ Δ) →
               w ⊩⋆ Γ →
               w ⊩ A

infix 3 _⊨⋆_
_⊨⋆_ : Cx → Ty⋆ → Set₁
Δ ⁏ Γ ⊨⋆ Ξ = ∀ {{_ : Model}} {w} →
                (∀ {w′} → w′ Я w → π₁ (peek w′) ⁏ ∅ ⊢⧆ Δ) →
                (∀ {w′} → w′ Я w → w′ ⊩⧆ Δ) →
                w ⊩⋆ Γ →
                w ⊩⋆ Ξ


-- Soundness.

mutual
  ⟦_⟧ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A → Δ ⁏ Γ ⊨ A
  ⟦ var 𝒾 ⟧                     `δ δ γ = lookup⊩ γ 𝒾
  ⟦ mvar ψ 𝒾 ⟧                  `δ δ γ = mlookup⊩ (⟦ ψ ⟧⋆ `δ δ γ) (δ reflЯ) 𝒾
  ⟦ lam {A = A} {B} 𝒟 ⟧         `δ δ γ = return {A ⇒ B}
                                           λ θ a →
                                             ⟦ 𝒟 ⟧ (λ ζ → `δ (transЯ ζ (⊒→Я θ)))
                                                   (λ ζ → δ (transЯ ζ (⊒→Я θ)))
                                                   (mono⊩⋆ θ γ , a)
  ⟦ app {A = A} {B} 𝒟 ℰ ⟧       `δ δ γ = bind {A ⇒ B} {B} (⟦ 𝒟 ⟧ `δ δ γ)
                                           λ θ f →
                                             f refl⊒ (mono⊩ {A} θ (⟦ ℰ ⟧ `δ δ γ))
  ⟦ box {Ψ = Ψ} {A} 𝒟 ⟧         `δ δ γ = return {[ Ψ ] A}
                                           λ ζ →
                                             mgraft⊢ (`δ ζ) 𝒟 ,
                                             λ θ →
                                               ⟦ 𝒟 ⟧ (λ ζ′ → `δ (transЯ ζ′ (transЯ (⊒→Я θ) ζ)))
                                                     (λ ζ′ → δ (transЯ ζ′ (transЯ (⊒→Я θ) ζ)))
  ⟦ unbox {Ψ = Ψ} {A} {C} 𝒟 ℰ ⟧ `δ δ γ = bind {[ Ψ ] A} {C} (⟦ 𝒟 ⟧ `δ δ γ)
                                           λ θ q →
                                             ⟦ ℰ ⟧ (λ ζ → `δ (transЯ ζ (⊒→Я θ)) , box (π₁ (q ζ)))
                                                   (λ ζ → δ (transЯ ζ (⊒→Я θ)) , π₂ (q ζ))
                                                   (mono⊩⋆ θ γ)

  ⟦_⟧⋆ : ∀ {Δ Γ Ξ} → Δ ⁏ Γ ⊢⋆ Ξ → Δ ⁏ Γ ⊨⋆ Ξ
  ⟦ ∅ ⟧⋆     `δ δ γ = ∅
  ⟦ ξ , 𝒟 ⟧⋆ `δ δ γ = ⟦ ξ ⟧⋆ `δ δ γ , ⟦ 𝒟 ⟧ `δ δ γ


-- Completeness.

instance
  canon : Model
  canon = record
    { World  = Cx
    ; _⊒_    = λ { (Δ′ ⁏ Γ′) (Δ ⁏ Γ) → Δ′ ⊇ Δ ∧ Γ′ ⊇ Γ }
    ; refl⊒  = refl⊇ , refl⊇
    ; trans⊒ = λ { (ζ′ , η′) (ζ , η) → trans⊇ ζ′ ζ , trans⊇ η′ η }
    ; _Я_    = λ { (Δ′ ⁏ Γ′) (Δ ⁏ Γ) → Δ′ ⊇ Δ }
    ; reflЯ  = refl⊇
    ; transЯ = trans⊇
    ; G      = _⊢ⁿᵉ •
    ; monoG  = λ { (ζ , η) 𝒟 → mono⊢ⁿᵉ ζ η 𝒟 }
    ; ⊒→Я   = π₁
    ; peek   = id
    }

postulate
  reverse : ∀ {ℓ} {X : Set ℓ} {Ξ Ξ′ : List X} → Ξ′ ⊇ Ξ → Ξ ⊇ Ξ′

mutual
  reifyᶜ : ∀ {A Δ Γ} → Δ ⁏ Γ ⊩ A → Δ ⁏ Γ ⊢ⁿᶠ A
  reifyᶜ {•}       κ = κ (refl⊇ , refl⊇)
                         λ θ a →
                           neⁿᶠ a
  reifyᶜ {A ⇒ B}  κ = κ (refl⊇ , refl⊇)
                         λ θ f →
                           lamⁿᶠ (reifyᶜ (f (refl⊇ , weak refl⊇) ⟦ varⁿᵉ zero ⟧ᶜ))
  reifyᶜ {[ Ψ ] A} κ = κ (refl⊇ , refl⊇)
                         λ {w″} θ q →
                           boxⁿᶠ (π₁ (q {w′ = w″} refl⊇))

  reify⋆ᶜ : ∀ {Ξ Δ Γ} → Δ ⁏ Γ ⊩⋆ Ξ → Δ ⁏ Γ ⊢⋆ⁿᶠ Ξ
  reify⋆ᶜ {∅}     ∅       = ∅
  reify⋆ᶜ {Ξ , A} (ξ , a) = reify⋆ᶜ ξ , reifyᶜ a

  ⟦_⟧ᶜ : ∀ {A Δ Γ} → Δ ⁏ Γ ⊢ⁿᵉ A → Δ ⁏ Γ ⊩ A
  ⟦_⟧ᶜ {•}       𝒟 = return {•} 𝒟
  ⟦_⟧ᶜ {A ⇒ B}  𝒟 = return {A ⇒ B}
                       λ { (ζ , η) a →
                         ⟦ appⁿᵉ (mono⊢ⁿᵉ ζ η 𝒟) (reifyᶜ a) ⟧ᶜ }
  ⟦_⟧ᶜ {[ Ψ ] A} 𝒟 = λ { (ζ , η) κ →
                       neⁿᶠ (unboxⁿᵉ (mono⊢ⁿᵉ ζ η 𝒟)
                                     (κ (weak refl⊇ , refl⊇)
                                        (λ ζ′ →
                                          mono⊢ ζ′ refl⊇ (mvar refl⊢⋆ zero) ,
                                          λ { (ζ″ , η′) ψ →
                                            ⟦ mono⊢ⁿᵉ (trans⊇ ζ″ ζ′) η′ (mvarⁿᵉ (mono⊢⋆ⁿᶠ (reverse (trans⊇ ζ″ ζ′)) (reverse η′) (reify⋆ᶜ ψ)) zero) ⟧ᶜ }))) }

refl⊩⋆ : ∀ {Δ Γ} → Δ ⁏ Γ ⊩⋆ Γ
refl⊩⋆ {Γ = ∅}     = ∅
refl⊩⋆ {Γ = Γ , A} = mono⊩⋆ (refl⊇ , weak refl⊇) refl⊩⋆ , ⟦ varⁿᵉ zero ⟧ᶜ

mrefl⊩⧆ : ∀ {Δ Γ} → Δ ⁏ Γ ⊩⧆ Δ
mrefl⊩⧆ {∅}           = ∅
mrefl⊩⧆ {Δ , [ Ψ ] A} = mono⊩⧆ (weak refl⊇ , refl⊇) mrefl⊩⧆ ,
                          λ { (ζ , η) ψ →
                            ⟦ mono⊢ⁿᵉ ζ η (mvarⁿᵉ (mono⊢⋆ⁿᶠ (reverse ζ) (reverse η) (reify⋆ᶜ ψ)) zero) ⟧ᶜ }

reify : ∀ {Δ Γ A} → Δ ⁏ Γ ⊨ A → Δ ⁏ Γ ⊢ⁿᶠ A
reify 𝔞 = reifyᶜ (𝔞 (λ ζ → mono⊢⧆ ζ refl⊇ mrefl⊢⧆)
                    (λ ζ → mono⊩⧆ (ζ , refl⊇) mrefl⊩⧆)
                    refl⊩⋆)


-- Normalisation.

nbe : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A → Δ ⁏ Γ ⊢ⁿᶠ A
nbe = reify ∘ ⟦_⟧
