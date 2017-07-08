module IS4NormalisationNoTerms where

open import IS4SemanticsNoTerms public


-- Absolute values.

infix 3 _⊨_
_⊨_ : Cx → Ty → Set₁
Δ ⁏ Γ ⊨ A = ∀ {{_ : Model}} {w} →
               (∀ {w′} → w′ Я w → w′ [⊩₁]⋆ Δ) →
               (∀ {w′} → w′ Я w → w′ [⊩₂]⋆ Δ) →
               w ⊩⋆ Γ →
               w ⊩ A


-- Soundness.

⟦_⟧ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A → Δ ⁏ Γ ⊨ A
⟦ var 𝒾 ⟧                 δ₁ δ₂ γ = lookup⊩ γ 𝒾
⟦ mvar 𝒾 ⟧                δ₁ δ₂ γ = mlookup[⊩₂] (δ₂ reflЯ) 𝒾
⟦ lam {A = A} {B} 𝒟 ⟧     δ₁ δ₂ γ = return {A ⇒ B}
                                      λ θ a →
                                        ⟦ 𝒟 ⟧ (λ ζ → δ₁ (transЯ ζ (⊒→Я θ)))
                                              (λ ζ → δ₂ (transЯ ζ (⊒→Я θ)))
                                              (mono⊩⋆ θ γ , a)
⟦ app {A = A} {B} 𝒟 ℰ ⟧   δ₁ δ₂ γ = bind {A ⇒ B} {B} (⟦ 𝒟 ⟧ δ₁ δ₂ γ)
                                      λ θ f →
                                        f refl⊒ (mono⊩ {A} θ (⟦ ℰ ⟧ δ₁ δ₂ γ))
⟦ box {A = A} 𝒟 ⟧         δ₁ δ₂ γ = return {□ A}
                                      λ ζ →
                                        mgraft⊢ (δ₁ ζ) 𝒟 ,
                                        ⟦ 𝒟 ⟧ (λ ζ′ → δ₁ (transЯ ζ′ ζ))
                                              (λ ζ′ → δ₂ (transЯ ζ′ ζ))
                                              ∅
⟦ unbox {A = A} {C} 𝒟 ℰ ⟧ δ₁ δ₂ γ = bind {□ A} {C} (⟦ 𝒟 ⟧ δ₁ δ₂ γ)
                                      λ θ q →
                                        ⟦ ℰ ⟧ (λ ζ → δ₁ (transЯ ζ (⊒→Я θ)) , π₁ (q ζ))
                                              (λ ζ → δ₂ (transЯ ζ (⊒→Я θ)) , π₂ (q ζ))
                                              (mono⊩⋆ θ γ)


-- Canonical model.

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

mutual
  reifyᶜ : ∀ {A Δ Γ} → Δ ⁏ Γ ⊩ A → Δ ⁏ Γ ⊢ⁿᶠ A
  reifyᶜ {•}      κ = κ (refl⊇ , refl⊇)
                        λ θ a →
                          neⁿᶠ a
  reifyᶜ {A ⇒ B} κ = κ (refl⊇ , refl⊇)
                        λ θ f →
                          lamⁿᶠ (reifyᶜ (f (refl⊇ , weak refl⊇) ⟦ varⁿᵉ zero ⟧ᶜ))
  reifyᶜ {□ A}    κ = κ (refl⊇ , refl⊇)
                        λ {w″} θ q →
                          boxⁿᶠ (π₁ (q {w′ = w″} refl⊇))

  ⟦_⟧ᶜ : ∀ {A Δ Γ} → Δ ⁏ Γ ⊢ⁿᵉ A → Δ ⁏ Γ ⊩ A
  ⟦_⟧ᶜ {•}      𝒟 = return {•} 𝒟
  ⟦_⟧ᶜ {A ⇒ B} 𝒟 = return {A ⇒ B}
                      λ { (ζ , η) a →
                        ⟦ appⁿᵉ (mono⊢ⁿᵉ ζ η 𝒟) (reifyᶜ a) ⟧ᶜ }
  ⟦_⟧ᶜ {□ A}    𝒟 = λ { (ζ , η) κ →
                      neⁿᶠ (unboxⁿᵉ (mono⊢ⁿᵉ ζ η 𝒟)
                                    (κ (weak refl⊇ , refl⊇)
                                       λ ζ′ →
                                         mono⊢ ζ′ refl⊇ (mvar zero) ,
                                         ⟦ mono⊢ⁿᵉ ζ′ refl⊇ (mvarⁿᵉ zero) ⟧ᶜ)) }

-- Lists of values, continued.

refl⊩⋆ : ∀ {Δ Γ} → Δ ⁏ Γ ⊩⋆ Γ
refl⊩⋆ {Γ = ∅}     = ∅
refl⊩⋆ {Γ = Γ , A} = mono⊩⋆ (refl⊇ , weak refl⊇) refl⊩⋆ , ⟦ varⁿᵉ zero ⟧ᶜ


-- TODO: Needs a name, continued.

mono[⊩₁] : ∀ {w w′ A} → w′ ⊒ w → w [⊩₁] □ A → w′ [⊩₁] □ A
mono[⊩₁] (ζ , η) 𝒟 = mono[⊢] ζ η 𝒟

mono[⊩₁]⋆ : ∀ {w w′ Ξ} → w′ ⊒ w → w [⊩₁]⋆ Ξ → w′ [⊩₁]⋆ Ξ
mono[⊩₁]⋆ (ζ , η) ξ = mono[⊢]⋆ ζ η ξ

mrefl[⊩₁]⋆ : ∀ {w} → w [⊩₁]⋆ π₁ w
mrefl[⊩₁]⋆ {w} = mrefl[⊢]⋆ {Γ = π₂ w}


-- TODO: Needs a name, continued.

mono[⊩₂] : ∀ {A w w′} → w′ ⊒ w → w [⊩₂] □ A → w′ [⊩₂] □ A
mono[⊩₂] {A} θ q = mono⊩ {A} θ q

mono[⊩₂]⋆ : ∀ {Ξ w w′} → w′ ⊒ w → w [⊩₂]⋆ Ξ → w′ [⊩₂]⋆ Ξ
mono[⊩₂]⋆ {∅}       θ ∅       = ∅
mono[⊩₂]⋆ {Ξ , □ A} θ (ξ , q) = mono[⊩₂]⋆ θ ξ , mono[⊩₂] {A} θ q
-- TODO: Equivalent using mapAll?

mrefl[⊩₂]⋆ : ∀ {w} → w [⊩₂]⋆ π₁ w
mrefl[⊩₂]⋆ {∅       ⁏ Γ} = ∅
mrefl[⊩₂]⋆ {Δ , □ A ⁏ Γ} = mono[⊩₂]⋆ (weak refl⊇ , refl⊇) mrefl[⊩₂]⋆ ,
                            ⟦ mvarⁿᵉ zero ⟧ᶜ


-- Completeness.

reify : ∀ {Δ Γ A} → Δ ⁏ Γ ⊨ A → Δ ⁏ Γ ⊢ⁿᶠ A
reify 𝔞 = reifyᶜ (𝔞 (λ { {_ ⁏ Γ°} ζ →
                       mono[⊩₁]⋆ {w = _ ⁏ Γ°} (ζ , refl⊇) (mrefl[⊩₁]⋆ {w = _ ⁏ Γ°}) })
                    (λ ζ →
                      mono[⊩₂]⋆ (ζ , refl⊇) mrefl[⊩₂]⋆)
                    refl⊩⋆)


-- Normalisation.

nbe : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A → Δ ⁏ Γ ⊢ⁿᶠ A
nbe = reify ∘ ⟦_⟧
