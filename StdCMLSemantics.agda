module StdCMLSemantics where

open import Prelude
open import List
open import StdCML
open import StdCMLNormalForms


--------------------------------------------------------------------------------


record Model : Set₁
  where
    field
      World : Set

      Ground : World → Set

      _≥_ : World → World → Set

      id≥ : ∀ {W} → W ≥ W

      _∘≥_ : ∀ {W W′ W″} → W′ ≥ W → W″ ≥ W′
                         → W″ ≥ W

      relG : ∀ {W W′} → W′ ≥ W → Ground W
                      → Ground W′

      ⌊_⌋ : World → Context

      ⌊_⌋≥ : ∀ {W W′} → W′ ≥ W
                      → ⌊ W′ ⌋ ⊇² ⌊ W ⌋

open Model {{...}}


--------------------------------------------------------------------------------


⌊_⌋₁ : ∀ {{_ : Model}} → World → List Validity
⌊ W ⌋₁ = Context.Δ ⌊ W ⌋


⌊_⌋≥₁ : ∀ {{_ : Model}} {W W′} → W′ ≥ W
                               → ⌊ W′ ⌋₁ ⊇ ⌊ W ⌋₁
⌊ η ⌋≥₁ = proj₁ ⌊ η ⌋≥


--------------------------------------------------------------------------------


mutual
  infix 3 _⊩_
  _⊩_ : ∀ {{_ : Model}} → World → Truth → Set
  W ⊩ BASE true    = Ground W
  W ⊩ A ⊃ B true   = ∀ {W′} → W′ ≥ W → W′ ⊪ A true
                             → W′ ⊪ B true
  W ⊩ [ Ψ ] A true = ∀ {W′} → W′ ≥ W → W′ ⊪₁ A valid[ Ψ ]

  infix 3 _⊪_
  _⊪_ : ∀ {{_ : Model}} → World → Truth → Set
  W ⊪ A true = ∀ {B W′} → W′ ≥ W → (∀ {W″} → W″ ≥ W′ → W″ ⊩ A true
                                              → ⌊ W″ ⌋ ⊢ₙₘ B)
                         → ⌊ W′ ⌋ ⊢ₙₘ B

  infix 3 _⊪₁_
  _⊪₁_ : ∀ {{_ : Model}} → World → Validity → Set
  W ⊪₁ A valid[ Ψ ] = ⌊ W ⌋₁ ⊢₁ A valid[ Ψ ] × (∀ {W′} → W′ ≥ W → W′ ⊪⋆ Ψ
                                                         → W′ ⊪ A true)

  infix 3 _⊪⋆_
  _⊪⋆_ : ∀ {{_ : Model}} → World → List Truth → Set
  W ⊪⋆ ∙          = ⊤
  W ⊪⋆ Γ , A true = W ⊪⋆ Γ × W ⊪ A true
  -- NOTE: Equivalent to
  -- W ⊪⋆ Γ = All (W ⊪_) Γ


clookup : ∀ {{_ : Model}} {Γ A W} → W ⊪⋆ Γ → Γ ∋ A true
                                  → W ⊪ A true
clookup {Γ , A true} (γ , a) zero    = a
clookup {Γ , B true} (γ , b) (suc 𝒾) = clookup γ 𝒾
-- NOTE: Equivalent to lookup


syn : ∀ {{_ : Model}} {A Ψ W} → W ⊪₁ A valid[ Ψ ]
                              → ⌊ W ⌋₁ ⊢₁ A valid[ Ψ ]
syn v = proj₁ v


sem : ∀ {{_ : Model}} {A Ψ W} → W ⊪₁ A valid[ Ψ ]
                              → (∀ {W′} → W′ ≥ W → W′ ⊪⋆ Ψ
                                         → W′ ⊪ A true)
sem v = proj₂ v


--------------------------------------------------------------------------------


mutual
  rel : ∀ {{_ : Model}} {Aₜ W W′} → W′ ≥ W → W ⊩ Aₜ
                                  → W′ ⊩ Aₜ
  rel {BASE true}    η 𝒟 = relG η 𝒟
  rel {A ⊃ B true}   η f = \ η′ k → f (η ∘≥ η′) k
  rel {[ Ψ ] A true} η f = \ η′ → crel₁ (η ∘≥ η′) (f id≥)

  crel : ∀ {{_ : Model}} {Aₜ W W′} → W′ ≥ W → W ⊪ Aₜ
                                   → W′ ⊪ Aₜ
  crel η k = \ η′ f → k (η ∘≥ η′) f

  crel₁ : ∀ {{_ : Model}} {Aᵥ W W′} → W′ ≥ W → W ⊪₁ Aᵥ
                                    → W′ ⊪₁ Aᵥ
  crel₁ {A valid[ Ψ ]} η v = mren ⌊ η ⌋≥₁ (syn v) ,
                             \ η′ ψ → crel {A true} id≥ (sem v (η ∘≥ η′) ψ)

  crels : ∀ {{_ : Model}} {Γ W W′} → W′ ≥ W → W ⊪⋆ Γ
                                   → W′ ⊪⋆ Γ
  crels {∙}          η tt      = tt
  crels {Γ , A true} η (γ , a) = crels η γ , crel {A true} η a
  -- NOTE: Equivalent to
  -- crels η γ = mapAll (crel η) γ


--------------------------------------------------------------------------------


infix 3 _⊪⋆₁_
_⊪⋆₁_ : ∀ {{_ : Model}} → World → List Validity → Set
W ⊪⋆₁ Δ = All (W ⊪₁_) Δ


syns : ∀ {{_ : Model}} {Δ W} → W ⊪⋆₁ Δ
                             → ⌊ W ⌋₁ ⊢⋆₁ Δ
syns δ = mapAll syn δ


--------------------------------------------------------------------------------


crels₁ : ∀ {{_ : Model}} {Δ W W′} → W′ ≥ W → W ⊪⋆₁ Δ
                                  → W′ ⊪⋆₁ Δ
crels₁ η δ = mapAll (crel₁ η) δ


--------------------------------------------------------------------------------


return : ∀ {{_ : Model}} {A W} → W ⊩ A true
                               → W ⊪ A true
return {A} a = \ η f → f id≥ (rel {A true} η a)

bind : ∀ {{_ : Model}} {A B W} → W ⊪ A true → (∀ {W′} → W′ ≥ W → W′ ⊩ A true
                                                         → W′ ⊪ B true)
                               → W ⊪ B true
bind k f = \ η f′ →
             k η (\ η′ a →
               f (η ∘≥ η′) a id≥ (\ η″ b →
                 f′ (η′ ∘≥ η″) b))


--------------------------------------------------------------------------------


infix 3 _⊨_
_⊨_ : Context → Truth → Set₁
Δ ⨾ Γ ⊨ A true = ∀ {{_ : Model}} {W} → W ⊪⋆₁ Δ → W ⊪⋆ Γ
                                      → W ⊪ A true

infix 3 _⊨⋆_
_⊨⋆_ : Context → List Truth → Set₁
Δ ⨾ Γ ⊨⋆ Ξ = ∀ {{_ : Model}} {W} → W ⊪⋆₁ Δ → W ⊪⋆ Γ
                                  → W ⊪⋆ Ξ


mutual
  ↓ : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ A true
                → Δ ⨾ Γ ⊨ A true
  ↓ (var 𝒾)                  δ γ = clookup γ 𝒾
  ↓ (lam {A} {B} 𝒟)          δ γ = return {A ⊃ B} (\ η k →
                                     ↓ 𝒟 (crels₁ η δ) (crels η γ , k))
  ↓ (app {A} {B} 𝒟 ℰ)        δ γ = bind {A ⊃ B} {B} (↓ 𝒟 δ γ) (\ η f →
                                     f id≥ (↓ ℰ (crels₁ η δ) (crels η γ)))
  ↓ (mvar 𝒾 ψ)               δ γ = sem (lookup δ 𝒾) id≥ (↓⋆ ψ δ γ)
  ↓ (box {A} {Ψ} 𝒟)          δ γ = return {[ Ψ ] A} (\ η →
                                     msub (syns (crels₁ η δ)) 𝒟 ,
                                     \ η′ ψ → ↓ 𝒟 (crels₁ (η ∘≥ η′) δ) ψ)
  ↓ (letbox {A} {B} {Ψ} 𝒟 ℰ) δ γ = bind {[ Ψ ] A} {B} (↓ 𝒟 δ γ) (\ η f →
                                     ↓ ℰ (crels₁ η δ , f id≥) (crels η γ))

  ↓⋆ : ∀ {Ξ Δ Γ} → Δ ⨾ Γ ⊢⋆ Ξ
                 → Δ ⨾ Γ ⊨⋆ Ξ
  ↓⋆ ∙       δ γ = tt
  ↓⋆ (ξ , 𝒟) δ γ = ↓⋆ ξ δ γ , ↓ 𝒟 δ γ


--------------------------------------------------------------------------------


instance
  canon : Model
  canon = record
            { World  = Context
            ; Ground = _⊢ₙₜ BASE true
            ; _≥_    = _⊇²_
            ; id≥    = id⊇²
            ; _∘≥_   = _∘⊇²_
            ; relG   = renₙₜ²
            ; ⌊_⌋    = id
            ; ⌊_⌋≥   = id
            }


xmvz : ∀ {A Ψ Δ Δ′ Γ} → Δ′ ⊇ Δ , A valid[ Ψ ] → Δ′ ⨾ Γ ⊢⋆ Ψ
                      → Δ′ ⨾ Γ ⊢ A true
xmvz η ψ = mvar (ren∋ η zero) ψ


xmvzₙₜ : ∀ {A Ψ Δ Δ′ Γ} → Δ′ ⊇ Δ , A valid[ Ψ ] → Δ′ ⨾ Γ ⊢⋆ₙₘ Ψ
                        → Δ′ ⨾ Γ ⊢ₙₜ A true
xmvzₙₜ η ψ = mvar (ren∋ η zero) ψ


mutual
  ⇓ : ∀ {A Δ Γ} → Δ ⨾ Γ ⊢ₙₜ A true
                → Δ ⨾ Γ ⊪ A true
  ⇓ {BASE}    𝒟 = return {BASE} 𝒟
  ⇓ {A ⊃ B}   𝒟 = return {A ⊃ B} (\ η k → ⇓ (app (renₙₜ² η 𝒟) (⇑ k)))
  ⇓ {[ Ψ ] A} 𝒟 = \ η f → letbox (renₙₜ² η 𝒟) (f (mdrop⊇² id⊇²) (\ η′ →
                    xmvz (proj₁ η′) ids ,
                    \ η″ ψ → ⇓ (xmvzₙₜ (proj₁ (η′ ∘⊇² η″)) (⇑⋆ ψ))))

  ⇑ : ∀ {A Δ Γ} → Δ ⨾ Γ ⊪ A true
                → Δ ⨾ Γ ⊢ₙₘ A true
  ⇑ {BASE}    k = k id⊇² (\ η 𝒟 → nt 𝒟)
  ⇑ {A ⊃ B}   k = k id⊇² (\ η f → lam (⇑ (f (drop⊇² id⊇²) (⇓ vzₙₜ))))
  ⇑ {[ Ψ ] A} k = k id⊇² (\ η f → box (syn (f id⊇²)))

  ⇑⋆ : ∀ {Ξ Δ Γ} → Δ ⨾ Γ ⊪⋆ Ξ
                 → Δ ⨾ Γ ⊢⋆ₙₘ Ξ
  ⇑⋆ {∙}          tt      = ∙
  ⇑⋆ {Ξ , A true} (ξ , a) = ⇑⋆ ξ , ⇑ a


--------------------------------------------------------------------------------


swk : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊪ A true
                  → Δ ⨾ Γ , B true ⊪ A true
swk {A} k = crel {A true} (drop⊇² id⊇²) k


svz : ∀ {A Δ Γ} → Δ ⨾ Γ , A true ⊪ A true
svz = ⇓ vzₙₜ


--------------------------------------------------------------------------------


smwk : ∀ {A B Ψ Δ Γ} → Δ ⨾ Γ ⊪ A true
                     → Δ , B valid[ Ψ ] ⨾ Γ ⊪ A true
smwk {A} k = crel {A true} (mdrop⊇² id⊇²) k


smvz : ∀ {A Ψ Δ Γ} → Δ ⨾ Γ ⊢⋆ₙₘ Ψ
                   → Δ , A valid[ Ψ ] ⨾ Γ ⊪ A true
smvz ψ = ⇓ (mvzₙₜ ψ)


--------------------------------------------------------------------------------


swks : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊪⋆ Ξ
                   → Δ ⨾ Γ , A true ⊪⋆ Ξ
swks ξ = crels (drop⊇² id⊇²) ξ


slifts : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊪⋆ Ξ
                     → Δ ⨾ Γ , A true ⊪⋆ Ξ , A true
slifts ξ = swks ξ , svz


sids : ∀ {Γ Δ} → Δ ⨾ Γ ⊪⋆ Γ
sids {∙}          = tt
sids {Γ , A true} = slifts sids


--------------------------------------------------------------------------------


smwks : ∀ {A Ψ Δ Γ Ξ} → Δ ⨾ Γ ⊪⋆ Ξ
                      → Δ , A valid[ Ψ ] ⨾ Γ ⊪⋆ Ξ
smwks ξ = crels (mdrop⊇² id⊇²) ξ


--------------------------------------------------------------------------------


smwks₁ : ∀ {A Ψ Δ Γ Ξ} → Δ ⨾ Γ ⊪⋆₁ Ξ
                       → Δ , A valid[ Ψ ] ⨾ Γ ⊪⋆₁ Ξ
smwks₁ ξ = crels₁ (mdrop⊇² id⊇²) ξ


smvz₁ : ∀ {A Ψ Δ Γ} → Δ , A valid[ Ψ ] ⨾ Γ ⊪₁ A valid[ Ψ ]
smvz₁ = mvz ids ,
        \ η ψ → ⇓ (xmvzₙₜ (proj₁ η) (⇑⋆ ψ))


smlifts₁ : ∀ {A Ψ Δ Γ Ξ} → Δ ⨾ Γ ⊪⋆₁ Ξ
                         → Δ , A valid[ Ψ ] ⨾ Γ ⊪⋆₁ Ξ , A valid[ Ψ ]
smlifts₁ ξ = smwks₁ ξ , smvz₁


smids₁ : ∀ {Δ Γ} → Δ ⨾ Γ ⊪⋆₁ Δ
smids₁ {∙}                = ∙
smids₁ {Δ , A valid[ Ψ ]} = smlifts₁ smids₁


--------------------------------------------------------------------------------


↑ : ∀ {Δ Γ A} → Δ ⨾ Γ ⊨ A true
              → Δ ⨾ Γ ⊢ₙₘ A true
↑ f = ⇑ (f smids₁ sids)


nbe : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ A true
                → Δ ⨾ Γ ⊢ₙₘ A true
nbe 𝒟 = ↑ (↓ 𝒟)


--------------------------------------------------------------------------------
