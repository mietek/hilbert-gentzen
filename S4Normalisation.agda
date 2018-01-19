module S4Normalisation where

open import Prelude
open import Category
open import List
open List²
open import ListLemmas
open import AllList
open import S4Propositions
open import S4Derivations
open import S4BidirectionalDerivationsForNormalisation


--------------------------------------------------------------------------------


record Model : Set₁
  where
    field
      World : Set

      -- TODO: Better name
      Ground : World → Set

      _≥_ : World → World → Set

      id≥ : ∀ {W} → W ≥ W

      _∘≥_ : ∀ {W W′ W″} → W′ ≥ W → W″ ≥ W′
                         → W″ ≥ W

      relG : ∀ {W W′} → W′ ≥ W → Ground W
                      → Ground W′

      ⌊_⌋ : World → List² Prop Prop

      ⌊_⌋≥ : ∀ {W W′} → W′ ≥ W
                      → ⌊ W′ ⌋ ⊇² ⌊ W ⌋

open Model {{...}}


--------------------------------------------------------------------------------


⌊_⌋₁ : ∀ {{_ : Model}} → World → List Prop
⌊ W ⌋₁ = proj₁ ⌊ W ⌋


⌊_⌋₂ : ∀ {{_ : Model}} → World → List Prop
⌊ W ⌋₂ = proj₂ ⌊ W ⌋


⌊_⌋≥₁ : ∀ {{_ : Model}} {W W′} → W′ ≥ W
                               → ⌊ W′ ⌋₁ ⊇ ⌊ W ⌋₁
⌊ η ⌋≥₁ = proj₁ ⌊ η ⌋≥


⌊_⌋≥₂ : ∀ {{_ : Model}} {W W′} → W′ ≥ W
                               → ⌊ W′ ⌋₂ ⊇ ⌊ W ⌋₂
⌊ η ⌋≥₂ = proj₂ ⌊ η ⌋≥


--------------------------------------------------------------------------------


mutual
  infix 3 _⊩_value
  _⊩_value : ∀ {{_ : Model}} → World → Prop → Set
  W ⊩ BASE value  = Ground W
  W ⊩ A ⊃ B value = ∀ {W′} → W′ ≥ W → W′ ⊩ A thunk
                            → W′ ⊩ B thunk
  W ⊩ □ A value   = W ⊩ A chunk

  infix 3 _⊩_thunk
  _⊩_thunk : ∀ {{_ : Model}} → World → Prop → Set
  W ⊩ A thunk = ∀ {B W′} → W′ ≥ W → (∀ {W″} → W″ ≥ W′ → W″ ⊩ A value
                                               → ⌊ W″ ⌋₁ ⨾ ⌊ W″ ⌋₂ ⊢ B verifiable)
                          → ⌊ W′ ⌋₁ ⨾ ⌊ W′ ⌋₂ ⊢ B verifiable

  infix 3 _⊩_chunk
  _⊩_chunk : ∀ {{_ : Model}} → World → Prop → Set
  W ⊩ A chunk = ⌊ W ⌋₁ ⊢ A valid × W ⊩ A thunk


infix 3 _⊩_thunk*
_⊩_thunk* : ∀ {{_ : Model}} → World → List Prop → Set
W ⊩ Γ thunk* = All (W ⊩_thunk) Γ


infix 3 _⊩_chunk*
_⊩_chunk* : ∀ {{_ : Model}} → World → List Prop → Set
W ⊩ Δ chunk* = All (W ⊩_chunk) Δ


--------------------------------------------------------------------------------


syn : ∀ {{_ : Model}} {A W} → W ⊩ A chunk
                            → ⌊ W ⌋₁ ⊢ A valid
syn v = proj₁ v


syns : ∀ {{_ : Model}} {Δ W} → W ⊩ Δ chunk*
                             → ⌊ W ⌋₁ ⊢ Δ valid*
syns δ = maps syn δ


sem : ∀ {{_ : Model}} {A W} → W ⊩ A chunk
                            → W ⊩ A thunk
sem v = proj₂ v


--------------------------------------------------------------------------------


mutual
  rel : ∀ {{_ : Model}} {A W W′} → W′ ≥ W → W ⊩ A value
                                 → W′ ⊩ A value
  rel {BASE}  η 𝒟 = relG η 𝒟
  rel {A ⊃ B} η f = \ η′ k → f (η ∘≥ η′) k
  rel {□ A}   η v = relₖ₁ η v

  relₖ : ∀ {{_ : Model}} {A W W′} → W′ ≥ W → W ⊩ A thunk
                                  → W′ ⊩ A thunk
  relₖ η k = \ η′ f → k (η ∘≥ η′) f

  relₖ₁ : ∀ {{_ : Model}} {A W W′} → W′ ≥ W → W ⊩ A chunk
                                   → W′ ⊩ A chunk
  relₖ₁ {A} η v = mren ⌊ η ⌋≥₁ (syn v) , relₖ {A} η (sem v)


relsₖ : ∀ {{_ : Model}} {Γ W W′} → W′ ≥ W → W ⊩ Γ thunk*
                                 → W′ ⊩ Γ thunk*
relsₖ η γ = maps (\ {A} k {B} {W′} → relₖ {A} η (\ {C} {W″} → k {C} {W″})) γ
-- NOTE: Pattern-matching problem here prevents rel from taking “A true”
-- NOTE: Equivalent to
-- relsₖ η γ = maps (relₖ η) γ


relsₖ₁ : ∀ {{_ : Model}} {Δ W W′} → W′ ≥ W → W ⊩ Δ chunk*
                                  → W′ ⊩ Δ chunk*
relsₖ₁ η δ = maps (relₖ₁ η) δ


--------------------------------------------------------------------------------


return : ∀ {{_ : Model}} {A W} → W ⊩ A value
                               → W ⊩ A thunk
return {A} a = \ η f → f id≥ (rel {A} η a)


bind : ∀ {{_ : Model}} {A B W} → W ⊩ A thunk → (∀ {W′} → W′ ≥ W → W′ ⊩ A value
                                                          → W′ ⊩ B thunk)
                               → W ⊩ B thunk
bind k f = \ η f′ →
             k η (\ η′ a →
               f (η ∘≥ η′) a id≥ (\ η″ b →
                 f′ (η′ ∘≥ η″) b))


--------------------------------------------------------------------------------


infix 3 _⊨_true
_⊨_true : List² Prop Prop → Prop → Set₁
Δ ⨾ Γ ⊨ A true = ∀ {{_ : Model}} {W} → W ⊩ Δ chunk* → W ⊩ Γ thunk*
                                      → W ⊩ A thunk


↓ : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ A true
              → Δ ⨾ Γ ⊨ A true
↓ (var i)              δ γ = get γ i
↓ (lam {A} {B} 𝒟)      δ γ = return {A ⊃ B} (\ η k →
                               ↓ 𝒟 (relsₖ₁ η δ) (relsₖ η γ , k))
↓ (app {A} {B} 𝒟 ℰ)    δ γ = bind {A ⊃ B} {B} (↓ 𝒟 δ γ) (\ η f →
                               f id≥ (↓ ℰ (relsₖ₁ η δ) (relsₖ η γ)))
↓ (mvar i)             δ γ = sem (get δ i)
↓ (box {A} 𝒟)          δ γ = return {□ A} (msub (syns δ) 𝒟 , ↓ 𝒟 δ ∙)
↓ (letbox {A} {B} 𝒟 ℰ) δ γ = bind {□ A} {B} (↓ 𝒟 δ γ) (\ η v →
                               ↓ ℰ (relsₖ₁ η δ , v) (relsₖ η γ))


--------------------------------------------------------------------------------


renᵣ² : ∀ {Δ Δ′ Γ Γ′ A} → Δ′ ⨾ Γ′ ⊇² Δ ⨾ Γ → Δ ⨾ Γ ⊢ A usable
                        → Δ′ ⨾ Γ′ ⊢ A usable
renᵣ² η 𝒟 = mrenᵣ (proj₁ η) (renᵣ (proj₂ η) 𝒟)


instance
  canon : Model
  canon = record
            { World  = List² Prop Prop
            ; Ground = \ { (Δ ⨾ Γ) → Δ ⨾ Γ ⊢ BASE usable }
            ; _≥_    = _⊇²_
            ; id≥    = id
            ; _∘≥_   = _∘_
            ; relG   = renᵣ²
            ; ⌊_⌋    = id
            ; ⌊_⌋≥   = id
            }


mutual
  ⇓ : ∀ {A Δ Γ} → Δ ⨾ Γ ⊢ A usable
                → Δ ⨾ Γ ⊩ A thunk
  ⇓ {BASE}  𝒟 = return {BASE} 𝒟
  ⇓ {A ⊃ B} 𝒟 = return {A ⊃ B} (\ η k → ⇓ (app (renᵣ² η 𝒟) (⇑ k)))
  ⇓ {□ A}   𝒟 = \ η f → letbox (renᵣ² η 𝒟) (f (drop₁ id) (mvz , ⇓ mvzᵣ))

  ⇑ : ∀ {A Δ Γ} → Δ ⨾ Γ ⊩ A thunk
                → Δ ⨾ Γ ⊢ A verifiable
  ⇑ {BASE}  k = k id (\ η 𝒟 → use 𝒟)
  ⇑ {A ⊃ B} k = k id (\ η f → lam (⇑ (f (drop₂ id) (⇓ vzᵣ))))
  ⇑ {□ A}   k = k id (\ η v → box (syn v))


--------------------------------------------------------------------------------


wksₛ : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊩ Ξ thunk*
                   → Δ ⨾ Γ , A ⊩ Ξ thunk*
wksₛ ξ = relsₖ (drop₂ id) ξ


liftsₛ : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊩ Ξ thunk*
                     → Δ ⨾ Γ , A ⊩ Ξ , A thunk*
liftsₛ ξ = wksₛ ξ , ⇓ vzᵣ


varsₛ : ∀ {Δ Γ Γ′} → Γ′ ⊇ Γ
                   → Δ ⨾ Γ′ ⊩ Γ thunk*
varsₛ done     = ∙
varsₛ (drop η) = wksₛ (varsₛ η)
varsₛ (keep η) = liftsₛ (varsₛ η)


idsₛ : ∀ {Δ Γ} → Δ ⨾ Γ ⊩ Γ thunk*
idsₛ = varsₛ id


--------------------------------------------------------------------------------


mwksₛ₁ : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊩ Ξ chunk*
                     → Δ , A ⨾ Γ ⊩ Ξ chunk*
mwksₛ₁ ξ = relsₖ₁ (drop₁ id) ξ


mliftsₛ₁ : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊩ Ξ chunk*
                       → Δ , A ⨾ Γ ⊩ Ξ , A chunk*
mliftsₛ₁ ξ = mwksₛ₁ ξ , (mvz , ⇓ mvzᵣ)


mvarsₛ₁ : ∀ {Δ Δ′ Γ} → Δ′ ⊇ Δ
                     → Δ′ ⨾ Γ ⊩ Δ chunk*
mvarsₛ₁ done     = ∙
mvarsₛ₁ (drop η) = mwksₛ₁ (mvarsₛ₁ η)
mvarsₛ₁ (keep η) = mliftsₛ₁ (mvarsₛ₁ η)


midsₛ₁ : ∀ {Δ Γ} → Δ ⨾ Γ ⊩ Δ chunk*
midsₛ₁ = mvarsₛ₁ id


--------------------------------------------------------------------------------


↑ : ∀ {Δ Γ A} → Δ ⨾ Γ ⊨ A true
              → Δ ⨾ Γ ⊢ A verifiable
↑ f = ⇑ (f midsₛ₁ idsₛ)


nbe : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ A true
                → Δ ⨾ Γ ⊢ A verifiable
nbe 𝒟 = ↑ (↓ 𝒟)


--------------------------------------------------------------------------------
