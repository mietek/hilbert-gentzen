module Alt1-S4Semantics where

open import Prelude
open import Category
open import List
open List²
open import ListLemmas
open import AllList
open import Alt1-S4
open import Alt1-S4NormalForms


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

      ⌊_⌋ : World → List² Validity Truth

      ⌊_⌋≥ : ∀ {W W′} → W′ ≥ W
                      → ⌊ W′ ⌋ ⊇² ⌊ W ⌋

open Model {{...}}


--------------------------------------------------------------------------------


⌊_⌋₁ : ∀ {{_ : Model}} → World → List Validity
⌊ W ⌋₁ = proj₁ ⌊ W ⌋


⌊_⌋₂ : ∀ {{_ : Model}} → World → List Truth
⌊ W ⌋₂ = proj₂ ⌊ W ⌋


⌊_⌋≥₁ : ∀ {{_ : Model}} {W W′} → W′ ≥ W
                               → ⌊ W′ ⌋₁ ⊇ ⌊ W ⌋₁
⌊ η ⌋≥₁ = proj₁ ⌊ η ⌋≥


⌊_⌋≥₂ : ∀ {{_ : Model}} {W W′} → W′ ≥ W
                               → ⌊ W′ ⌋₂ ⊇ ⌊ W ⌋₂
⌊ η ⌋≥₂ = proj₂ ⌊ η ⌋≥


--------------------------------------------------------------------------------


mutual
  infix 3 _⊩_
  _⊩_ : ∀ {{_ : Model}} → World → Truth → Set
  W ⊩ BASE true  = Ground W
  W ⊩ A ⊃ B true = ∀ {W′} → W′ ≥ W → W′ ⊪ A true
                           → W′ ⊪ B true
  W ⊩ □ A true   = W ⊪₁ A valid

  infix 3 _⊪_
  _⊪_ : ∀ {{_ : Model}} → World → Truth → Set
  W ⊪ A true = ∀ {B W′} → W′ ≥ W → (∀ {W″} → W″ ≥ W′ → W″ ⊩ A true
                                              → ⌊ W″ ⌋₁ ⨾ₙₘ ⌊ W″ ⌋₂ ⊢ₙₘ B)
                         → ⌊ W′ ⌋₁ ⨾ₙₘ ⌊ W′ ⌋₂ ⊢ₙₘ B

  infix 3 _⊪₁_
  _⊪₁_ : ∀ {{_ : Model}} → World → Validity → Set
  W ⊪₁ A valid = ⌊ W ⌋₁ ⊢₁ A valid × W ⊪ A true


syn : ∀ {{_ : Model}} {A W} → W ⊪₁ A valid
                            → ⌊ W ⌋₁ ⊢₁ A valid
syn v = proj₁ v


sem : ∀ {{_ : Model}} {A W} → W ⊪₁ A valid
                            → W ⊪ A true
sem v = proj₂ v


--------------------------------------------------------------------------------


mutual
  rel : ∀ {{_ : Model}} {Aₜ W W′} → W′ ≥ W → W ⊩ Aₜ
                                  → W′ ⊩ Aₜ
  rel {BASE true}  η 𝒟 = relG η 𝒟
  rel {A ⊃ B true} η f = \ η′ k → f (η ∘≥ η′) k
  rel {□ A true}   η v = crel₁ η v

  crel : ∀ {{_ : Model}} {Aₜ W W′} → W′ ≥ W → W ⊪ Aₜ
                                   → W′ ⊪ Aₜ
  crel η k = \ η′ f → k (η ∘≥ η′) f

  crel₁ : ∀ {{_ : Model}} {Aᵥ W W′} → W′ ≥ W → W ⊪₁ Aᵥ
                                    → W′ ⊪₁ Aᵥ
  crel₁ {A valid} η v = mren ⌊ η ⌋≥₁ (syn v) ,
                        crel {A true} η (sem v)


--------------------------------------------------------------------------------


infix 3 _⊪⋆_
_⊪⋆_ : ∀ {{_ : Model}} → World → List Truth → Set
W ⊪⋆ Γ = All (W ⊪_) Γ


infix 3 _⊪⋆₁_
_⊪⋆₁_ : ∀ {{_ : Model}} → World → List Validity → Set
W ⊪⋆₁ Δ = All (W ⊪₁_) Δ


syns : ∀ {{_ : Model}} {Δ W} → W ⊪⋆₁ Δ
                             → ⌊ W ⌋₁ ⊢⋆₁ Δ
syns δ = maps syn δ


--------------------------------------------------------------------------------


crels : ∀ {{_ : Model}} {Γ W W′} → W′ ≥ W → W ⊪⋆ Γ
                                 → W′ ⊪⋆ Γ
crels η γ = maps (\ {Aₜ} k {B} {W′} → crel {Aₜ} η (\ {C} {W″} → k {C} {W″})) γ
-- NOTE: Equivalent to
-- crels η γ = maps (crel η) γ


crels₁ : ∀ {{_ : Model}} {Δ W W′} → W′ ≥ W → W ⊪⋆₁ Δ
                                  → W′ ⊪⋆₁ Δ
crels₁ η δ = maps (crel₁ η) δ


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
_⊨_ : List² Validity Truth → Truth → Set₁
Δ ⁏ Γ ⊨ A true = ∀ {{_ : Model}} {W} → W ⊪⋆₁ Δ → W ⊪⋆ Γ
                                      → W ⊪ A true


↓ : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ A true
              → Δ ⁏ Γ ⊨ A true
↓ (var 𝒾)              δ γ = get γ 𝒾
↓ (lam {A} {B} 𝒟)      δ γ = return {A ⊃ B} (\ η k →
                               ↓ 𝒟 (crels₁ η δ) (crels η γ , k))
↓ (app {A} {B} 𝒟 ℰ)    δ γ = bind {A ⊃ B} {B} (↓ 𝒟 δ γ) (\ η f →
                               f id≥ (↓ ℰ (crels₁ η δ) (crels η γ)))
↓ (mvar 𝒾)             δ γ = sem (get δ 𝒾)
↓ (box {A} 𝒟)          δ γ = return {□ A} (msub (syns δ) 𝒟 , ↓ 𝒟 δ ∙)
↓ (letbox {A} {B} 𝒟 ℰ) δ γ = bind {□ A} {B} (↓ 𝒟 δ γ) (\ η v →
                               ↓ ℰ (crels₁ η δ , v) (crels η γ))


--------------------------------------------------------------------------------


instance
  canon : Model
  canon = record
            { World  = List² Validity Truth
            ; Ground = \ { (Δ ⁏ Γ) →  Δ ⨾ₙₜ Γ ⊢ₙₜ BASE true }
            ; _≥_    = _⊇²_
            ; id≥    = id
            ; _∘≥_   = _∘_
            ; relG   = renₙₜ²
            ; ⌊_⌋    = id
            ; ⌊_⌋≥   = id
            }


mutual
  ⇓ : ∀ {A Δ Γ} → Δ ⨾ₙₜ Γ ⊢ₙₜ A true
                → Δ ⁏ Γ ⊪ A true
  ⇓ {BASE}  𝒟 = return {BASE} 𝒟
  ⇓ {A ⊃ B} 𝒟 = return {A ⊃ B} (\ η k → ⇓ (app (renₙₜ² η 𝒟) (⇑ k)))
  ⇓ {□ A}   𝒟 = \ η f → letbox (renₙₜ² η 𝒟) (f (drop₁ id) (mvz , ⇓ mvzₙₜ))

  ⇑ : ∀ {A Δ Γ} → Δ ⁏ Γ ⊪ A true
                → Δ ⨾ₙₘ Γ ⊢ₙₘ A true
  ⇑ {BASE}  k = k id (\ η 𝒟 → nt 𝒟)
  ⇑ {A ⊃ B} k = k id (\ η f → lam (⇑ (f (drop₂ id) (⇓ vzₙₜ))))
  ⇑ {□ A}   k = k id (\ η v → box (syn v))


--------------------------------------------------------------------------------


swk : ∀ {A B Δ Γ} → Δ ⁏ Γ ⊪ A true
                  → Δ ⁏ Γ , B true ⊪ A true
swk {A} k = crel {A true} (drop₂ id) k


svz : ∀ {A Δ Γ} → Δ ⁏ Γ , A true ⊪ A true
svz = ⇓ vzₙₜ


--------------------------------------------------------------------------------


smwk : ∀ {A B Δ Γ} → Δ ⁏ Γ ⊪ A true
                   → Δ , B valid ⁏ Γ ⊪ A true
smwk {A} k = crel {A true} (drop₁ id) k


smvz : ∀ {A Δ Γ} → Δ , A valid ⁏ Γ ⊪ A true
smvz = ⇓ mvzₙₜ


--------------------------------------------------------------------------------


swks : ∀ {A Δ Γ Ξ} → Δ ⁏ Γ ⊪⋆ Ξ
                   → Δ ⁏ Γ , A true ⊪⋆ Ξ
swks ξ = crels (drop₂ id) ξ


slifts : ∀ {A Δ Γ Ξ} → Δ ⁏ Γ ⊪⋆ Ξ
                     → Δ ⁏ Γ , A true ⊪⋆ Ξ , A true
slifts ξ = swks ξ , svz


svars : ∀ {Δ Γ Γ′} → Γ′ ⊇ Γ
                   → Δ ⁏ Γ′ ⊪⋆ Γ
svars done     = ∙
svars (drop η) = swks (svars η)
svars (keep η) = slifts (svars η)


sids : ∀ {Δ Γ} → Δ ⁏ Γ ⊪⋆ Γ
sids = svars id⊇


--------------------------------------------------------------------------------


smwks : ∀ {A Δ Γ Ξ} → Δ ⁏ Γ ⊪⋆ Ξ
                    → Δ , A valid ⁏ Γ ⊪⋆ Ξ
smwks ξ = crels (drop₁ id) ξ


--------------------------------------------------------------------------------


smwks₁ : ∀ {A Δ Γ Ξ} → Δ ⁏ Γ ⊪⋆₁ Ξ
                     → Δ , A valid ⁏ Γ ⊪⋆₁ Ξ
smwks₁ ξ = crels₁ (drop₁ id) ξ


smvz₁ : ∀ {A Δ Γ} → Δ , A valid ⁏ Γ ⊪₁ A valid
smvz₁ = mvz , smvz


smlifts₁ : ∀ {A Δ Γ Ξ} → Δ ⁏ Γ ⊪⋆₁ Ξ
                       → Δ , A valid ⁏ Γ ⊪⋆₁ Ξ , A valid
smlifts₁ ξ = smwks₁ ξ , smvz₁


smvars₁ : ∀ {Δ Δ′ Γ} → Δ′ ⊇ Δ
                     → Δ′ ⁏ Γ ⊪⋆₁ Δ
smvars₁ done     = ∙
smvars₁ (drop η) = smwks₁ (smvars₁ η)
smvars₁ (keep η) = smlifts₁ (smvars₁ η)


smids₁ : ∀ {Δ Γ} → Δ ⁏ Γ ⊪⋆₁ Δ
smids₁ = smvars₁ id⊇


--------------------------------------------------------------------------------


↑ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊨ A true
              → Δ ⨾ₙₘ Γ ⊢ₙₘ A true
↑ f = ⇑ (f smids₁ sids)


nbe : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ A true
                → Δ ⨾ₙₘ Γ ⊢ₙₘ A true
nbe 𝒟 = ↑ (↓ 𝒟)


--------------------------------------------------------------------------------