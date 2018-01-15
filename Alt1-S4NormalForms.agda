module Alt1-S4NormalForms where

open import Prelude
open import List
open import Alt1-S4


--------------------------------------------------------------------------------


infix 4 _⊢ₙₘ_
record NormalDerivability : Set
  where
    constructor _⊢ₙₘ_
    field
      Γ  : List Truth
      Aₜ : Truth


infix 4 _⊢ₙₜ_
record NeutralDerivability : Set
  where
    constructor _⊢ₙₜ_
    field
      Γ  : List Truth
      Aₜ : Truth


mutual
  infix 3 _⨾ₙₘ_
  data _⨾ₙₘ_ : List Validity → NormalDerivability → Set
    where
      lam : ∀ {A B Δ Γ} → Δ ⨾ₙₘ Γ , A true ⊢ₙₘ B true
                        → Δ ⨾ₙₘ Γ ⊢ₙₘ A ⊃ B true

      box : ∀ {A Δ Γ} → Δ ⨾ ∙ ⊢ A true
                      → Δ ⨾ₙₘ Γ ⊢ₙₘ □ A true

      letbox : ∀ {A B Δ Γ} → Δ ⨾ₙₜ Γ ⊢ₙₜ □ A true → Δ , A valid ⨾ₙₘ Γ ⊢ₙₘ B true
                           → Δ ⨾ₙₘ Γ ⊢ₙₘ B true

      nt : ∀ {Δ Γ} → Δ ⨾ₙₜ Γ ⊢ₙₜ BASE true
                   → Δ ⨾ₙₘ Γ ⊢ₙₘ BASE true

  infix 3 _⨾ₙₜ_
  data _⨾ₙₜ_ : List Validity → NeutralDerivability → Set
    where
      var : ∀ {A Δ Γ} → Γ ∋ A true
                      → Δ ⨾ₙₜ Γ ⊢ₙₜ A true

      app : ∀ {A B Δ Γ} → Δ ⨾ₙₜ Γ ⊢ₙₜ A ⊃ B true → Δ ⨾ₙₘ Γ ⊢ₙₘ A true
                        → Δ ⨾ₙₜ Γ ⊢ₙₜ B true

      mvar : ∀ {A Δ Γ} → Δ ∋ A valid
                       → Δ ⨾ₙₜ Γ ⊢ₙₜ A true


--------------------------------------------------------------------------------


mutual
  embₙₘ : ∀ {Δ Γ A} → Δ ⨾ₙₘ Γ ⊢ₙₘ A true
                    → Δ ⨾ Γ ⊢ A true
  embₙₘ (lam 𝒟)      = lam (embₙₘ 𝒟)
  embₙₘ (box 𝒟)      = box 𝒟
  embₙₘ (letbox 𝒟 ℰ) = letbox (embₙₜ 𝒟) (embₙₘ ℰ)
  embₙₘ (nt 𝒟)       = embₙₜ 𝒟

  embₙₜ : ∀ {Δ Γ A} → Δ ⨾ₙₜ Γ ⊢ₙₜ A true
                    → Δ ⨾ Γ ⊢ A true
  embₙₜ (var 𝒾)   = var 𝒾
  embₙₜ (app 𝒟 ℰ) = app (embₙₜ 𝒟) (embₙₘ ℰ)
  embₙₜ (mvar 𝒾)  = mvar 𝒾


--------------------------------------------------------------------------------


mutual
  renₙₘ : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⨾ₙₘ Γ ⊢ₙₘ A true
                       → Δ ⨾ₙₘ Γ′ ⊢ₙₘ A true
  renₙₘ η (lam 𝒟)      = lam (renₙₘ (keep η) 𝒟)
  renₙₘ η (box 𝒟)      = box 𝒟
  renₙₘ η (letbox 𝒟 ℰ) = letbox (renₙₜ η 𝒟) (renₙₘ η ℰ)
  renₙₘ η (nt 𝒟)       = nt (renₙₜ η 𝒟)

  renₙₜ : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⨾ₙₜ Γ ⊢ₙₜ A true
                       → Δ ⨾ₙₜ Γ′ ⊢ₙₜ A true
  renₙₜ η (var 𝒾)   = var (ren∋ η 𝒾)
  renₙₜ η (app 𝒟 ℰ) = app (renₙₜ η 𝒟) (renₙₘ η ℰ)
  renₙₜ η (mvar 𝒾)  = mvar 𝒾


wkₙₜ : ∀ {B A Δ Γ} → Δ ⨾ₙₜ Γ ⊢ₙₜ A true
                   → Δ ⨾ₙₜ Γ , B true ⊢ₙₜ A true
wkₙₜ 𝒟 = renₙₜ (drop id⊇) 𝒟


vzₙₜ : ∀ {A Δ Γ} → Δ ⨾ₙₜ Γ , A true ⊢ₙₜ A true
vzₙₜ = var zero


--------------------------------------------------------------------------------


mutual
  mrenₙₘ : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⨾ₙₘ Γ ⊢ₙₘ A true
                        → Δ′ ⨾ₙₘ Γ ⊢ₙₘ A true
  mrenₙₘ η (lam 𝒟)      = lam (mrenₙₘ η 𝒟)
  mrenₙₘ η (box 𝒟)      = box (mren η 𝒟)
  mrenₙₘ η (letbox 𝒟 ℰ) = letbox (mrenₙₜ η 𝒟) (mrenₙₘ (keep η) ℰ)
  mrenₙₘ η (nt 𝒟)       = nt (mrenₙₜ η 𝒟)

  mrenₙₜ : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⨾ₙₜ Γ ⊢ₙₜ A true
                        → Δ′ ⨾ₙₜ Γ ⊢ₙₜ A true
  mrenₙₜ η (var 𝒾)   = var 𝒾
  mrenₙₜ η (app 𝒟 ℰ) = app (mrenₙₜ η 𝒟) (mrenₙₘ η ℰ)
  mrenₙₜ η (mvar 𝒾)  = mvar (ren∋ η 𝒾)


mwkₙₜ : ∀ {B A Δ Γ} → Δ ⨾ₙₜ Γ ⊢ₙₜ A true
                    → Δ , B valid ⨾ₙₜ Γ ⊢ₙₜ A true
mwkₙₜ 𝒟 = mrenₙₜ (drop id⊇) 𝒟


mvzₙₜ : ∀ {A Δ Γ} → Δ , A valid ⨾ₙₜ Γ ⊢ₙₜ A true
mvzₙₜ = mvar zero


--------------------------------------------------------------------------------


-- renₙₜ² : ∀ {Δ Δ′ Γ Γ′ A} → Δ′ ⁏ Γ′ ⊇² Δ ⁏ Γ → Δ ⨾ₙₜ Γ ⊢ₙₜ A true
--                          → Δ′ ⨾ₙₜ Γ′ ⊢ₙₜ A true
-- renₙₜ² η 𝒟 = mrenₙₜ (proj₁ η) (renₙₜ (proj₂ η) 𝒟)


--------------------------------------------------------------------------------
