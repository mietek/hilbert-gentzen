module StdS4NormalForms where

open import Prelude
open import List
open import List2
open import StdS4


--------------------------------------------------------------------------------


mutual
  infix 3 _⊢ₙₘ_
  data _⊢ₙₘ_ : List² Validity Truth → Truth → Set
    where
      lam : ∀ {A B Δ Γ} → Δ ⨾ Γ , A true ⊢ₙₘ B true
                        → Δ ⨾ Γ ⊢ₙₘ A ⊃ B true

      box : ∀ {A Δ Γ} → Δ ⨾ ∙ ⊢ A true
                      → Δ ⨾ Γ ⊢ₙₘ □ A true

      letbox : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ₙₜ □ A true → Δ , A valid ⨾ Γ ⊢ₙₘ B true
                           → Δ ⨾ Γ ⊢ₙₘ B true

      nt : ∀ {Δ Γ} → Δ ⨾ Γ ⊢ₙₜ BASE true
                   → Δ ⨾ Γ ⊢ₙₘ BASE true

  infix 3 _⊢ₙₜ_
  data _⊢ₙₜ_ : List² Validity Truth → Truth → Set
    where
      var : ∀ {A Δ Γ} → Γ ∋ A true
                      → Δ ⨾ Γ ⊢ₙₜ A true

      app : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ₙₜ A ⊃ B true → Δ ⨾ Γ ⊢ₙₘ A true
                        → Δ ⨾ Γ ⊢ₙₜ B true

      mvar : ∀ {A Δ Γ} → Δ ∋ A valid
                       → Δ ⨾ Γ ⊢ₙₜ A true


--------------------------------------------------------------------------------


mutual
  embₙₘ : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ₙₘ A true
                    → Δ ⨾ Γ ⊢ A true
  embₙₘ (lam 𝒟)      = lam (embₙₘ 𝒟)
  embₙₘ (box 𝒟)      = box 𝒟
  embₙₘ (letbox 𝒟 ℰ) = letbox (embₙₜ 𝒟) (embₙₘ ℰ)
  embₙₘ (nt 𝒟)       = embₙₜ 𝒟

  embₙₜ : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ₙₜ A true
                    → Δ ⨾ Γ ⊢ A true
  embₙₜ (var 𝒾)   = var 𝒾
  embₙₜ (app 𝒟 ℰ) = app (embₙₜ 𝒟) (embₙₘ ℰ)
  embₙₜ (mvar 𝒾)  = mvar 𝒾


--------------------------------------------------------------------------------


mutual
  renₙₘ : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⨾ Γ ⊢ₙₘ A true
                       → Δ ⨾ Γ′ ⊢ₙₘ A true
  renₙₘ η (lam 𝒟)      = lam (renₙₘ (keep η) 𝒟)
  renₙₘ η (box 𝒟)      = box 𝒟
  renₙₘ η (letbox 𝒟 ℰ) = letbox (renₙₜ η 𝒟) (renₙₘ η ℰ)
  renₙₘ η (nt 𝒟)       = nt (renₙₜ η 𝒟)

  renₙₜ : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⨾ Γ ⊢ₙₜ A true
                       → Δ ⨾ Γ′ ⊢ₙₜ A true
  renₙₜ η (var 𝒾)   = var (ren∋ η 𝒾)
  renₙₜ η (app 𝒟 ℰ) = app (renₙₜ η 𝒟) (renₙₘ η ℰ)
  renₙₜ η (mvar 𝒾)  = mvar 𝒾


wkₙₜ : ∀ {B A Δ Γ} → Δ ⨾ Γ ⊢ₙₜ A true
                   → Δ ⨾ Γ , B true ⊢ₙₜ A true
wkₙₜ 𝒟 = renₙₜ (drop id⊇) 𝒟


vzₙₜ : ∀ {A Δ Γ} → Δ ⨾ Γ , A true ⊢ₙₜ A true
vzₙₜ = var zero


--------------------------------------------------------------------------------


mutual
  mrenₙₘ : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⨾ Γ ⊢ₙₘ A true
                        → Δ′ ⨾ Γ ⊢ₙₘ A true
  mrenₙₘ η (lam 𝒟)      = lam (mrenₙₘ η 𝒟)
  mrenₙₘ η (box 𝒟)      = box (mren η 𝒟)
  mrenₙₘ η (letbox 𝒟 ℰ) = letbox (mrenₙₜ η 𝒟) (mrenₙₘ (keep η) ℰ)
  mrenₙₘ η (nt 𝒟)       = nt (mrenₙₜ η 𝒟)

  mrenₙₜ : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⨾ Γ ⊢ₙₜ A true
                        → Δ′ ⨾ Γ ⊢ₙₜ A true
  mrenₙₜ η (var 𝒾)   = var 𝒾
  mrenₙₜ η (app 𝒟 ℰ) = app (mrenₙₜ η 𝒟) (mrenₙₘ η ℰ)
  mrenₙₜ η (mvar 𝒾)  = mvar (ren∋ η 𝒾)


mwkₙₜ : ∀ {B A Δ Γ} → Δ ⨾ Γ ⊢ₙₜ A true
                    → Δ , B valid ⨾ Γ ⊢ₙₜ A true
mwkₙₜ 𝒟 = mrenₙₜ (drop id⊇) 𝒟


mvzₙₜ : ∀ {A Δ Γ} → Δ , A valid ⨾ Γ ⊢ₙₜ A true
mvzₙₜ = mvar zero


--------------------------------------------------------------------------------


renₙₜ² : ∀ {Δ Δ′ Γ Γ′ A} → Δ′ ⨾ Γ′ ⊇² Δ ⨾ Γ → Δ ⨾ Γ ⊢ₙₜ A true
                         → Δ′ ⨾ Γ′ ⊢ₙₜ A true
renₙₜ² η 𝒟 = mrenₙₜ (proj₁ η) (renₙₜ (proj₂ η) 𝒟)


--------------------------------------------------------------------------------
