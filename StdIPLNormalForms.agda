module StdIPLNormalForms where

open import Prelude
open import List
open import AllList
open import StdIPL


--------------------------------------------------------------------------------


mutual
  infix 3 _⊢ₙₘ_
  data _⊢ₙₘ_ : Context → Truth → Set
    where
      lam : ∀ {A B Γ} → Γ , A true ⊢ₙₘ B true
                      → Γ ⊢ₙₘ A ⊃ B true

      nt : ∀ {Γ} → Γ ⊢ₙₜ BASE true
                 → Γ ⊢ₙₘ BASE true

  infix 3 _⊢ₙₜ_
  data _⊢ₙₜ_ : Context → Truth → Set
    where
      var : ∀ {A Γ} → Γ ∋ A true
                    → Γ ⊢ₙₜ A true

      app : ∀ {A B Γ} → Γ ⊢ₙₜ A ⊃ B true → Γ ⊢ₙₘ A true
                      → Γ ⊢ₙₜ B true


--------------------------------------------------------------------------------


mutual
  embₙₘ : ∀ {Γ A} → Γ ⊢ₙₘ A true
                  → Γ ⊢ A true
  embₙₘ (lam 𝒟) = lam (embₙₘ 𝒟)
  embₙₘ (nt 𝒟)  = embₙₜ 𝒟

  embₙₜ : ∀ {Γ A} → Γ ⊢ₙₜ A true
                  → Γ ⊢ A true
  embₙₜ (var 𝒾)   = var 𝒾
  embₙₜ (app 𝒟 ℰ) = app (embₙₜ 𝒟) (embₙₘ ℰ)


--------------------------------------------------------------------------------


mutual
  renₙₘ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ₙₘ A true
                     → Γ′ ⊢ₙₘ A true
  renₙₘ η (lam 𝒟) = lam (renₙₘ (keep η) 𝒟)
  renₙₘ η (nt 𝒟)  = nt (renₙₜ η 𝒟)

  renₙₜ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ₙₜ A true
                     → Γ′ ⊢ₙₜ A true
  renₙₜ η (var 𝒾)   = var (ren∋ η 𝒾)
  renₙₜ η (app 𝒟 ℰ) = app (renₙₜ η 𝒟) (renₙₘ η ℰ)


wkₙₜ : ∀ {B A Γ} → Γ ⊢ₙₜ A true
                 → Γ , B true ⊢ₙₜ A true
wkₙₜ 𝒟 = renₙₜ (drop id⊇) 𝒟


vzₙₜ : ∀ {A Γ} → Γ , A true ⊢ₙₜ A true
vzₙₜ = var zero


--------------------------------------------------------------------------------
