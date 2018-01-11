module StdCMLNormalForms where

open import Prelude
open import List
open List²
open import AllList
open import StdCML


--------------------------------------------------------------------------------


mutual
  infix 3 _⊢ₙₘ_
  data _⊢ₙₘ_ : List² Validity Truth → Truth → Set
    where
      lam : ∀ {A B Δ Γ} → Δ ⨾ Γ , A true ⊢ₙₘ B true
                        → Δ ⨾ Γ ⊢ₙₘ A ⊃ B true

      box : ∀ {A Ψ Δ Γ} → Δ ⨾ Ψ ⊢ A true
                        → Δ ⨾ Γ ⊢ₙₘ [ Ψ ] A true

      letbox : ∀ {A B Ψ Δ Γ} → Δ ⨾ Γ ⊢ₙₜ [ Ψ ] A true → Δ , A valid[ Ψ ] ⨾ Γ ⊢ₙₘ B true
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

      mvar : ∀ {A Ψ Δ Γ} → Δ ∋ A valid[ Ψ ] → Δ ⨾ Γ ⊢⋆ₙₘ Ψ
                         → Δ ⨾ Γ ⊢ₙₜ A true

  infix 3 _⊢⋆ₙₘ_
  _⊢⋆ₙₘ_ : List² Validity Truth → List Truth → Set
  Δ ⨾ Γ ⊢⋆ₙₘ Ξ = All (Δ ⨾ Γ ⊢ₙₘ_) Ξ


infix 3 _⊢⋆ₙₜ_
_⊢⋆ₙₜ_ : List² Validity Truth → List Truth → Set
Δ ⨾ Γ ⊢⋆ₙₜ Ξ = All (Δ ⨾ Γ ⊢ₙₜ_) Ξ


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
  embₙₜ (var 𝒾)    = var 𝒾
  embₙₜ (app 𝒟 ℰ)  = app (embₙₜ 𝒟) (embₙₘ ℰ)
  embₙₜ (mvar 𝒾 ψ) = mvar 𝒾 (embsₙₘ ψ)

  embsₙₘ : ∀ {Δ Γ Ξ} → Δ ⨾ Γ ⊢⋆ₙₘ Ξ
                     → Δ ⨾ Γ ⊢⋆ Ξ
  embsₙₘ ∙       = ∙
  embsₙₘ (ξ , 𝒟) = embsₙₘ ξ , embₙₘ 𝒟


embsₙₜ : ∀ {Δ Γ Ξ} → Δ ⨾ Γ ⊢⋆ₙₜ Ξ
                   → Δ ⨾ Γ ⊢⋆ Ξ
embsₙₜ ξ = maps embₙₜ ξ


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
  renₙₜ η (var 𝒾)    = var (ren∋ η 𝒾)
  renₙₜ η (app 𝒟 ℰ)  = app (renₙₜ η 𝒟) (renₙₘ η ℰ)
  renₙₜ η (mvar 𝒾 ψ) = mvar 𝒾 (rensₙₘ η ψ)

  rensₙₘ : ∀ {Δ Γ Γ′ Ξ} → Γ′ ⊇ Γ → Δ ⨾ Γ ⊢⋆ₙₘ Ξ
                        → Δ ⨾ Γ′ ⊢⋆ₙₘ Ξ
  rensₙₘ η ∙       = ∙
  rensₙₘ η (ξ , 𝒟) = rensₙₘ η ξ , renₙₘ η 𝒟
  -- NOTE: Equivalent to
  -- rensₙₘ η ξ = maps (renₙₘ η) ξ


rensₙₜ : ∀ {Δ Γ Γ′ Ξ} → Γ′ ⊇ Γ → Δ ⨾ Γ ⊢⋆ₙₜ Ξ
                      → Δ ⨾ Γ′ ⊢⋆ₙₜ Ξ
rensₙₜ η ξ = maps (renₙₜ η) ξ


--------------------------------------------------------------------------------


wkₙₘ : ∀ {B A Δ Γ} → Δ ⨾ Γ ⊢ₙₘ A true
                   → Δ ⨾ Γ , B true ⊢ₙₘ A true
wkₙₘ 𝒟 = renₙₘ (drop id⊇) 𝒟


wkₙₜ : ∀ {B A Δ Γ} → Δ ⨾ Γ ⊢ₙₜ A true
                   → Δ ⨾ Γ , B true ⊢ₙₜ A true
wkₙₜ 𝒟 = renₙₜ (drop id⊇) 𝒟


vzₙₜ : ∀ {A Δ Γ} → Δ ⨾ Γ , A true ⊢ₙₜ A true
vzₙₜ = var zero


--------------------------------------------------------------------------------


wksₙₘ : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢⋆ₙₘ Ξ
                    → Δ ⨾ Γ , A true ⊢⋆ₙₘ Ξ
wksₙₘ ξ = rensₙₘ (drop id⊇) ξ


wksₙₜ : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢⋆ₙₜ Ξ
                    → Δ ⨾ Γ , A true ⊢⋆ₙₜ Ξ
wksₙₜ ξ = rensₙₜ (drop id⊇) ξ


liftsₙₜ : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢⋆ₙₜ Ξ
                      → Δ ⨾ Γ , A true ⊢⋆ₙₜ Ξ , A true
liftsₙₜ ξ = wksₙₜ ξ , vzₙₜ


idsₙₜ : ∀ {Δ Γ} → Δ ⨾ Γ ⊢⋆ₙₜ Γ
idsₙₜ {Γ = ∙}          = ∙
idsₙₜ {Γ = Γ , A true} = liftsₙₜ idsₙₜ


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
  mrenₙₜ η (var 𝒾)    = var 𝒾
  mrenₙₜ η (app 𝒟 ℰ)  = app (mrenₙₜ η 𝒟) (mrenₙₘ η ℰ)
  mrenₙₜ η (mvar 𝒾 ψ) = mvar (ren∋ η 𝒾) (mrensₙₘ η ψ)

  mrensₙₘ : ∀ {Δ Δ′ Γ Ξ} → Δ′ ⊇ Δ → Δ ⨾ Γ ⊢⋆ₙₘ Ξ
                         → Δ′ ⨾ Γ ⊢⋆ₙₘ Ξ
  mrensₙₘ η ∙       = ∙
  mrensₙₘ η (ξ , 𝒟) = mrensₙₘ η ξ , mrenₙₘ η 𝒟
  -- NOTE: Equivalent to
  -- mrensₙₘ η ξ = maps (mrenₙₘ η) ξ


mrensₙₜ : ∀ {Δ Δ′ Γ Ξ} → Δ′ ⊇ Δ → Δ ⨾ Γ ⊢⋆ₙₜ Ξ
                       → Δ′ ⨾ Γ ⊢⋆ₙₜ Ξ
mrensₙₜ η ξ = maps (mrenₙₜ η) ξ


--------------------------------------------------------------------------------


mwkₙₘ : ∀ {B Ψ A Δ Γ} → Δ ⨾ Γ ⊢ₙₘ A true
                      → Δ , B valid[ Ψ ] ⨾ Γ ⊢ₙₘ A true
mwkₙₘ 𝒟 = mrenₙₘ (drop id⊇) 𝒟


mwkₙₜ : ∀ {B Ψ A Δ Γ} → Δ ⨾ Γ ⊢ₙₜ A true
                      → Δ , B valid[ Ψ ] ⨾ Γ ⊢ₙₜ A true
mwkₙₜ 𝒟 = mrenₙₜ (drop id⊇) 𝒟


mwksₙₘ : ∀ {A Ψ Δ Γ Ξ} → Δ ⨾ Γ ⊢⋆ₙₘ Ξ
                       → Δ , A valid[ Ψ ] ⨾ Γ ⊢⋆ₙₘ Ξ
mwksₙₘ ξ = mrensₙₘ (drop id⊇) ξ


mwksₙₜ : ∀ {A Ψ Δ Γ Ξ} → Δ ⨾ Γ ⊢⋆ₙₜ Ξ
                       → Δ , A valid[ Ψ ] ⨾ Γ ⊢⋆ₙₜ Ξ
mwksₙₜ ξ = mrensₙₜ (drop id⊇) ξ


mvzₙₜ : ∀ {A Ψ Δ Γ} → Δ ⨾ Γ ⊢⋆ₙₘ Ψ
                    → Δ , A valid[ Ψ ] ⨾ Γ ⊢ₙₜ A true
mvzₙₜ ψ = mvar zero (mwksₙₘ ψ)


--------------------------------------------------------------------------------


renₙₜ² : ∀ {Δ Δ′ Γ Γ′ A} → Δ′ ⨾ Γ′ ⊇² Δ ⨾ Γ → Δ ⨾ Γ ⊢ₙₜ A true
                         → Δ′ ⨾ Γ′ ⊢ₙₜ A true
renₙₜ² η 𝒟 = mrenₙₜ (proj₁ η) (renₙₜ (proj₂ η) 𝒟)


--------------------------------------------------------------------------------
