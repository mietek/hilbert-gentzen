{-# OPTIONS --rewriting #-}

module A201801.CMLProjectionToS4 where

open import A201801.Prelude
open import A201801.Category
open import A201801.List
open import A201801.ListLemmas
open import A201801.ListConcatenation
open import A201801.AllList
open import A201801.CMLPropositions
open import A201801.CMLStandardDerivations
import A201801.S4Propositions as S4
import A201801.S4StandardDerivations as S4


--------------------------------------------------------------------------------


mutual
  ⟦_⟧ₚ : Form → S4.Form
  ⟦ ι P ⟧ₚ     = S4.ι P
  ⟦ A ⊃ B ⟧ₚ   = ⟦ A ⟧ₚ S4.⊃ ⟦ B ⟧ₚ
  ⟦ [ Ψ ] A ⟧ₚ = S4.□ (⟦ Ψ ⟧ₚₛ S4.⊃⋯⊃ ⟦ A ⟧ₚ)

  ⟦_⟧ₚₛ : List Form → List S4.Form
  ⟦ ∙ ⟧ₚₛ     = ∙
  ⟦ Ξ , A ⟧ₚₛ = ⟦ Ξ ⟧ₚₛ , ⟦ A ⟧ₚ


⟦_⟧ₐ : Assert → S4.Assert
⟦ ⟪ Γ ⊫ A ⟫ ⟧ₐ = S4.⟪⊫ ⟦ Γ ⟧ₚₛ S4.⊃⋯⊃ ⟦ A ⟧ₚ ⟫


⟦_⟧ₐₛ : List Assert → List S4.Assert
⟦ Δ ⟧ₐₛ = map ⟦_⟧ₐ Δ


⟦_⟧∋ₚ : ∀ {Γ A} → Γ ∋ A
                → ⟦ Γ ⟧ₚₛ ∋ ⟦ A ⟧ₚ
⟦ zero ⟧∋ₚ  = zero
⟦ suc i ⟧∋ₚ = suc ⟦ i ⟧∋ₚ


⟦_⟧∋ₐ : ∀ {Δ Γ A} → Δ ∋ ⟪ Γ ⊫ A ⟫
                  → ⟦ Δ ⟧ₐₛ ∋ S4.⟪⊫ ⟦ Γ ⟧ₚₛ S4.⊃⋯⊃ ⟦ A ⟧ₚ ⟫
⟦ zero ⟧∋ₐ  = zero
⟦ suc i ⟧∋ₐ = suc ⟦ i ⟧∋ₐ


-- TODO: unfinished
-- mutual
--   ⟦_⟧ : ∀ {Δ Γ A} → Δ ⊢ A valid[ Γ ]
--                   → ⟦ Δ ⟧ₐₛ S4.⊢ ⟦ A ⟧ₚ valid[ ⟦ Γ ⟧ₚₛ ]
--   ⟦ var i ⟧         = S4.var ⟦ i ⟧∋ₚ
--   ⟦ lam 𝒟 ⟧         = S4.lam ⟦ 𝒟 ⟧
--   ⟦ app 𝒟 ℰ ⟧       = S4.app ⟦ 𝒟 ⟧ ⟦ ℰ ⟧
--   ⟦ mvar i ψ ⟧      = {!S4.apps (S4.mvar ⟦ i ⟧∋ₐ) ⟦ ψ ⟧ⁿ!}
--   ⟦ box {Ψ = Ψ} 𝒟 ⟧ = {!S4.box (S4.lams ⟦ Ψ ⟧ₚₛ ⟦ 𝒟 ⟧)!}
--   ⟦ letbox 𝒟 ℰ ⟧    = S4.letbox ⟦ 𝒟 ⟧ ⟦ ℰ ⟧
--
--   ⟦_⟧ⁿ : ∀ {Δ Γ Ξ} → Δ ⊢ Ξ allvalid[ Γ ]
--                    → ⟦ Δ ⟧ₐₛ S4.⊢ ⟦ Ξ ⟧ₚₛ allvalid[ ⟦ Γ ⟧ₚₛ ]
--   ⟦ ∙ ⟧ⁿ     = ∙
--   ⟦ ξ , 𝒟 ⟧ⁿ = ⟦ ξ ⟧ⁿ , ⟦ 𝒟 ⟧


--------------------------------------------------------------------------------


↓ₚ : S4.Form → Form
↓ₚ (S4.ι P)   = ι P
↓ₚ (A S4.⊃ B) = (↓ₚ A) ⊃ (↓ₚ B)
↓ₚ (S4.□ A)   = [ ∙ ] (↓ₚ A)


↓ₚₛ : List S4.Form → List Form
↓ₚₛ Γ = map ↓ₚ Γ


↓ₐ : S4.Assert → Assert
↓ₐ S4.⟪⊫ A ⟫ = ⟪ ∙ ⊫ ↓ₚ A ⟫


↓ₐₛ : List S4.Assert → List Assert
↓ₐₛ Δ = map ↓ₐ Δ


↓∋ₚ : ∀ {Γ A} → Γ ∋ A
              → ↓ₚₛ Γ ∋ ↓ₚ A
↓∋ₚ zero    = zero
↓∋ₚ (suc i) = suc (↓∋ₚ i)


↓∋ₐ : ∀ {Δ A} → Δ ∋ S4.⟪⊫ A ⟫
              → ↓ₐₛ Δ ∋ ⟪ ∙ ⊫ ↓ₚ A ⟫
↓∋ₐ zero    = zero
↓∋ₐ (suc i) = suc (↓∋ₐ i)


↓ : ∀ {Δ Γ A} → Δ S4.⊢ A valid[ Γ ]
              → ↓ₐₛ Δ ⊢ ↓ₚ A valid[ ↓ₚₛ Γ ]
↓ (S4.var i)      = var (↓∋ₚ i)
↓ (S4.lam 𝒟)      = lam (↓ 𝒟)
↓ (S4.app 𝒟 ℰ)    = app (↓ 𝒟) (↓ ℰ)
↓ (S4.mvar i)     = mvar (↓∋ₐ i) ∙
↓ (S4.box 𝒟)      = box (↓ 𝒟)
↓ (S4.letbox 𝒟 ℰ) = letbox (↓ 𝒟) (↓ ℰ)


--------------------------------------------------------------------------------


id⟦⟧↓ₚ : ∀ {A : S4.Form} → ⟦_⟧ₚ (↓ₚ A) ≡ A
id⟦⟧↓ₚ {S4.ι P}   = refl
id⟦⟧↓ₚ {A S4.⊃ B} = S4._⊃_ & id⟦⟧↓ₚ ⊗ id⟦⟧↓ₚ
id⟦⟧↓ₚ {S4.□ A}   = S4.□_ & id⟦⟧↓ₚ


id⟦⟧↓ₚₛ : ∀ {Γ : List S4.Form} → ⟦_⟧ₚₛ (↓ₚₛ Γ) ≡ Γ
id⟦⟧↓ₚₛ {∙}     = refl
id⟦⟧↓ₚₛ {Γ , A} = _,_ & id⟦⟧↓ₚₛ ⊗ id⟦⟧↓ₚ


id⟦⟧↓ₐ : ∀ {A} → ⟦_⟧ₐ (↓ₐ S4.⟪⊫ A ⟫) ≡ S4.⟪⊫ A ⟫
id⟦⟧↓ₐ = S4.⟪⊫_⟫ & id⟦⟧↓ₚ


-- NOTE: Agda does not accept this type for REWRITE
-- id⟦⟧↓ₐₛ : ∀ {Δ} → (⟦_⟧ₐₛ ∘ ↓ₐₛ) Δ ≡ Δ

id⟦⟧↓ₐₛ : ∀ {Δ} → map ⟦_⟧ₐ (map ↓ₐ Δ) ≡ Δ
id⟦⟧↓ₐₛ {∙}              = refl
id⟦⟧↓ₐₛ {Δ , S4.⟪⊫ A ⟫} = _,_ & id⟦⟧↓ₐₛ ⊗ id⟦⟧↓ₐ


{-# REWRITE id⟦⟧↓ₚ #-}
{-# REWRITE id⟦⟧↓ₚₛ #-}
id⟦⟧↓∋ₚ : ∀ {Γ A} → (i : Γ ∋ A)
                  → ⟦_⟧∋ₚ (↓∋ₚ i) ≡ i
id⟦⟧↓∋ₚ zero    = refl
id⟦⟧↓∋ₚ (suc i) = suc & id⟦⟧↓∋ₚ i


{-# REWRITE id⟦⟧↓ₐₛ #-}
id⟦⟧↓∋ₐ : ∀ {Δ A} → (i : Δ ∋ S4.⟪⊫ A ⟫)
                  → ⟦_⟧∋ₐ (↓∋ₐ i) ≡ i
id⟦⟧↓∋ₐ zero    = refl
id⟦⟧↓∋ₐ (suc i) = suc & id⟦⟧↓∋ₐ i


-- TODO: unfinished
-- {-# REWRITE id⟦⟧↓∋ₚ #-}
-- {-# REWRITE id⟦⟧↓∋ₐ #-}
-- id⟦⟧↓ : ∀ {Δ Γ A} → (𝒟 : Δ S4.⊢ A valid[ Γ ])
--                   → ⟦_⟧ (↓ 𝒟) ≡ 𝒟
-- id⟦⟧↓ (S4.var i)      = refl
-- id⟦⟧↓ (S4.lam 𝒟)      = S4.lam & id⟦⟧↓ 𝒟
-- id⟦⟧↓ (S4.app 𝒟 ℰ)    = S4.app & id⟦⟧↓ 𝒟 ⊗ id⟦⟧↓ ℰ
-- id⟦⟧↓ (S4.mvar i)     = refl
-- id⟦⟧↓ (S4.box 𝒟)      = S4.box & id⟦⟧↓ 𝒟
-- id⟦⟧↓ (S4.letbox 𝒟 ℰ) = S4.letbox & id⟦⟧↓ 𝒟 ⊗ id⟦⟧↓ ℰ


--------------------------------------------------------------------------------
