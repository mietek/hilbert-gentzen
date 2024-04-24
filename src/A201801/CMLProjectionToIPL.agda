{-# OPTIONS --rewriting #-}

module A201801.CMLProjectionToIPL where

open import A201801.Prelude
open import A201801.Category
open import A201801.List
open import A201801.ListLemmas
open import A201801.ListConcatenation
open import A201801.AllList
open import A201801.CMLPropositions
open import A201801.CMLStandardDerivations
import A201801.IPLPropositions as IPL
import A201801.IPLStandardDerivations as IPL


--------------------------------------------------------------------------------


mutual
  ↓ₚ : Form → IPL.Form
  ↓ₚ (ι P)     = IPL.ι P
  ↓ₚ (A ⊃ B)   = ↓ₚ A IPL.⊃ ↓ₚ B
  ↓ₚ ([ Ψ ] A) = ↓ₚₛ Ψ IPL.⊃⋯⊃ ↓ₚ A

  ↓ₚₛ : List Form → List IPL.Form
  ↓ₚₛ ∙       = ∙
  ↓ₚₛ (Ξ , A) = ↓ₚₛ Ξ , ↓ₚ A


↓ₐ : Assert → IPL.Form
↓ₐ ⟪ Γ ⊫ A ⟫ = ↓ₚₛ Γ IPL.⊃⋯⊃ ↓ₚ A


↓ₐₛ : List Assert → List IPL.Form
↓ₐₛ Δ = map ↓ₐ Δ


↓∋ₚ : ∀ {Γ A} → Γ ∋ A
              → ↓ₚₛ Γ ∋ ↓ₚ A
↓∋ₚ zero    = zero
↓∋ₚ (suc i) = suc (↓∋ₚ i)


↓∋ₐ : ∀ {Δ Γ A} → Δ ∋ ⟪ Γ ⊫ A ⟫
                → ↓ₐₛ Δ ∋ ↓ₚₛ Γ IPL.⊃⋯⊃ ↓ₚ A
↓∋ₐ zero    = zero
↓∋ₐ (suc i) = suc (↓∋ₐ i)


mutual
  ↓ : ∀ {Δ Γ A} → Δ ⊢ A valid[ Γ ]
                → ↓ₐₛ Δ ⧺ ↓ₚₛ Γ IPL.⊢ ↓ₚ A true
  ↓ {Δ = Δ}     (var i)         = IPL.ren (ldrops (↓ₐₛ Δ) id⊇) (IPL.var (↓∋ₚ i))
  ↓             (lam 𝒟)         = IPL.lam (↓ 𝒟)
  ↓             (app 𝒟 ℰ)       = IPL.app (↓ 𝒟) (↓ ℰ)
  ↓ {Γ = Γ}     (mvar i ψ)      = IPL.apps (IPL.ren (rdrops (↓ₚₛ Γ) id) (IPL.var (↓∋ₐ i))) (↓ⁿ ψ)
  ↓ {Δ = Δ} {Γ} (box {Ψ = Ψ} 𝒟) = IPL.ren {Γ = ↓ₐₛ Δ} (rdrops (↓ₚₛ Γ) id⊇) (IPL.lams (↓ₚₛ Ψ) (↓ 𝒟))
  ↓ {Γ = Γ}     (letbox 𝒟 ℰ)    = IPL.cut (↓ 𝒟) (IPL.pull (↓ₚₛ Γ) (↓ ℰ))

  ↓ⁿ : ∀ {Δ Γ Ξ} → Δ ⊢ Ξ allvalid[ Γ ]
                 → ↓ₐₛ Δ ⧺ ↓ₚₛ Γ IPL.⊢ ↓ₚₛ Ξ alltrue
  ↓ⁿ ∙       = ∙
  ↓ⁿ (ξ , 𝒟) = ↓ⁿ ξ , ↓ 𝒟


--------------------------------------------------------------------------------


↑ₚ : IPL.Form → Form
↑ₚ (IPL.ι P)   = ι P
↑ₚ (A IPL.⊃ B) = ↑ₚ A ⊃ ↑ₚ B


↑ₚₛ : List IPL.Form → List Form
↑ₚₛ Γ = map ↑ₚ Γ


↑∋ₚ : ∀ {Γ A} → Γ ∋ A
              → ↑ₚₛ Γ ∋ ↑ₚ A
↑∋ₚ zero    = zero
↑∋ₚ (suc i) = suc (↑∋ₚ i)


↑ : ∀ {Δ Γ A} → Γ IPL.⊢ A true
              → Δ ⊢ ↑ₚ A valid[ ↑ₚₛ Γ ]
↑ (IPL.var i)   = var (↑∋ₚ i)
↑ (IPL.lam 𝒟)   = lam (↑ 𝒟)
↑ (IPL.app 𝒟 ℰ) = app (↑ 𝒟) (↑ ℰ)


--------------------------------------------------------------------------------


-- TODO: something broke
-- id↓↑ₚ : ∀ {A} → (↓ₚ ∘ ↑ₚ) A ≡ A
-- id↓↑ₚ {IPL.ι P}   = refl
-- id↓↑ₚ {A IPL.⊃ B} = IPL._⊃_ & id↓↑ₚ ⊗ id↓↑ₚ
--
--
-- -- NOTE: Agda does not accept this type for REWRITE
-- -- id↓↑ₚₛ : ∀ {Γ} → (↓ₚₛ ∘ ↑ₚₛ) Γ ≡ Γ
--
-- id↓↑ₚₛ : ∀ {Γ} → ↓ₚₛ (map ↑ₚ Γ) ≡ Γ
-- id↓↑ₚₛ {∙}     = refl
-- id↓↑ₚₛ {Γ , A} = _,_ & id↓↑ₚₛ ⊗ id↓↑ₚ
--
--
-- {-# REWRITE id↓↑ₚ #-}
-- {-# REWRITE id↓↑ₚₛ #-}
-- id↓↑∋ₚ : ∀ {Γ A} → (i : Γ ∋ A)
--                  → (↓∋ₚ ∘ ↑∋ₚ) i ≡ i
-- id↓↑∋ₚ zero    = refl
-- id↓↑∋ₚ (suc i) = suc & id↓↑∋ₚ i
--
--
-- {-# REWRITE id↓↑∋ₚ #-}
-- id↓↑ : ∀ {Γ A} → (𝒟 : Γ IPL.⊢ A true)
--                → (↓ {∙} ∘ ↑ {∙}) 𝒟 ≡ 𝒟
-- id↓↑ (IPL.var i)   = IPL.var & ( (\ η′ → ren∋ η′ i) & lid-ldrops id
--                                ⋮ id-ren∋ i
--                                )
-- id↓↑ (IPL.lam 𝒟)   = IPL.lam & id↓↑ 𝒟
-- id↓↑ (IPL.app 𝒟 ℰ) = IPL.app & id↓↑ 𝒟 ⊗ id↓↑ ℰ
--
--
-- -- NOTE: Cannot hold
--
-- -- id↑↓ : ∀ {Δ Γ A} → (𝒟 : Δ ⊢ A valid[ Γ ])
-- --                  → (↑ ∘ ↓) 𝒟 ≡ 𝒟
-- -- id↑↓ 𝒟 = ?
--
--
-- -- TODO: Semantic equivalence


--------------------------------------------------------------------------------
