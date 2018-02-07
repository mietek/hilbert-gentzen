{-# OPTIONS --rewriting #-}

module S4ProjectionToIPL where

open import Prelude
open import Category
open import List
open import ListLemmas
open import ListConcatenation
open import S4Propositions
open import S4StandardDerivations
open import S4EmbeddingOfIPL
import IPLPropositions as IPL
import IPLStandardDerivations as IPL


--------------------------------------------------------------------------------


↓ₚ : Prop → IPL.Prop
↓ₚ (ι P)   = IPL.ι P
↓ₚ (A ⊃ B) = ↓ₚ A IPL.⊃ ↓ₚ B
↓ₚ (□ A)   = ↓ₚ A


↓ₚₛ : List Prop → List IPL.Prop
↓ₚₛ Γ = map ↓ₚ Γ


↓ₐ : Assert → IPL.Prop
↓ₐ ⟪⊫ A ⟫ = ↓ₚ A


↓ₐₛ : List Assert → List IPL.Prop
↓ₐₛ Δ = map ↓ₐ Δ


↓∋ₚ : ∀ {Γ A} → Γ ∋ A
              → ↓ₚₛ Γ ∋ ↓ₚ A
↓∋ₚ zero    = zero
↓∋ₚ (suc i) = suc (↓∋ₚ i)


↓∋ₐ : ∀ {Δ A} → Δ ∋ ⟪⊫ A ⟫
              → ↓ₐₛ Δ ∋ ↓ₚ A
↓∋ₐ zero    = zero
↓∋ₐ (suc i) = suc (↓∋ₐ i)


↓ : ∀ {Δ Γ A} → Δ ⊢ A valid[ Γ ]
              → ↓ₐₛ Δ ⧺ ↓ₚₛ Γ IPL.⊢ ↓ₚ A true
↓ {Δ = Δ} (var i)      = IPL.ren (ldrops (↓ₐₛ Δ) id) (IPL.var (↓∋ₚ i))
↓         (lam 𝒟)      = IPL.lam (↓ 𝒟)
↓         (app 𝒟 ℰ)    = IPL.app (↓ 𝒟) (↓ ℰ)
↓ {Γ = Γ} (mvar i)     = IPL.ren (rdrops (↓ₚₛ Γ) id) (IPL.var (↓∋ₐ i))
↓ {Γ = Γ} (box 𝒟)      = IPL.ren (rdrops (↓ₚₛ Γ) id) (↓ 𝒟)
↓ {Γ = Γ} (letbox 𝒟 ℰ) = IPL.cut (↓ 𝒟) (IPL.pull (↓ₚₛ Γ) (↓ ℰ))


--------------------------------------------------------------------------------


id↓↑ₚ : (A : IPL.Prop) → (↓ₚ ∘ ↑ₚ) A ≡ A
id↓↑ₚ (IPL.ι P)   = refl
id↓↑ₚ (A IPL.⊃ B) = IPL._⊃_ & id↓↑ₚ A ⊗ id↓↑ₚ B


-- NOTE: Agda does not accept this type for REWRITE
-- id↓↑ₚₛ : ∀ {Γ} → (↓ₚₛ ∘ ↑ₚₛ) Γ ≡ Γ

id↓↑ₚₛ : (Γ : List IPL.Prop) → map ↓ₚ (map ↑ₚ Γ) ≡ Γ
id↓↑ₚₛ ∙       = refl
id↓↑ₚₛ (Γ , A) = _,_ & id↓↑ₚₛ Γ ⊗ id↓↑ₚ A


{-# REWRITE id↓↑ₚ #-}
{-# REWRITE id↓↑ₚₛ #-}
id↓↑∋ₚ : ∀ {Γ A} → (i : Γ ∋ A)
                 → (↓∋ₚ ∘ ↑∋ₚ) i ≡ i
id↓↑∋ₚ zero    = refl
id↓↑∋ₚ (suc i) = suc & id↓↑∋ₚ i


{-# REWRITE id↓↑∋ₚ #-}
id↓↑ : ∀ {Γ A} → (𝒟 : Γ IPL.⊢ A true)
               → (↓ {∙} ∘ ↑ {∙}) 𝒟 ≡ 𝒟
id↓↑ (IPL.var i)   = IPL.var & ( (\ η′ → ren∋ η′ i) & lid-ldrops id
                               ⋮ id-ren∋ i
                               )
id↓↑ (IPL.lam 𝒟)   = IPL.lam & id↓↑ 𝒟
id↓↑ (IPL.app 𝒟 ℰ) = IPL.app & id↓↑ 𝒟 ⊗ id↓↑ ℰ


-- id↑↓ₚ : (A : Prop) → (↑ₚ ∘ ↓ₚ) A ≡ A
-- id↑↓ₚ (ι P)   = refl
-- id↑↓ₚ (A ⊃ B) = _⊃_ & id↑↓ₚ A ⊗ id↑↓ₚ B
-- id↑↓ₚ (□ A)   = {!!}


-- NOTE: Cannot hold

-- id↑↓ : ∀ {Δ Γ A} → (𝒟 : Δ ⊢ A valid[ Γ ])
--                  → (↑ ∘ ↓) 𝒟 ≡ 𝒟
-- id↑↓ 𝒟 = ?


-- TODO: Semantic equivalence


--------------------------------------------------------------------------------
