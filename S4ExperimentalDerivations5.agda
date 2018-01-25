module S4ExperimentalDerivations5 where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import S4Propositions
import S4Derivations as S4


--------------------------------------------------------------------------------


infix 3 _⊢_valid[_]
data _⊢_valid[_] : List Assert → Prop → List Prop → Set
  where
    vz : ∀ {A Δ Γ} → Δ ⊢ A valid[ Γ , A ]

    wk : ∀ {A B Δ Γ} → Δ ⊢ A valid[ Γ ]
                     → Δ ⊢ A valid[ Γ , B ]

    cut : ∀ {A B Δ Γ} → Δ ⊢ A valid[ Γ ] → Δ ⊢ B valid[ Γ , A ]
                      → Δ ⊢ B valid[ Γ ]

    lam : ∀ {A B Δ Γ} → Δ ⊢ B valid[ Γ , A ]
                      → Δ ⊢ A ⊃ B valid[ Γ ]

    unlam : ∀ {A B Δ Γ} → Δ ⊢ A ⊃ B valid[ Γ ]
                        → Δ ⊢ B valid[ Γ , A ]

    mvz : ∀ {A Δ Γ} → Δ , ⟪⊫ A ⟫ ⊢ A valid[ Γ ]

    mwk : ∀ {A B Δ Γ} → Δ ⊢ A valid[ Γ ]
                      → Δ , ⟪⊫ B ⟫ ⊢ A valid[ Γ ]

    mcut : ∀ {Δ Γ A B} → Δ ⊢ A valid[ ∙ ] → Δ , ⟪⊫ A ⟫ ⊢ B valid[ Γ ]
                       → Δ ⊢ B valid[ Γ ]

    box : ∀ {A Δ Γ} → Δ ⊢ A valid[ ∙ ]
                    → Δ ⊢ □ A valid[ Γ ]

    unbox : ∀ {A Δ Γ} → Δ ⊢ □ A valid[ Γ ]
                      → Δ ⊢ A valid[ Γ ]


--------------------------------------------------------------------------------


var : ∀ {A Δ Γ} → Γ ∋ A
                → Δ ⊢ A valid[ Γ ]
var zero    = vz
var (suc i) = wk (var i)


app : ∀ {A B Δ Γ} → Δ ⊢ A ⊃ B valid[ Γ ] → Δ ⊢ A valid[ Γ ]
                  → Δ ⊢ B valid[ Γ ]
app 𝒟 ℰ = cut ℰ (unlam 𝒟)


mvar : ∀ {A Δ Γ} → Δ ∋ ⟪⊫ A ⟫
                 → Δ ⊢ A valid[ Γ ]
mvar zero    = mvz
mvar (suc i) = mwk (mvar i)


-- NOTE: Problematic

-- letbox : ∀ {A B Δ Γ} → Δ ⊢ □ A valid[ Γ ] → Δ , ⟪⊫ A ⟫ ⊢ B valid[ Γ ]
--                      → Δ ⊢ B valid[ Γ ]
-- letbox 𝒟 ℰ = {!!}


-- NOTE: Local completeness of □; problematic

-- rebox : ∀ {Δ Γ A} → Δ ⊢ □ A valid[ Γ ]
--                   → Δ ⊢ □ A valid[ Γ ]
-- rebox 𝒟 = letbox 𝒟 (box mvz)


-- NOTE: Local soundness of □; problematic

-- pseudomcut : ∀ {Δ Γ A B} → Δ ⊢ A valid[ ∙ ] → Δ , ⟪⊫ A ⟫ ⊢ B valid[ Γ ]
--                          → Δ ⊢ B valid[ Γ ]
-- pseudomcut 𝒟 ℰ = letbox (box 𝒟) ℰ


--------------------------------------------------------------------------------


↓ : ∀ {Δ Γ A} → Δ ⊢ A valid[ Γ ]
              → Δ S4.⊢ A valid[ Γ ]
↓ vz         = S4.vz
↓ (wk 𝒟)     = S4.wk (↓ 𝒟)
↓ (cut 𝒟 ℰ)  = S4.cut (↓ 𝒟) (↓ ℰ)
↓ (lam 𝒟)    = S4.lam (↓ 𝒟)
↓ (unlam 𝒟)  = S4.unlam (↓ 𝒟)
↓ mvz        = S4.mvz
↓ (mwk 𝒟)    = S4.mwk (↓ 𝒟)
↓ (mcut 𝒟 ℰ) = S4.mcut (↓ 𝒟) (↓ ℰ)
↓ (box 𝒟)    = S4.box (↓ 𝒟)
↓ (unbox 𝒟)  = S4.unbox (↓ 𝒟)


-- NOTE: Problematic

-- ↑ : ∀ {Δ Γ A} → Δ S4.⊢ A valid[ Γ ]
--               → Δ ⊢ A valid[ Γ ]
-- ↑ (S4.var i)      = var i
-- ↑ (S4.lam 𝒟)      = lam (↑ 𝒟)
-- ↑ (S4.app 𝒟 ℰ)    = app (↑ 𝒟) (↑ ℰ)
-- ↑ (S4.mvar i)     = mvar i
-- ↑ (S4.box 𝒟)      = box (↑ 𝒟)
-- ↑ (S4.letbox 𝒟 ℰ) = letbox (↑ 𝒟) (↑ ℰ)


--------------------------------------------------------------------------------
