module FullS4EmbeddingOfFullIPL where

open import Prelude
open import List
open import FullS4Propositions
open import FullS4StandardDerivations
import FullIPLPropositions as IPL
import FullIPLDerivations as IPL


--------------------------------------------------------------------------------


↑ₚ : IPL.Prop → Prop
↑ₚ (IPL.ι P)   = ι P
↑ₚ (A IPL.⊃ B) = ↑ₚ A ⊃ ↑ₚ B
↑ₚ (A IPL.∧ B) = ↑ₚ A ∧ ↑ₚ B
↑ₚ IPL.⊤      = ⊤
↑ₚ IPL.⊥      = ⊥
↑ₚ (A IPL.∨ B) = ↑ₚ A ∨ ↑ₚ B


↑ₐ : IPL.Prop → Assert
↑ₐ A = ⟪⊫ ↑ₚ A ⟫


↑ₚₛ : List IPL.Prop → List Prop
↑ₚₛ Γ = map ↑ₚ Γ


↑ₐₛ : List IPL.Prop → List Assert
↑ₐₛ Γ = map ↑ₐ Γ


↑∋ₚ : ∀ {Γ A} → Γ ∋ A
              → ↑ₚₛ Γ ∋ ↑ₚ A
↑∋ₚ zero    = zero
↑∋ₚ (suc i) = suc (↑∋ₚ i)


↑∋ₐ : ∀ {Γ A} → Γ ∋ A
              → ↑ₐₛ Γ ∋ ↑ₐ A
↑∋ₐ zero    = zero
↑∋ₐ (suc i) = suc (↑∋ₐ i)


↑ : ∀ {Δ Γ A} → Γ IPL.⊢ A true
              → Δ ⊢ ↑ₚ A valid[ ↑ₚₛ Γ ]
↑ (IPL.var i)      = var (↑∋ₚ i)
↑ (IPL.lam 𝒟)      = lam (↑ 𝒟)
↑ (IPL.app 𝒟 ℰ)    = app (↑ 𝒟) (↑ ℰ)
↑ (IPL.pair 𝒟 ℰ)   = pair (↑ 𝒟) (↑ ℰ)
↑ (IPL.fst 𝒟)      = fst (↑ 𝒟)
↑ (IPL.snd 𝒟)      = snd (↑ 𝒟)
↑ IPL.unit         = unit
↑ (IPL.abort 𝒟)    = abort (↑ 𝒟)
↑ (IPL.inl 𝒟)      = inl (↑ 𝒟)
↑ (IPL.inr 𝒟)      = inr (↑ 𝒟)
↑ (IPL.case 𝒟 ℰ ℱ) = case (↑ 𝒟) (↑ ℰ) (↑ ℱ)


--------------------------------------------------------------------------------


intern : ∀ {Γ A} → Γ IPL.⊢ A true
                 → ↑ₐₛ Γ ⊢ □ (↑ₚ A) valid[ ∙ ]
intern {∙}     𝒟 = box (↑ 𝒟)
intern {Γ , B} 𝒟 = unvau (boxapp (wk (intern (IPL.lam 𝒟))) vz)


--------------------------------------------------------------------------------
