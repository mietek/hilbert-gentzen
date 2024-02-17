----------------------------------------------------------------------------------------------------

-- properties of order-preserving embeddings

module OPE-GAN {𝓍} {X : Set 𝓍} where

open import OPE public
open import GAN public


----------------------------------------------------------------------------------------------------

⟪⊑⟫ : Category 𝓍 𝓍
⟪⊑⟫ = record
        { Obj  = Tsil X
        ; _▻_  = _⊑_
        ; id   = id⊑
        ; _∘_  = _∘⊑_
        ; lid▻ = lid⊑
        ; rid▻ = rid⊑
        ; ass▻ = ass⊑
        ; ◅ssa = λ ρ ρ′ ρ″ → ass⊑ ρ″ ρ′ ρ ⁻¹
        }

⟪⊒⟫ : Category 𝓍 𝓍
⟪⊒⟫ = ⟪⊑⟫ ᵒᵖ

ƒlift⊑ : X → Functor ⟪⊑⟫ ⟪⊑⟫
ƒlift⊑ B = record
            { ƒObj = _, B
            ; ƒ    = lift⊑
            ; idƒ  = refl
            ; _∘ƒ_ = λ ρ′ ρ → refl
            }

ηwk⊑ : ∀ (B : X) → NatTrans (ƒId ⟪⊑⟫) (ƒlift⊑ B)
ηwk⊑ B = record
           { η    = λ Γ → wk⊑ id⊑
           ; natη = λ Γ Δ ρ → wk⊑ & (lid⊑ ρ ⋮ rid⊑ ρ ⁻¹)
           }

module _ (⚠ : FunExt) where
  ψren∋ : X → Presheaf ⟪⊒⟫ 𝓍
  ψren∋ A = record
              { ƒObj = _∋ A
              ; ƒ    = ren∋
              ; idƒ  = ⚠ idren∋
              ; _∘ƒ_ = λ ρ′ ρ → ⚠ (compren∋ ρ′ ρ)
              }


----------------------------------------------------------------------------------------------------
