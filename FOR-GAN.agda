----------------------------------------------------------------------------------------------------

-- properties of first-order renamings

module FOR-GAN {𝓍} {X : Set 𝓍} where

open import FOR public
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
        ; ◅ssa = λ ρ″ ρ′ ρ → ass⊑ ρ ρ′ ρ″ ⁻¹
        }

⟪⊒⟫ : Category 𝓍 𝓍
⟪⊒⟫ = ⟪⊑⟫ ᵒᵖ

module _ (⚠ : FunExt) where
  ψren∋ : X → Presheaf ⟪⊒⟫ 𝓍
  ψren∋ A = record
              { ƒObj = _∋ A
              ; ƒ    = ren∋
              ; idƒ  = ⚠ idren∋
              ; _∘ƒ_ = λ ρ′ ρ → ⚠ (compren∋ ρ′ ρ)
              }


----------------------------------------------------------------------------------------------------
