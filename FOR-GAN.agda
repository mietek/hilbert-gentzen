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
        ; ◅ssa = λ ϱ″ ϱ′ ϱ → ass⊑ ϱ ϱ′ ϱ″ ⁻¹
        }

⟪⊒⟫ : Category 𝓍 𝓍
⟪⊒⟫ = ⟪⊑⟫ ᵒᵖ

module _ (⚠ : FunExt) where
  ϖren∋ : X → Presheaf ⟪⊒⟫ 𝓍
  ϖren∋ A = record
              { ƒObj = _∋ A
              ; ƒ    = ren∋
              ; idƒ  = ⚠ idren∋
              ; _∘ƒ_ = λ ϱ′ ϱ → ⚠ (compren∋ ϱ′ ϱ)
              }


----------------------------------------------------------------------------------------------------
