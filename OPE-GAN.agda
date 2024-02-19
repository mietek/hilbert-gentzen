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
        ; ◅ssa = λ ϱ ϱ′ ϱ″ → ass⊑ ϱ″ ϱ′ ϱ ⁻¹
        }

⟪⊒⟫ : Category 𝓍 𝓍
⟪⊒⟫ = ⟪⊑⟫ ᵒᵖ

ƒlift⊑ : X → Functor ⟪⊑⟫ ⟪⊑⟫
ƒlift⊑ B = record
            { ƒObj = _, B
            ; ƒ    = lift⊑
            ; idƒ  = refl
            ; _∘ƒ_ = λ ϱ′ ϱ → refl
            }

νwk⊑ : ∀ (B : X) → NatTrans (ƒId ⟪⊑⟫) (ƒlift⊑ B)
νwk⊑ B = record
           { ν    = λ Γ → wk⊑ id⊑
           ; natν = λ Γ Δ ϱ → wk⊑ & (lid⊑ ϱ ⋮ rid⊑ ϱ ⁻¹)
           }

module _ (⚠ : FunExt) where
  ϖren∋ : X → Presheaf ⟪⊒⟫ 𝓍
  ϖren∋ A = record
              { ƒObj = _∋ A
              ; ƒ    = ren∋
              ; idƒ  = ⚠ idren∋
              ; _∘ƒ_ = λ ϱ′ ϱ → ⚠ (compren∋ ϱ′ ϱ)
              }


----------------------------------------------------------------------------------------------------
