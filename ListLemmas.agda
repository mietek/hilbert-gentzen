module ListLemmas where

open import Prelude
open import Fin
open import List


--------------------------------------------------------------------------------
{-

                              id⊇ ∘⊇ η ≡ η                                      lid-∘⊇
                              η ∘⊇ id⊇ ≡ η                                      rid-∘⊇
                      (η₁ ∘⊇ η₂) ∘⊇ η₃ ≡ η₁ ∘⊇ (η₂ ∘⊇ η₃)                       assoc-∘⊇

                            ren∋ id⊇ 𝒾 ≡ 𝒾                                      id-ren∋
                     ren∋ (η₁ ∘⊇ η₂) 𝒾 ≡ ren∋ η₂ (ren∋ η₁ 𝒾)                    comp-ren∋

-}
--------------------------------------------------------------------------------


lid-∘⊇ : ∀ {X} → {Ξ Ξ′ : List X}
               → (η : Ξ′ ⊇ Ξ)
               → id⊇ ∘⊇ η ≡ η
lid-∘⊇ done     = refl
lid-∘⊇ (drop η) = drop & lid-∘⊇ η
lid-∘⊇ (keep η) = keep & lid-∘⊇ η


rid-∘⊇ : ∀ {X} → {Ξ Ξ′ : List X}
               → (η : Ξ′ ⊇ Ξ)
               → η ∘⊇ id⊇ ≡ η
rid-∘⊇ done     = refl
rid-∘⊇ (drop η) = drop & rid-∘⊇ η
rid-∘⊇ (keep η) = keep & rid-∘⊇ η


assoc-∘⊇ : ∀ {X} → {Ξ Ξ′ Ξ″ Ξ‴ : List X}
                 → (η₁ : Ξ′ ⊇ Ξ) (η₂ : Ξ″ ⊇ Ξ′) (η₃ : Ξ‴ ⊇ Ξ″)
                 → (η₁ ∘⊇ η₂) ∘⊇ η₃ ≡ η₁ ∘⊇ (η₂ ∘⊇ η₃)
assoc-∘⊇ η₁        η₂        done      = refl
assoc-∘⊇ η₁        η₂        (drop η₃) = drop & assoc-∘⊇ η₁ η₂ η₃
assoc-∘⊇ η₁        (drop η₂) (keep η₃) = drop & assoc-∘⊇ η₁ η₂ η₃
assoc-∘⊇ (drop η₁) (keep η₂) (keep η₃) = drop & assoc-∘⊇ η₁ η₂ η₃
assoc-∘⊇ (keep η₁) (keep η₂) (keep η₃) = keep & assoc-∘⊇ η₁ η₂ η₃


--------------------------------------------------------------------------------


id-ren∋ : ∀ {X A} → {Ξ : List X}
                  → (𝒾 : Ξ ∋ A)
                  → ren∋ id⊇ 𝒾 ≡ 𝒾
id-ren∋ zero    = refl
id-ren∋ (suc 𝒾) = suc & id-ren∋ 𝒾


comp-ren∋ : ∀ {X A} → {Ξ Ξ′ Ξ″ : List X}
                    → (η₁ : Ξ′ ⊇ Ξ) (η₂ : Ξ″ ⊇ Ξ′) (𝒾 : Ξ ∋ A)
                    → ren∋ (η₁ ∘⊇ η₂) 𝒾 ≡ ren∋ η₂ (ren∋ η₁ 𝒾)
comp-ren∋ η₁        done      𝒾       = refl
comp-ren∋ η₁        (drop η₂) 𝒾       = suc & comp-ren∋ η₁ η₂ 𝒾
comp-ren∋ (drop η₁) (keep η₂) 𝒾       = suc & comp-ren∋ η₁ η₂ 𝒾
comp-ren∋ (keep η₁) (keep η₂) zero    = refl
comp-ren∋ (keep η₁) (keep η₂) (suc 𝒾) = suc & comp-ren∋ η₁ η₂ 𝒾


--------------------------------------------------------------------------------

