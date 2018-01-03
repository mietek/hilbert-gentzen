{-# OPTIONS --rewriting #-}

module VecLemmas where

open import Prelude
open import Fin
open import FinLemmas
open import Vec


--------------------------------------------------------------------------------
{-

                              id⊇ ∘⊇ η ≡ η                                      lid-∘⊇
                              η ∘⊇ id⊇ ≡ η                                      rid-∘⊇
                      (η₁ ∘⊇ η₂) ∘⊇ η₃ ≡ η₁ ∘⊇ (η₂ ∘⊇ η₃)                       assoc-∘⊇

                            ren∋ id⊇ 𝒾 ≡ 𝒾                                      id-ren∋
                     ren∋ (η₁ ∘⊇ η₂) 𝒾 ≡ ren∋ η₂ (ren∋ η₁ 𝒾)                    comp-ren∋

-}
--------------------------------------------------------------------------------


{-# REWRITE lid-∘≥ #-}
lid-∘⊇ : ∀ {X n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′}
                      → (η : Ξ′ ⊇⟨ e ⟩ Ξ)
                      → id⊇ ∘⊇ η ≡ η
lid-∘⊇ done     = refl
lid-∘⊇ (drop η) = drop & lid-∘⊇ η
lid-∘⊇ (keep η) = keep & lid-∘⊇ η


{-# REWRITE rid-∘≥ #-}
rid-∘⊇ : ∀ {X n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′}
                      → (η : Ξ′ ⊇⟨ e ⟩ Ξ)
                      → η ∘⊇ id⊇ ≡ η
rid-∘⊇ done     = refl
rid-∘⊇ (drop η) = drop & rid-∘⊇ η
rid-∘⊇ (keep η) = keep & rid-∘⊇ η


{-# REWRITE assoc-∘≥ #-}
assoc-∘⊇ : ∀ {X n n′ n″ n‴ e₁ e₂ e₃} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {Ξ″ : Vec X n″} {Ξ‴ : Vec X n‴}
                                     → (η₁ : Ξ′ ⊇⟨ e₁ ⟩ Ξ) (η₂ : Ξ″ ⊇⟨ e₂ ⟩ Ξ′) (η₃ : Ξ‴ ⊇⟨ e₃ ⟩ Ξ″)
                                     → (η₁ ∘⊇ η₂) ∘⊇ η₃ ≡ η₁ ∘⊇ (η₂ ∘⊇ η₃)
assoc-∘⊇ η₁        η₂        done      = refl
assoc-∘⊇ η₁        η₂        (drop η₃) = drop & assoc-∘⊇ η₁ η₂ η₃
assoc-∘⊇ η₁        (drop η₂) (keep η₃) = drop & assoc-∘⊇ η₁ η₂ η₃
assoc-∘⊇ (drop η₁) (keep η₂) (keep η₃) = drop & assoc-∘⊇ η₁ η₂ η₃
assoc-∘⊇ (keep η₁) (keep η₂) (keep η₃) = keep & assoc-∘⊇ η₁ η₂ η₃


--------------------------------------------------------------------------------


{-# REWRITE id-renF #-}
id-ren∋ : ∀ {X A n i} → {Ξ : Vec X n}
                      → (𝒾 : Ξ ∋⟨ i ⟩ A)
                      → ren∋ id⊇ 𝒾 ≡ 𝒾
id-ren∋ zero    = refl
id-ren∋ (suc 𝒾) = suc & id-ren∋ 𝒾


{-# REWRITE comp-renF #-}
comp-ren∋ : ∀ {X A n n′ n″ e₁ e₂ i} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {Ξ″ : Vec X n″}
                                    → (η₁ : Ξ′ ⊇⟨ e₁ ⟩ Ξ) (η₂ : Ξ″ ⊇⟨ e₂ ⟩ Ξ′) (𝒾 : Ξ ∋⟨ i ⟩ A)
                                    → ren∋ (η₁ ∘⊇ η₂) 𝒾 ≡ ren∋ η₂ (ren∋ η₁ 𝒾) 
comp-ren∋ η₁        done      𝒾       = refl
comp-ren∋ η₁        (drop η₂) 𝒾       = suc & comp-ren∋ η₁ η₂ 𝒾
comp-ren∋ (drop η₁) (keep η₂) 𝒾       = suc & comp-ren∋ η₁ η₂ 𝒾
comp-ren∋ (keep η₁) (keep η₂) zero    = refl
comp-ren∋ (keep η₁) (keep η₂) (suc 𝒾) = suc & comp-ren∋ η₁ η₂ 𝒾


--------------------------------------------------------------------------------
