{-# OPTIONS --rewriting #-}

module AllListLemmas where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList


--------------------------------------------------------------------------------
{-
                      get (gets ξ η) 𝒾 ≡ (get ξ ∘ ren∋ η) 𝒾                     comp-get-ren∋

                            gets ξ id⊇ ≡ ξ                                      id-gets   ⎱ 𝐠𝐞𝐭𝐬
                      gets ξ (η₁ ∘ η₂) ≡ gets (gets ξ η₂) η₁                    comp-gets ⎰

                            id⊇◇ ∘⊇◇ 𝛈 ≡ 𝛈                                      lid∘⊇◇   ⎫
                            𝛈 ∘⊇◇ id⊇◇ ≡ 𝛈                                      rid∘⊇◇   ⎬ 𝐎𝐏𝐄′
                    (𝛈₁ ∘⊇◇ 𝛈₂) ∘⊇◇ 𝛈₃ ≡ 𝛈₁ ∘⊇◇ (𝛈₂ ∘⊇◇ 𝛈₃)                     assoc∘⊇◇ ⎭

                          ren∋◇ id⊇◇ 𝓲 ≡ 𝓲                                      id-ren∋◇   ⎱ 𝐫𝐞𝐧∋◇
                   ren∋◇ (𝛈₁ ∘⊇◇ 𝛈₂) 𝓲 ≡ (ren∋◇ 𝛈₂ ∘ ren∋◇ 𝛈₁) 𝓲                comp-ren∋◇ ⎰
-}
--------------------------------------------------------------------------------


comp-get-ren∋ : ∀ {X P A} → {Ξ Ξ′ : List X}
                          → (ξ : All P Ξ′) (η : Ξ′ ⊇ Ξ) (𝒾 : Ξ ∋ A)
                          → get (gets ξ η) 𝒾 ≡ (get ξ ∘ ren∋ η) 𝒾
comp-get-ren∋ ∙       done     ()
comp-get-ren∋ (ξ , b) (drop η) 𝒾       = comp-get-ren∋ ξ η 𝒾
comp-get-ren∋ (ξ , a) (keep η) zero    = refl
comp-get-ren∋ (ξ , b) (keep η) (suc 𝒾) = comp-get-ren∋ ξ η 𝒾


--------------------------------------------------------------------------------


id-gets : ∀ {X P} → {Ξ : List X}
                  → (ξ : All P Ξ)
                  → gets ξ id⊇ ≡ ξ
id-gets ∙       = refl
id-gets (ξ , a) = (_, a) & id-gets ξ


comp-gets : ∀ {X P} → {Ξ Ξ′ Ξ″ : List X}
                    → (ξ : All P Ξ″) (η₁ : Ξ′ ⊇ Ξ) (η₂ : Ξ″ ⊇ Ξ′)
                    → gets ξ (η₁ ∘ η₂) ≡ gets (gets ξ η₂) η₁
comp-gets ∙       η₁        done      = refl
comp-gets (ξ , b) η₁        (drop η₂) = comp-gets ξ η₁ η₂
comp-gets (ξ , b) (drop η₁) (keep η₂) = comp-gets ξ η₁ η₂
comp-gets (ξ , a) (keep η₁) (keep η₂) = (_, a) & comp-gets ξ η₁ η₂


𝐠𝐞𝐭𝐬 : ∀ {X P} → Presheaf (Opposite (𝐎𝐏𝐄 {X})) (All P) (flip gets)
𝐠𝐞𝐭𝐬 = record
         { idℱ   = funext! id-gets
         ; compℱ = \ η₁ η₂ → funext! (\ ξ → comp-gets ξ η₂ η₁)
         }


--------------------------------------------------------------------------------


{-# REWRITE lid∘⊇ #-}
lid∘⊇◇ : ∀ {X P} → {Ξ Ξ′ : List X} {η : Ξ′ ⊇ Ξ}
                    {ξ : All P Ξ} {ξ′ : All P Ξ′}
                 → (𝛈 : ξ′ ⊇◇⟨ η ⟩ ξ)
                 → id⊇◇ ∘⊇◇ 𝛈 ≡ 𝛈
lid∘⊇◇ done     = refl
lid∘⊇◇ (drop 𝛈) = drop & lid∘⊇◇ 𝛈
lid∘⊇◇ (keep 𝛈) = keep & lid∘⊇◇ 𝛈


{-# REWRITE rid∘⊇ #-}
rid∘⊇◇ : ∀ {X P} → {Ξ Ξ′ : List X} {η : Ξ′ ⊇ Ξ} {ξ : All P Ξ} {ξ′ : All P Ξ′}
                 → (𝛈 : ξ′ ⊇◇⟨ η ⟩ ξ)
                 → 𝛈 ∘⊇◇ id⊇◇ ≡ 𝛈
rid∘⊇◇ done     = refl
rid∘⊇◇ (drop 𝛈) = drop & rid∘⊇◇ 𝛈
rid∘⊇◇ (keep 𝛈) = keep & rid∘⊇◇ 𝛈


{-# REWRITE assoc∘⊇ #-}
assoc∘⊇◇ : ∀ {X P} → {Ξ Ξ′ Ξ″ Ξ‴ : List X} {η₁ : Ξ′ ⊇ Ξ} {η₂ : Ξ″ ⊇ Ξ′} {η₃ : Ξ‴ ⊇ Ξ″}
                      {ξ : All P Ξ} {ξ′ : All P Ξ′} {ξ″ : All P Ξ″} {ξ‴ : All P Ξ‴}
                   → (𝛈₁ : ξ′ ⊇◇⟨ η₁ ⟩ ξ) (𝛈₂ : ξ″ ⊇◇⟨ η₂ ⟩ ξ′) (𝛈₃ : ξ‴ ⊇◇⟨ η₃ ⟩ ξ″)
                   → (𝛈₁ ∘⊇◇ 𝛈₂) ∘⊇◇ 𝛈₃ ≡ 𝛈₁ ∘⊇◇ (𝛈₂ ∘⊇◇ 𝛈₃)
assoc∘⊇◇ 𝛈₁        𝛈₂        done      = refl
assoc∘⊇◇ 𝛈₁        𝛈₂        (drop 𝛈₃) = drop & assoc∘⊇◇ 𝛈₁ 𝛈₂ 𝛈₃
assoc∘⊇◇ 𝛈₁        (drop 𝛈₂) (keep 𝛈₃) = drop & assoc∘⊇◇ 𝛈₁ 𝛈₂ 𝛈₃
assoc∘⊇◇ (drop 𝛈₁) (keep 𝛈₂) (keep 𝛈₃) = drop & assoc∘⊇◇ 𝛈₁ 𝛈₂ 𝛈₃
assoc∘⊇◇ (keep 𝛈₁) (keep 𝛈₂) (keep 𝛈₃) = keep & assoc∘⊇◇ 𝛈₁ 𝛈₂ 𝛈₃


instance
  𝐎𝐏𝐄′ : ∀ {X P} → Category (Σ (List X) (All P))
                             (\ { (Ξ′ , ξ′) (Ξ , ξ) →
                               Σ (Ξ′ ⊇ Ξ) (\ η → ξ′ ⊇◇⟨ η ⟩ ξ) })
  𝐎𝐏𝐄′ = record
           { id     = id⊇ , id⊇◇
           ; _∘_    = \ { (η₁ , 𝛈₁) (η₂ , 𝛈₂) → η₁ ∘⊇ η₂ , 𝛈₁ ∘⊇◇ 𝛈₂ }
           ; lid∘   = \ { (η , 𝛈) → (η ,_) & lid∘⊇◇ 𝛈 }
           ; rid∘   = \ { (η , 𝛈) → (η ,_) & rid∘⊇◇ 𝛈 }
           ; assoc∘ = \ { (η₁ , 𝛈₁) (η₂ , 𝛈₂) (η₃ , 𝛈₃) →
                        ((η₁ ∘⊇ η₂) ∘⊇ η₃ ,_) & assoc∘⊇◇ 𝛈₁ 𝛈₂ 𝛈₃ }
           }


--------------------------------------------------------------------------------


{-# REWRITE id-ren∋ #-}
id-ren∋◇ : ∀ {X P A} → {Ξ : List X} {𝒾 : Ξ ∋ A} {a : P A} {ξ : All P Ξ}
                     → (𝓲 : ξ ∋◇⟨ 𝒾 ⟩ a)
                     → ren∋◇ id⊇◇ 𝓲 ≡ 𝓲
id-ren∋◇ zero    = refl
id-ren∋◇ (suc 𝓲) = suc & id-ren∋◇ 𝓲


{-# REWRITE comp-ren∋ #-}
comp-ren∋◇ : ∀ {X P A} → {Ξ Ξ′ Ξ″ : List X} {η₁ : Ξ′ ⊇ Ξ} {η₂ : Ξ″ ⊇ Ξ′} {𝒾 : Ξ ∋ A}
                          {a : P A} {ξ : All P Ξ} {ξ′ : All P Ξ′} {ξ″ : All P Ξ″}
                       → (𝛈₁ : ξ′ ⊇◇⟨ η₁ ⟩ ξ) (𝛈₂ : ξ″ ⊇◇⟨ η₂ ⟩ ξ′) (𝓲 : ξ ∋◇⟨ 𝒾 ⟩ a)
                       → ren∋◇ (𝛈₁ ∘⊇◇ 𝛈₂) 𝓲 ≡ (ren∋◇ 𝛈₂ ∘ ren∋◇ 𝛈₁) 𝓲
comp-ren∋◇ 𝛈₁        done      𝓲       = refl
comp-ren∋◇ 𝛈₁        (drop 𝛈₂) 𝓲       = suc & comp-ren∋◇ 𝛈₁ 𝛈₂ 𝓲
comp-ren∋◇ (drop 𝛈₁) (keep 𝛈₂) 𝓲       = suc & comp-ren∋◇ 𝛈₁ 𝛈₂ 𝓲
comp-ren∋◇ (keep 𝛈₁) (keep 𝛈₂) zero    = refl
comp-ren∋◇ (keep 𝛈₁) (keep 𝛈₂) (suc 𝓲) = suc & comp-ren∋◇ 𝛈₁ 𝛈₂ 𝓲


𝐫𝐞𝐧∋◇ : ∀ {X P A} → {a : P A}
                  → Presheaf (𝐎𝐏𝐄′ {X} {P})
                              (\ { (Ξ , ξ) →
                                Σ (Ξ ∋ A) (\ 𝒾 → ξ ∋◇⟨ 𝒾 ⟩ a) })
                              (\ { (η , 𝛈) (i , 𝓲) → ren∋ η i , ren∋◇ 𝛈 𝓲 })
𝐫𝐞𝐧∋◇ = record
          { idℱ   = funext! (\ { (𝒾 , 𝓲) →
                      (ren∋ id⊇ 𝒾 ,_) & id-ren∋◇ 𝓲 })
          ; compℱ = \ { (η₁ , 𝛈₁) (η₂ , 𝛈₂) →
                      funext! (\ { (𝒾 , 𝓲) →
                        (ren∋ (η₁ ∘⊇ η₂) 𝒾 ,_) & comp-ren∋◇ 𝛈₁ 𝛈₂ 𝓲 }) }
          }


--------------------------------------------------------------------------------
