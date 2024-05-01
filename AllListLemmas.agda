{-# OPTIONS --rewriting #-}

module AllListLemmas where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList


--------------------------------------------------------------------------------
{-
                      get (gets ξ η) i ≡ (get ξ ∘ ren∋ η) i                     comp-get-ren∋

                             gets ξ id ≡ ξ                                      id-gets
                      gets ξ (η₁ ∘ η₂) ≡ gets (gets ξ η₂) η₁                    comp-gets
                                                                                𝐠𝐞𝐭𝐬

                            id⊇◇ ∘⊇◇ 𝜂 ≡ 𝜂                                      lid∘⊇◇
                            𝜂 ∘⊇◇ id⊇◇ ≡ 𝜂                                      rid∘⊇◇
                    (𝜂₁ ∘⊇◇ 𝜂₂) ∘⊇◇ 𝜂₃ ≡ 𝜂₁ ∘⊇◇ (𝜂₂ ∘⊇◇ 𝜂₃)                     assoc∘⊇◇
                                                                                𝐎𝐏𝐄◇

                          ren∋◇ id⊇◇ 𝑖 ≡ 𝑖                                      id-ren∋◇
                   ren∋◇ (𝜂₁ ∘⊇◇ 𝜂₂) 𝑖 ≡ (ren∋◇ 𝜂₂ ∘ ren∋◇ 𝜂₁) 𝑖                comp-ren∋◇
                                                                                𝐫𝐞𝐧∋◇
-}
--------------------------------------------------------------------------------


comp-get-ren∋ : ∀ {X P A} → {Ξ Ξ′ : List X}
                          → (ξ : All P Ξ′) (η : Ξ′ ⊇ Ξ) (i : Ξ ∋ A)
                          → get (gets ξ η) i ≡ (get ξ ∘ ren∋ η) i
comp-get-ren∋ ∙       done     ()
comp-get-ren∋ (ξ , b) (drop η) i       = comp-get-ren∋ ξ η i
comp-get-ren∋ (ξ , a) (keep η) zero    = refl
comp-get-ren∋ (ξ , b) (keep η) (suc i) = comp-get-ren∋ ξ η i


--------------------------------------------------------------------------------


id-gets : ∀ {X P} → {Ξ : List X}
                  → (ξ : All P Ξ)
                  → gets ξ id ≡ ξ
id-gets ∙       = refl
id-gets (ξ , a) = (_, a) & id-gets ξ


comp-gets : ∀ {X P} → {Ξ Ξ′ Ξ″ : List X}
                    → (ξ : All P Ξ″) (η₁ : Ξ′ ⊇ Ξ) (η₂ : Ξ″ ⊇ Ξ′)
                    → gets ξ (η₁ ∘ η₂) ≡ gets (gets ξ η₂) η₁
comp-gets ∙       η₁        done      = refl
comp-gets (ξ , b) η₁        (drop η₂) = comp-gets ξ η₁ η₂
comp-gets (ξ , b) (drop η₁) (keep η₂) = comp-gets ξ η₁ η₂
comp-gets (ξ , a) (keep η₁) (keep η₂) = (_, a) & comp-gets ξ η₁ η₂


𝐠𝐞𝐭𝐬 : ∀ {X P} → Presheaf (Opposite (𝐎𝐏𝐄 {X})) (All P)
𝐠𝐞𝐭𝐬 = record
         { ℱ     = flip gets
         ; idℱ   = funext! id-gets
         ; compℱ = \ η₁ η₂ → funext! (\ ξ → comp-gets ξ η₂ η₁)
         }


--------------------------------------------------------------------------------


{-# REWRITE lid∘⊇ #-}
lid∘⊇◇ : ∀ {X P} → {Ξ Ξ′ : List X} {η : Ξ′ ⊇ Ξ}
                    {ξ : All P Ξ} {ξ′ : All P Ξ′}
                 → (𝜂 : ξ′ ⊇◇⟨ η ⟩ ξ)
                 → id⊇◇ ∘⊇◇ 𝜂 ≡ 𝜂
lid∘⊇◇ done     = refl
lid∘⊇◇ (drop 𝜂) = drop & lid∘⊇◇ 𝜂
lid∘⊇◇ (keep 𝜂) = keep & lid∘⊇◇ 𝜂


{-# REWRITE rid∘⊇ #-}
rid∘⊇◇ : ∀ {X P} → {Ξ Ξ′ : List X} {η : Ξ′ ⊇ Ξ} {ξ : All P Ξ} {ξ′ : All P Ξ′}
                 → (𝜂 : ξ′ ⊇◇⟨ η ⟩ ξ)
                 → 𝜂 ∘⊇◇ id⊇◇ ≡ 𝜂
rid∘⊇◇ done     = refl
rid∘⊇◇ (drop 𝜂) = drop & rid∘⊇◇ 𝜂
rid∘⊇◇ (keep 𝜂) = keep & rid∘⊇◇ 𝜂


{-# REWRITE assoc∘⊇ #-}
assoc∘⊇◇ : ∀ {X P} → {Ξ Ξ′ Ξ″ Ξ‴ : List X} {η₁ : Ξ′ ⊇ Ξ} {η₂ : Ξ″ ⊇ Ξ′} {η₃ : Ξ‴ ⊇ Ξ″}
                      {ξ : All P Ξ} {ξ′ : All P Ξ′} {ξ″ : All P Ξ″} {ξ‴ : All P Ξ‴}
                   → (𝜂₁ : ξ′ ⊇◇⟨ η₁ ⟩ ξ) (𝜂₂ : ξ″ ⊇◇⟨ η₂ ⟩ ξ′) (𝜂₃ : ξ‴ ⊇◇⟨ η₃ ⟩ ξ″)
                   → (𝜂₁ ∘⊇◇ 𝜂₂) ∘⊇◇ 𝜂₃ ≡ 𝜂₁ ∘⊇◇ (𝜂₂ ∘⊇◇ 𝜂₃)
assoc∘⊇◇ 𝜂₁        𝜂₂        done      = refl
assoc∘⊇◇ 𝜂₁        𝜂₂        (drop 𝜂₃) = drop & assoc∘⊇◇ 𝜂₁ 𝜂₂ 𝜂₃
assoc∘⊇◇ 𝜂₁        (drop 𝜂₂) (keep 𝜂₃) = drop & assoc∘⊇◇ 𝜂₁ 𝜂₂ 𝜂₃
assoc∘⊇◇ (drop 𝜂₁) (keep 𝜂₂) (keep 𝜂₃) = drop & assoc∘⊇◇ 𝜂₁ 𝜂₂ 𝜂₃
assoc∘⊇◇ (keep 𝜂₁) (keep 𝜂₂) (keep 𝜂₃) = keep & assoc∘⊇◇ 𝜂₁ 𝜂₂ 𝜂₃


instance
  𝐎𝐏𝐄◇ : ∀ {X P} → Category (Σ (List X) (All P))
                             (\ { (Ξ′ , ξ′) (Ξ , ξ) →
                               Σ (Ξ′ ⊇ Ξ) (\ η → ξ′ ⊇◇⟨ η ⟩ ξ) })
  𝐎𝐏𝐄◇ = record
           { id     = id , id⊇◇
           ; _∘_    = \ { (η₁ , 𝜂₁) (η₂ , 𝜂₂) → η₁ ∘ η₂ , 𝜂₁ ∘⊇◇ 𝜂₂ }
           ; lid∘   = \ { (η , 𝜂) → (η ,_) & lid∘⊇◇ 𝜂 }
           ; rid∘   = \ { (η , 𝜂) → (η ,_) & rid∘⊇◇ 𝜂 }
           ; assoc∘ = \ { (η₁ , 𝜂₁) (η₂ , 𝜂₂) (η₃ , 𝜂₃) →
                        ((η₁ ∘ η₂) ∘ η₃ ,_) & assoc∘⊇◇ 𝜂₁ 𝜂₂ 𝜂₃ }
           }


--------------------------------------------------------------------------------


{-# REWRITE id-ren∋ #-}
id-ren∋◇ : ∀ {X P A} → {Ξ : List X} {i : Ξ ∋ A} {a : P A} {ξ : All P Ξ}
                     → (𝑖 : ξ ∋◇⟨ i ⟩ a)
                     → ren∋◇ id⊇◇ 𝑖 ≡ 𝑖
id-ren∋◇ zero    = refl
id-ren∋◇ (suc 𝑖) = suc & id-ren∋◇ 𝑖


{-# REWRITE comp-ren∋ #-}
comp-ren∋◇ : ∀ {X P A} → {Ξ Ξ′ Ξ″ : List X} {η₁ : Ξ′ ⊇ Ξ} {η₂ : Ξ″ ⊇ Ξ′} {i : Ξ ∋ A}
                          {a : P A} {ξ : All P Ξ} {ξ′ : All P Ξ′} {ξ″ : All P Ξ″}
                       → (𝜂₁ : ξ′ ⊇◇⟨ η₁ ⟩ ξ) (𝜂₂ : ξ″ ⊇◇⟨ η₂ ⟩ ξ′) (𝑖 : ξ ∋◇⟨ i ⟩ a)
                       → ren∋◇ (𝜂₁ ∘⊇◇ 𝜂₂) 𝑖 ≡ (ren∋◇ 𝜂₂ ∘ ren∋◇ 𝜂₁) 𝑖
comp-ren∋◇ 𝜂₁        done      𝑖       = refl
comp-ren∋◇ 𝜂₁        (drop 𝜂₂) 𝑖       = suc & comp-ren∋◇ 𝜂₁ 𝜂₂ 𝑖
comp-ren∋◇ (drop 𝜂₁) (keep 𝜂₂) 𝑖       = suc & comp-ren∋◇ 𝜂₁ 𝜂₂ 𝑖
comp-ren∋◇ (keep 𝜂₁) (keep 𝜂₂) zero    = refl
comp-ren∋◇ (keep 𝜂₁) (keep 𝜂₂) (suc 𝑖) = suc & comp-ren∋◇ 𝜂₁ 𝜂₂ 𝑖


𝐫𝐞𝐧∋◇ : ∀ {X P A} → {a : P A}
                  → Presheaf (𝐎𝐏𝐄◇ {X} {P})
                              (\ { (Ξ , ξ) →
                                Σ (Ξ ∋ A) (\ i → ξ ∋◇⟨ i ⟩ a) })
𝐫𝐞𝐧∋◇ = record
          { ℱ     = \ { (η , 𝜂) (i , 𝑖) → ren∋ η i , ren∋◇ 𝜂 𝑖 }
          ; idℱ   = funext! (\ { (i , 𝑖) → (_ List².⨾_) & id-ren∋◇ 𝑖 })
          ; compℱ = \ { (η₁ , 𝜂₁) (η₂ , 𝜂₂) →
                      funext! (\ { (i , 𝑖) → (_ List².⨾_) & comp-ren∋◇ 𝜂₁ 𝜂₂ 𝑖 }) }
          }


--------------------------------------------------------------------------------
