{-# OPTIONS --rewriting #-}

module AllVecLemmas where

open import Prelude
open import Category
open import Fin
open import FinLemmas
open import Vec
open import VecLemmas
open import AllVec


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


comp-get-ren∋ : ∀ {X P A n n′} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {e : n′ ≥ n} {i : Fin n}
                               → (ξ : All P Ξ′) (η : Ξ′ ⊇⟨ e ⟩ Ξ) (𝒾 : Ξ ∋⟨ i ⟩ A)
                               → get (gets ξ η) 𝒾 ≡ (get ξ ∘ ren∋ η) 𝒾
comp-get-ren∋ ∙       done     ()
comp-get-ren∋ (ξ , b) (drop η) 𝒾       = comp-get-ren∋ ξ η 𝒾
comp-get-ren∋ (ξ , a) (keep η) zero    = refl
comp-get-ren∋ (ξ , b) (keep η) (suc 𝒾) = comp-get-ren∋ ξ η 𝒾


--------------------------------------------------------------------------------


id-gets : ∀ {X P n} → {Ξ : Vec X n}
                    → (ξ : All P Ξ)
                    → gets ξ id⊇ ≡ ξ
id-gets ∙       = refl
id-gets (ξ , a) = (_, a) & id-gets ξ


comp-gets : ∀ {X P n n′ n″ e₁ e₂} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {Ξ″ : Vec X n″}
                                  → (ξ : All P Ξ″) (η₁ : Ξ′ ⊇⟨ e₁ ⟩ Ξ) (η₂ : Ξ″ ⊇⟨ e₂ ⟩ Ξ′)
                                  → gets ξ (η₁ ∘⊇ η₂) ≡ gets (gets ξ η₂) η₁
comp-gets ∙       η₁        done      = refl
comp-gets (ξ , b) η₁        (drop η₂) = comp-gets ξ η₁ η₂
comp-gets (ξ , b) (drop η₁) (keep η₂) = comp-gets ξ η₁ η₂
comp-gets (ξ , a) (keep η₁) (keep η₂) = (_, a) & comp-gets ξ η₁ η₂


𝐠𝐞𝐭𝐬 : ∀ {X P} → Presheaf (Opposite (𝐎𝐏𝐄 {X}))
                           (\ { (n , Ξ) → All P Ξ })
𝐠𝐞𝐭𝐬 = record
         { ℱ     = \ { (e , η) ξ → gets ξ η }
         ; idℱ   = funext! id-gets
         ; compℱ = \ { (e₁ , η₁) (e₂ , η₂) → funext! (\ ξ → comp-gets ξ η₂ η₁) }
         }


--------------------------------------------------------------------------------


{-# REWRITE lid∘⊇ #-}
lid∘⊇◇ : ∀ {X P n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {η : Ξ′ ⊇⟨ e ⟩ Ξ}
                           {ξ : All P Ξ} {ξ′ : All P Ξ′}
                        → (𝛈 : ξ′ ⊇◇⟨ η ⟩ ξ)
                        → id⊇◇ ∘⊇◇ 𝛈 ≡ 𝛈
lid∘⊇◇ done     = refl
lid∘⊇◇ (drop 𝛈) = drop & lid∘⊇◇ 𝛈
lid∘⊇◇ (keep 𝛈) = keep & lid∘⊇◇ 𝛈


{-# REWRITE rid∘⊇ #-}
rid∘⊇◇ : ∀ {X P n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {η : Ξ′ ⊇⟨ e ⟩ Ξ}
                           {ξ : All P Ξ} {ξ′ : All P Ξ′}
                        → (𝛈 : ξ′ ⊇◇⟨ η ⟩ ξ)
                        → 𝛈 ∘⊇◇ id⊇◇ ≡ 𝛈
rid∘⊇◇ done     = refl
rid∘⊇◇ (drop 𝛈) = drop & rid∘⊇◇ 𝛈
rid∘⊇◇ (keep 𝛈) = keep & rid∘⊇◇ 𝛈


{-# REWRITE assoc∘⊇ #-}
assoc∘⊇◇ : ∀ {X P n n′ n″ n‴ e₁ e₂ e₃} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {Ξ″ : Vec X n″} {Ξ‴ : Vec X n‴}
                                          {η₁ : Ξ′ ⊇⟨ e₁ ⟩ Ξ} {η₂ : Ξ″ ⊇⟨ e₂ ⟩ Ξ′} {η₃ : Ξ‴ ⊇⟨ e₃ ⟩ Ξ″}
                                          {ξ : All P Ξ} {ξ′ : All P Ξ′} {ξ″ : All P Ξ″} {ξ‴ : All P Ξ‴}
                                       → (𝛈₁ : ξ′ ⊇◇⟨ η₁ ⟩ ξ) (𝛈₂ : ξ″ ⊇◇⟨ η₂ ⟩ ξ′) (𝛈₃ : ξ‴ ⊇◇⟨ η₃ ⟩ ξ″)
                                       → (𝛈₁ ∘⊇◇ 𝛈₂) ∘⊇◇ 𝛈₃ ≡ 𝛈₁ ∘⊇◇ (𝛈₂ ∘⊇◇ 𝛈₃)
assoc∘⊇◇ 𝛈₁        𝛈₂        done      = refl
assoc∘⊇◇ 𝛈₁        𝛈₂        (drop 𝛈₃) = drop & assoc∘⊇◇ 𝛈₁ 𝛈₂ 𝛈₃
assoc∘⊇◇ 𝛈₁        (drop 𝛈₂) (keep 𝛈₃) = drop & assoc∘⊇◇ 𝛈₁ 𝛈₂ 𝛈₃
assoc∘⊇◇ (drop 𝛈₁) (keep 𝛈₂) (keep 𝛈₃) = drop & assoc∘⊇◇ 𝛈₁ 𝛈₂ 𝛈₃
assoc∘⊇◇ (keep 𝛈₁) (keep 𝛈₂) (keep 𝛈₃) = keep & assoc∘⊇◇ 𝛈₁ 𝛈₂ 𝛈₃


instance
  𝐎𝐏𝐄′ : ∀ {X P} → Category (Σ Nat (\ n → Σ (Vec X n) (All P)))
                             (\ { (n′ , (Ξ′ , ξ′)) (n , (Ξ , ξ)) →
                               Σ (n′ ≥ n) (\ e →
                                 Σ (Ξ′ ⊇⟨ e ⟩ Ξ) (\ η → ξ′ ⊇◇⟨ η ⟩ ξ)) })
  𝐎𝐏𝐄′ = record
           { id     = id , (id⊇ , id⊇◇)
           ; _∘_    = \ { (e₁ , (η₁ , 𝛈₁)) (e₂ , (η₂ , 𝛈₂)) → e₁ ∘ e₂ , (η₁ ∘⊇ η₂ , 𝛈₁ ∘⊇◇ 𝛈₂) }
           ; lid∘   = \ { (e , (η , 𝛈)) → (\ 𝛈′ → e , (η , 𝛈′)) & lid∘⊇◇ 𝛈 }
           ; rid∘   = \ { (e , (η , 𝛈)) → (\ 𝛈′ → e , (η , 𝛈′)) & rid∘⊇◇ 𝛈 }
           ; assoc∘ = \ { (e₁ , (η₁ , 𝛈₁)) (e₂ , (η₂ , 𝛈₂)) (e₃ , (η₃ , 𝛈₃)) →
                        ((\ 𝛈′ → (e₁ ∘ e₂) ∘ e₃ , (((η₁ ∘⊇ η₂) ∘⊇ η₃) , 𝛈′))) & assoc∘⊇◇ 𝛈₁ 𝛈₂ 𝛈₃ }
           }


--------------------------------------------------------------------------------


{-# REWRITE id-ren∋ #-}
id-ren∋◇ : ∀ {X P A n i} → {Ξ : Vec X n} {𝒾 : Ξ ∋⟨ i ⟩ A} {a : P A} {ξ : All P Ξ}
                         → (𝓲 : ξ ∋◇⟨ 𝒾 ⟩ a)
                         → ren∋◇ id⊇◇ 𝓲 ≡ 𝓲
id-ren∋◇ zero    = refl
id-ren∋◇ (suc 𝓲) = suc & id-ren∋◇ 𝓲


{-# REWRITE comp-ren∋ #-}
comp-ren∋◇ : ∀ {X P A n n′ n″ e₁ e₂ i} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {Ξ″ : Vec X n″}
                                          {η₁ : Ξ′ ⊇⟨ e₁ ⟩ Ξ} {η₂ : Ξ″ ⊇⟨ e₂ ⟩ Ξ′} {𝒾 : Ξ ∋⟨ i ⟩ A}
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
                              (\ { (n , (Ξ , ξ)) →
                                Σ (Fin n) (\ i →
                                  Σ (Ξ ∋⟨ i ⟩ A) (\ 𝒾 → ξ ∋◇⟨ 𝒾 ⟩ a)) })
𝐫𝐞𝐧∋◇ = record
           { ℱ     = \ { (e , (η , 𝛈)) (i , (𝒾 , 𝓲)) → REN∋ e i , (ren∋ η 𝒾 , ren∋◇ 𝛈 𝓲) }
           ; idℱ   = funext! (\ { (i , (𝒾 , 𝓲)) →
                       (\ 𝓲′ → REN∋ id i , (ren∋ id⊇ 𝒾 , 𝓲′)) & id-ren∋◇ 𝓲 })
           ; compℱ = \ { (e₁ , (η₁ , 𝛈₁)) (e₂ , (η₂ , 𝛈₂)) →
                       funext! (\ { (i , (𝒾 , 𝓲)) →
                         (\ 𝓲′ → REN∋ (e₁ ∘ e₂) i , (ren∋ (η₁ ∘⊇ η₂) 𝒾 , 𝓲′)) & comp-ren∋◇ 𝛈₁ 𝛈₂ 𝓲 }) }
           }


--------------------------------------------------------------------------------
