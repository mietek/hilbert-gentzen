module FinLemmas where

open import Prelude
open import Category
open import Fin


--------------------------------------------------------------------------------
{-
                              id≥ ∘≥ e ≡ e                                      lid∘≥   ⎫
                              e ∘≥ id≥ ≡ e                                      rid∘≥   ⎬ 𝐆𝐄𝐐
                      (e₁ ∘≥ e₂) ∘≥ e₃ ≡ e₁ ∘≥ (e₂ ∘≥ e₃)                       assoc∘≥ ⎭

                             REN∋ id i ≡ i                                      id-REN∋   ⎱ 𝐑𝐄𝐍∋
                     REN∋ (e₁ ∘≥ e₂) i ≡ (REN∋ e₂ ∘ REN∋ e₁) i                  comp-REN∋ ⎰
-}
--------------------------------------------------------------------------------


lid∘≥ : ∀ {n n′} → (e : n′ ≥ n)
                 → id≥ ∘≥ e ≡ e
lid∘≥ done     = refl
lid∘≥ (drop e) = drop & lid∘≥ e
lid∘≥ (keep e) = keep & lid∘≥ e


rid∘≥ : ∀ {n n′} → (e : n′ ≥ n)
                 → e ∘≥ id≥ ≡ e
rid∘≥ done     = refl
rid∘≥ (drop e) = drop & rid∘≥ e
rid∘≥ (keep e) = keep & rid∘≥ e


assoc∘≥ : ∀ {n n′ n″ n‴} → (e₁ : n′ ≥ n) (e₂ : n″ ≥ n′) (e₃ : n‴ ≥ n″)
                         → (e₁ ∘≥ e₂) ∘≥ e₃ ≡ e₁ ∘≥ (e₂ ∘≥ e₃)
assoc∘≥ e₁        e₂        done      = refl
assoc∘≥ e₁        e₂        (drop e₃) = drop & assoc∘≥ e₁ e₂ e₃
assoc∘≥ e₁        (drop e₂) (keep e₃) = drop & assoc∘≥ e₁ e₂ e₃
assoc∘≥ (drop e₁) (keep e₂) (keep e₃) = drop & assoc∘≥ e₁ e₂ e₃
assoc∘≥ (keep e₁) (keep e₂) (keep e₃) = keep & assoc∘≥ e₁ e₂ e₃


instance
  𝐆𝐄𝐐 : Category Nat _≥_
  𝐆𝐄𝐐 = record
          { id     = id≥
          ; _∘_    = _∘≥_
          ; lid∘   = lid∘≥
          ; rid∘   = rid∘≥
          ; assoc∘ = assoc∘≥
          }


--------------------------------------------------------------------------------


id-REN∋ : ∀ {n} → (i : Fin n)
                → REN∋ id i ≡ i
id-REN∋ zero    = refl
id-REN∋ (suc i) = suc & id-REN∋ i


comp-REN∋ : ∀ {n n′ n″} → (e₁ : n′ ≥ n) (e₂ : n″ ≥ n′) (i : Fin n)
                        → REN∋ (e₁ ∘ e₂) i ≡ (REN∋ e₂ ∘ REN∋ e₁) i
comp-REN∋ e₁        done      i       = refl
comp-REN∋ e₁        (drop e₂) i       = suc & comp-REN∋ e₁ e₂ i
comp-REN∋ (drop e₁) (keep e₂) i       = suc & comp-REN∋ e₁ e₂ i
comp-REN∋ (keep e₁) (keep e₂) zero    = refl
comp-REN∋ (keep e₁) (keep e₂) (suc i) = suc & comp-REN∋ e₁ e₂ i


𝐑𝐄𝐍∋ : Presheaf 𝐆𝐄𝐐 Fin
𝐑𝐄𝐍∋ = record
         { ℱ     = REN∋
         ; idℱ   = funext! id-REN∋
         ; compℱ = \ e₁ e₂ → funext! (comp-REN∋ e₁ e₂)
         }


--------------------------------------------------------------------------------
