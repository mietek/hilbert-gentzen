module LR2 where

open import Prelude
open import Category
open import Fin
open import FinLemmas
-- open import List
-- open import ListLemmas
open import Vec
open import VecLemmas
open import AllVec
open import LR1


--------------------------------------------------------------------------------


data Val {g} : Term g → Set
  where
    instance
      val-LAM   : ∀ {M} → Val (LAM M)
      val-TRUE  : Val TRUE
      val-FALSE : Val FALSE

data EC (g : Nat) : Set
  where
    ec-[]   : EC g
    ec-IF   : EC g → Term g → Term g → EC g
    ec-APP₁ : EC g → Term g → EC g
    ec-APP₂ : (N : Term g) → EC g → {{_ : Val N}} → EC g

_[_] : ∀ {g} → EC g → Term g → Term g
ec-[]         [ M ] = M
ec-IF   E N O [ M ] = IF (E [ M ]) N O
ec-APP₁ E N   [ M ] = APP (E [ M ]) N
ec-APP₂ N E   [ M ] = APP N (E [ M ])

infix 3 _↦_
data _↦_ {g} : Term g → Term g → Set
  where
    red-IF-TRUE  : ∀ {M N} → IF TRUE M N ↦ M
    red-IF-FALSE : ∀ {M N} → IF FALSE M N ↦ N
    red-APP-LAM  : ∀ {M N} → APP (LAM M) N ↦ CUT N M
    red-ec       : ∀ {M M′} → (E : EC g) → M ↦ M′ → E [ M ] ↦ E [ M′ ]

infix 3 _⇓_
data _⇓_ {g} : Term g → (M′ : Term g) → {{_ : Val M′}} → Set
  where
    eval-TRUE  : TRUE ⇓ TRUE
    eval-FALSE : FALSE ⇓ FALSE
    eval-LAM   : ∀ {M} → LAM M ⇓ LAM M
    eval-red   : ∀ {M M′ M″} → {{_ : Val M″}} → M ↦ M′ → M′ ⇓ M″ → M ⇓ M″

_⇓ : ∀ {g} → (M : Term g) → Set
M ⇓ = Σ (Term _) (\ M′ → Σ (Val M′) (\ p → (M ⇓ M′) {{p}}))

mutual
  tp↦ : ∀ {g M M′ A} → {Γ : Types g}
                      → M ↦ M′ → Γ ⊢ M ⦂ A
                      → Γ ⊢ M′ ⦂ A
  tp↦ red-IF-TRUE      (if 𝒟 ℰ ℱ)      = ℰ
  tp↦ red-IF-FALSE     (if 𝒟 ℰ ℱ)      = ℱ
  tp↦ red-APP-LAM      (app (lam 𝒟) ℰ) = cut ℰ 𝒟
  tp↦ (red-ec E M↦M′) 𝒟               = plug E M↦M′ 𝒟

  plug : ∀ {g M M′ A} → {Γ : Types g}
                      → (E : EC g) → M ↦ M′ → Γ ⊢ E [ M ] ⦂ A
                      → Γ ⊢ E [ M′ ] ⦂ A
  plug ec-[]         M↦M′ 𝒟          = tp↦ M↦M′ 𝒟
  plug (ec-IF E N O) M↦M′ (if 𝒟 ℰ ℱ) = if (plug E M↦M′ 𝒟) ℰ ℱ
  plug (ec-APP₁ E N) M↦M′ (app 𝒟 ℰ)  = app (plug E M↦M′ 𝒟) ℰ
  plug (ec-APP₂ N E) M↦M′ (app 𝒟 ℰ)  = app 𝒟 (plug E M↦M′ ℰ)

tp⇓ : ∀ {g M M′ A} → {{_ : Val M′}}
                   → {Γ : Types g}
                   → M ⇓ M′ → Γ ⊢ M ⦂ A
                   → Γ ⊢ M′ ⦂ A
tp⇓ eval-TRUE              𝒟 = 𝒟
tp⇓ eval-FALSE             𝒟 = 𝒟
tp⇓ eval-LAM               𝒟 = 𝒟
tp⇓ (eval-red M↦M′ M′⇓M″) 𝒟 = tp⇓ M′⇓M″ (tp↦ M↦M′ 𝒟)

lem-IF-TRUE : ∀ {g} → {M N N′ O : Term g} → {{_ : Val N′}}
                    → M ⇓ TRUE → N ⇓ N′
                    → IF M N O ⇓ N′
lem-IF-TRUE {M = M} {N} {N′} {O} eval-TRUE N⇓N′
  = eval-red {M = IF TRUE N O} {N} {N′} red-IF-TRUE N⇓N′
lem-IF-TRUE {M = M} {N} {N′} {O} (eval-red {M′ = M′} M↦M′ M′⇓TRUE) N⇓N′
  = eval-red (red-ec (ec-IF ec-[] N O) M↦M′) (lem-IF-TRUE {M = M′} {N} {N′} {O} M′⇓TRUE N⇓N′)

lem-IF-FALSE : ∀ {g} → {M N O O′ : Term g} → {{_ : Val O′}}
                     → M ⇓ FALSE → O ⇓ O′
                     → IF M N O ⇓ O′
lem-IF-FALSE {M = M} {N} {O} {O′} eval-FALSE O⇓O′
  = eval-red {M = IF FALSE N O} {O} {O′} red-IF-FALSE O⇓O′
lem-IF-FALSE {M = M} {N} {O} {O′} (eval-red {M′ = M′} M↦M′ M′⇓FALSE) O⇓O′
  = eval-red (red-ec (ec-IF ec-[] N O) M↦M′) (lem-IF-FALSE {M = M′} {N} {O} {O′} M′⇓FALSE O⇓O′)

sn : ∀ {M A} → ∙ ⊢ M ⦂ A → M ⇓
sn (var ())
sn (lam 𝒟)    = {!!}
sn (app 𝒟 ℰ)  = {!!}
sn true       = TRUE  , (val-TRUE  , eval-TRUE)
sn false      = FALSE , (val-FALSE , eval-FALSE)
sn (if 𝒟 ℰ ℱ) with sn 𝒟 | sn ℰ | sn ℱ
sn (if 𝒟 ℰ ℱ) | M′     , (vM′         , M⇓M′)    | N′ , (vN′ , N⇓N′) | O′ , (vO′ , O⇓O′) with tp⇓ M⇓M′ 𝒟
sn (if 𝒟 ℰ ℱ) | LAM M′ , (val-LAM     , M⇓M′)    | N′ , (vN′ , N⇓N′) | O′ , (vO′ , O⇓O′) | ()
sn (if 𝒟 ℰ ℱ) | TRUE   , (val-TRUE    , M⇓TRUE)  | N′ , (vN′ , N⇓N′) | O′ , (vO′ , O⇓O′) | true  = N′ , (vN′ , lem-IF-TRUE  M⇓TRUE  N⇓N′)
sn (if 𝒟 ℰ ℱ) | FALSE  , (val-FALSE   , M⇓FALSE) | N′ , (vN′ , N⇓N′) | O′ , (vO′ , O⇓O′) | false = O′ , (vO′ , lem-IF-FALSE M⇓FALSE O⇓O′)
