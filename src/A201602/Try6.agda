{-# OPTIONS --allow-unsolved-metas #-}

{-

'(agda-input-user-translations
   (quote
    (("i" "⊃") ("e" "⊢") ("t" "⊩")
     ("f" "𝑓") ("f2" "𝑓²") ("f3" "𝑓³") ("fn" "𝑓ⁿ")
     ("v" "𝑣") ("v2" "𝑣²") ("v3" "𝑣³") ("vn" "𝑣ⁿ")
     ("l" "𝜆") ("l2" "𝜆²") ("l3" "𝜆³") ("ln" "𝜆ⁿ")
     ("o" "∘") ("o2" "∘²") ("o3" "∘³") ("on" "∘ⁿ")
     ("p" "𝑝") ("p2" "𝑝²") ("p3" "𝑝³") ("pn" "𝑝ⁿ")
     ("1" "𝜋₀") ("12" "𝜋₀²") ("13" "𝜋₀³") ("1n" "𝜋₀ⁿ")
     ("2" "𝜋₁") ("22" "𝜋₁²") ("23" "𝜋₁³") ("2n" "𝜋₁ⁿ")
     ("u" "⇑") ("u2" "⇑²") ("u3" "⇑³") ("un" "⇑ⁿ")
     ("d" "⇓") ("d2" "⇓²") ("d3" "⇓³") ("dn" "⇓ⁿ"))))

-}

module A201602.Try6 where

open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _×_; _,_)


data Vec (X : Set) : ℕ → Set where
  ∅   : Vec X zero
  _,_ : ∀{n} → Vec X n → X → Vec X (suc n)

data _∈_ {X : Set} : ∀{n} → X → Vec X n → Set where
  Z  : ∀{n x} {xs : Vec X n}
     → x ∈ (xs , x)
  S_ : ∀{n x y} {xs : Vec X n}
     → x ∈ xs
     → x ∈ (xs , y)


Pr : Set
Pr = ℕ

Cx : ℕ → Set
Cx = Vec Pr

mutual
  infixl 7 _∘_
  infixr 5 𝜆_
--  infixl 3 _∧_
  infixr 2 _⊃_
  infixl 1 _∷_
  infixr 0 _∙_⊢_

  data Ty {m : ℕ} (Δ : Cx m) : Set where
    α_  : Pr → Ty Δ
    _⊃_ : Ty Δ → Ty Δ → Ty Δ
--    _∧_ : Ty Δ → Ty Δ → Ty Δ

  data Ass {n m : ℕ} (Δ : Cx m) (Γ : Cx n) : Set where
    τ_  : Ty Δ → Ass Δ Γ
    _∷_ : (A : Ass Δ Γ) → Δ ∙ Γ ⊢ A → Ass Δ Γ

  data _∙_⊢_ {m n : ℕ} (Δ : Cx m) (Γ : Cx n) : Ass Δ Γ → Set where
    𝑓_ : ∀{A}
       → A ∈ Δ
       → Δ ∙ Γ ⊢ τ α A

    𝑓²_ : ∀{A}
        → (x : A ∈ Δ)
        → Δ ∙ Γ ⊢ τ α A ∷ 𝑓 x

    𝑓³_ : ∀{A}
        → (x : A ∈ Δ)
        → Δ ∙ Γ ⊢ τ α A ∷ 𝑓 x ∷ 𝑓² x

    𝑣_ : ∀{A}
       → A ∈ Γ
       → Δ ∙ Γ ⊢ τ α A

    𝑣²_ : ∀{A}
        → (x : A ∈ Γ)
        → Δ ∙ Γ ⊢ τ α A ∷ 𝑣 x

    𝑣³_ : ∀{A}
        → (x : A ∈ Γ)
        → Δ ∙ Γ ⊢ τ α A ∷ 𝑣 x ∷ 𝑣² x

    𝜆_ : ∀{A B}
       → Δ ∙ Γ , A ⊢ τ B
       → Δ ∙ Γ ⊢ τ (α A ⊃ B)

    𝜆²_ : ∀{A B t}
        → Δ ∙ Γ , A ⊢ τ B ∷ t
        → Δ ∙ Γ ⊢ τ (α A ⊃ B) ∷ 𝜆 t

    𝜆³_ : ∀{A B t t₂}
        → Δ ∙ Γ , A ⊢ τ B ∷ t ∷ t₂
        → Δ ∙ Γ ⊢ τ (α A ⊃ B) ∷ 𝜆 t ∷ 𝜆² t₂

    _∘_ : ∀{A B}
        → Δ ∙ Γ ⊢ τ (A ⊃ B)    → Δ ∙ Γ ⊢ τ A
        → Δ ∙ Γ ⊢ τ B

    _∘²_ : ∀{A B t s}
         → Δ ∙ Γ ⊢ τ (A ⊃ B) ∷ t    → Δ ∙ Γ ⊢ τ A ∷ s
         → Δ ∙ Γ ⊢ τ B ∷ t ∘ s

    _∘³_ : ∀{A B t t₂ s s₂}
         → Δ ∙ Γ ⊢ τ (A ⊃ B) ∷ t ∷ t₂    → Δ ∙ Γ ⊢ τ A ∷ s ∷ s₂
         → Δ ∙ Γ ⊢ τ B ∷ t ∘ s ∷ t₂ ∘² s₂

tI : ∀{A} → ∅ ∙ ∅ ⊢ τ (α A ⊃ α A)
tI = 𝜆 𝑣 Z

tK : ∀{A B} → ∅ ∙ ∅ ⊢ τ (α A ⊃ α B ⊃ α A)
tK = 𝜆 𝜆 𝑣 S Z

tS : ∀{A B C} → ∅ ∙ ∅ ⊢ τ ((α A ⊃ α B ⊃ α C) ⊃ (α A ⊃ α B) ⊃ α A ⊃ α C)
tS = {!𝜆 ?!}


--     _𝑝_ : ∀{A B}
--         → Δ ∙ Γ ⊢ A    → Δ ∙ Γ ⊢ B
--         → Δ ∙ Γ ⊢ A ∧ B

--     𝜋₀_ : ∀{A B}
--         → Δ ∙ Γ ⊢ A ∧ B
--         → Δ ∙ Γ ⊢ A

--     𝜋₁_ : ∀{A B}
--         → Δ ∙ Γ ⊢ A ∧ B
--         → Δ ∙ Γ ⊢ B

--     !_ : ∀{A}
--        → Δ ∙ Γ ⊢ A
--        → Δ ∙ Γ ⊢ A

-- {-    ⇑_ : ∀{A u}
--        → (t : Δ ∙ ∅ ⊢ A ∷ u)
--        → Δ ∙ Γ ⊢ A ∷ u ∷ ! t

--     ⇓_ : ∀{A t}
--        → Δ ∙ Γ ⊢ A ∷ t
--        → Δ ∙ Γ ⊢ A-}

-- -- TTm : ∀{m} (Δ : PCx m) → Ty Δ → Set
-- -- TTm Δ A = ∀{n} {Γ : TCx Δ n} → Δ ∙ Γ ⊢ A

-- -- TTTm : Ty ∅ → Set
-- -- TTTm = TTm ∅

-- -- TTTI : ∀{A} → TTTm (A ⊃ A)
-- -- TTTI = 𝜆 𝑣 Z

-- -- TTTK : ∀{A B} → TTTm (A ⊃ B ⊃ A)
-- -- TTTK = 𝜆 𝜆 𝑣 S Z

-- -- TTTS : ∀{A B C} → TTTm ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
-- -- TTTS = 𝜆 𝜆 𝜆 (𝑣 S S Z ∘ 𝑣 Z) ∘ (𝑣 S Z ∘ 𝑣 Z)


-- -- --axT : ∀{x A} → TTm (∅ , x) ((A ∷ 𝑓 Z) ⊃ A ∷ 𝜆 ⇓ 𝑣 Z)
-- -- --axT = {!!}

-- -- --axK : ∀{f x A} → TTm (∅ , f , x) (A ⊃ B ∷
