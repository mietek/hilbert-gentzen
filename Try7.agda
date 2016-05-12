{-

'(agda-input-user-translations
   (quote
    (("i" "⊃") ("e" "⊢") ("t" "⊩") ("N" "ℕ")
     ("f" "𝑓") ("f2" "𝑓²") ("f3" "𝑓³") ("fn" "𝑓ⁿ")
     ("b" "𝑏") ("b2" "𝑏²") ("b3" "𝑏³") ("bn" "𝑏ⁿ")
     ("v" "𝑣") ("v2" "𝑣²") ("v3" "𝑣³") ("vn" "𝑣ⁿ")
     ("l" "𝜆") ("l2" "𝜆²") ("l3" "𝜆³") ("ln" "𝜆ⁿ")
     ("o" "∘") ("o2" "∘²") ("o3" "∘³") ("on" "∘ⁿ")
     ("p" "𝑝") ("p2" "𝑝²") ("p3" "𝑝³") ("pn" "𝑝ⁿ")
     ("1" "𝜋₀") ("12" "𝜋₀²") ("13" "𝜋₀³") ("1n" "𝜋₀ⁿ")
     ("2" "𝜋₁") ("22" "𝜋₁²") ("23" "𝜋₁³") ("2n" "𝜋₁ⁿ")
     ("u" "⇑") ("u2" "⇑²") ("u3" "⇑³") ("un" "⇑ⁿ")
     ("d" "⇓") ("d2" "⇓²") ("d3" "⇓³") ("dn" "⇓ⁿ"))))

-}

module Try7 where

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


infixl 7 _∘⁰_ _∘_ _∘²_
infixr 5 𝜆⁰_ 𝜆_ 𝜆²_
infixl 3 _∧_
infixr 2 _⊃_
infixl 1 _∷_
infixr 0 _⊢_

mutual
  Cx : ℕ → Set
  Cx = Vec Ty

  data Ty : Set where
    ⊥ : Ty
    _⊃_ : Ty → Ty → Ty
    _∧_ : Ty → Ty → Ty
    _∷_ : ∀{m} {Γ : Cx m} (A : Ty) → Γ ⊢ A → Ty

  data _⊢_ {m : ℕ} (Γ : Cx m) : Ty → Set where
    𝑓⁰_   : ∀{A}
          → ℕ
          → Γ ⊢ A
    𝑣⁰_   : ∀{A}
          → A ∈ Γ
          → Γ ⊢ A
    𝜆⁰_   : ∀{A B}
          → Γ , A ⊢ B
          → Γ ⊢ A ⊃ B
    _∘⁰_  : ∀{A B}
          → Γ ⊢ A ⊃ B    → Γ ⊢ A
          → Γ ⊢ B

    𝑣_   : ∀{A}
         → (x : A ∈ Γ)
         → Γ ⊢ A ∷ 𝑣⁰ x
    𝜆_   : ∀{A B} → {t : Γ , A ⊢ B}
         → Γ , A ⊢ B ∷ t
         → Γ ⊢ A ⊃ B ∷ 𝜆⁰ t
    _∘_  : ∀{A B} → {t : Γ ⊢ A ⊃ B} {s : Γ ⊢ A}
         → Γ ⊢ A ⊃ B ∷ t    → Γ ⊢ A ∷ s
         → Γ ⊢ B ∷ t ∘⁰ s

    ⇓_   : ∀{A} → {u : Γ ⊢ A}
         → Γ ⊢ A ∷ u
         → Γ ⊢ A

    𝑣²_  : ∀{A}
         → (x : A ∈ Γ)
         → Γ ⊢ A ∷ 𝑣⁰ x ∷ 𝑣 x
    𝜆²_  : ∀{A B} → {t : Γ , A ⊢ B} → ∀{t₂}
         → Γ , A ⊢ B ∷ t ∷ t₂
         → Γ ⊢ A ⊃ B ∷ 𝜆⁰ t ∷ 𝜆 t₂
    _∘²_ : ∀{A B} → {t : Γ ⊢ A ⊃ B} {s : Γ ⊢ A} → ∀{t₂ s₂}
         → Γ ⊢ A ⊃ B ∷ t ∷ t₂   → Γ ⊢ A ∷ s ∷ s₂
         → Γ ⊢ B ∷ t ∘⁰ s ∷ t₂ ∘ s₂

tI : ∀{A} → ∅ ⊢ A ⊃ A
tI = 𝜆⁰ 𝑣⁰ Z

tK : ∀{A B} → ∅ ⊢ A ⊃ B ⊃ A
tK = 𝜆⁰ 𝜆⁰ 𝑣⁰ S Z

tS : ∀{A B C} → ∅ ⊢ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
tS = 𝜆⁰ 𝜆⁰ 𝜆⁰ (𝑣⁰ S S Z ∘⁰ 𝑣⁰ Z) ∘⁰ (𝑣⁰ S Z ∘⁰ 𝑣⁰ Z)

tI² : ∀{A} → ∅ ⊢ A ⊃ A ∷ 𝜆⁰ 𝑣⁰ Z
tI² = 𝜆 𝑣 Z

tK² : ∀{A B} → ∅ ⊢ A ⊃ B ⊃ A ∷ 𝜆⁰ 𝜆⁰ 𝑣⁰ S Z
tK² = 𝜆 𝜆 𝑣 S Z

tS² : ∀{A B C} → ∅ ⊢ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C ∷ 𝜆⁰ 𝜆⁰ 𝜆⁰ (𝑣⁰ S S Z ∘⁰ 𝑣⁰ Z) ∘⁰ (𝑣⁰ S Z ∘⁰ 𝑣⁰ Z)
tS² = 𝜆 𝜆 𝜆 (𝑣 S S Z ∘ 𝑣 Z) ∘ (𝑣 S Z ∘ 𝑣 Z)

e11 : ∀{A x} → ∅ ⊢ ((A ∷ 𝑓⁰ x) ⊃ A) ∷ 𝜆⁰ ⇓ (𝑣⁰ Z)
e11 = {!!}
