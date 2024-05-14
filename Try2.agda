{-# OPTIONS --allow-unsolved-metas #-}

{-

'(agda-input-user-translations
   (quote
    (("i" "⊃") ("e" "⊢") ("t" "⊩")
     ("v" "𝑣") ("v2" "𝑣²") ("v3" "𝑣³") ("vn" "𝑣ⁿ")
     ("l" "𝜆") ("l2" "𝜆²") ("l3" "𝜆³") ("ln" "𝜆ⁿ")
     ("o" "∘") ("o2" "∘²") ("o3" "∘³") ("on" "∘ⁿ")
     ("p" "𝑝") ("p2" "𝑝²") ("p3" "𝑝³") ("pn" "𝑝ⁿ")
     ("1" "𝜋₀") ("12" "𝜋₀²") ("13" "𝜋₀³") ("1n" "𝜋₀ⁿ")
     ("2" "𝜋₁") ("22" "𝜋₁²") ("23" "𝜋₁³") ("2n" "𝜋₁ⁿ")
     ("u" "⇑") ("u2" "⇑²") ("u3" "⇑³") ("un" "⇑ⁿ")
     ("d" "⇓") ("d2" "⇓²") ("d3" "⇓³") ("dn" "⇓ⁿ"))))

-}

module A201602.Try2 where

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



{-

A ∈ Γ
--------- M𝑣 Z
Γ , A ⊢ A
--------- M𝜆
Γ ⊢ A ⊃ A


A ∈ Γ
----------------- M𝑣² Z
Γ , A ⊢ 𝑣 Z : A
----------------- M𝜆²
Γ ⊢ 𝜆 𝑣 Z : A ⊃ A


A ∈ Γ
--------------------------- M𝑣³ Z
Γ , A ⊢ 𝑣² Z : 𝑣 Z : A
--------------------------- M𝜆³
Γ ⊢ 𝜆² 𝑣² Z : 𝜆 𝑣 Z : A ⊃ A

-}


infixl 4 _∘_ _∘²_ _∘³_
infixr 3 𝜆_ 𝜆²_ 𝜆³_
infixl 2 _∧_
infixr 1 _⊃_
infixr 0 _⊢_ ⊩_ _⊢_∷_ ⊩_∷_ _⊢_∷_∷_ ⊩_∷_∷_


data Ty : Set where
  ⊥   : Ty
  _⊃_ : Ty → Ty → Ty
  _∧_ : Ty → Ty → Ty


Cx : ℕ → Set
Cx = Vec Ty


data _⊢_ {n : ℕ} (Γ : Cx n) : Ty → Set where
  𝑣_     : ∀{A}
         → A ∈ Γ
         → Γ ⊢ A
  𝜆_     : ∀{A B}
         → Γ , A ⊢ B
         → Γ ⊢ A ⊃ B
  _∘_    : ∀{A B}
         → Γ ⊢ A ⊃ B    → Γ ⊢ A
         → Γ ⊢ B
  𝑝⟨_,_⟩ : ∀{A B}
         → Γ ⊢ A        → Γ ⊢ B
         → Γ ⊢ A ∧ B
  𝜋₀_    : ∀{A B}
         → Γ ⊢ A ∧ B
         → Γ ⊢ A
  𝜋₁_    : ∀{A B}
         → Γ ⊢ A ∧ B
         → Γ ⊢ B

⊩_ : Ty → Set
⊩ A = ∀{n} {Γ : Cx n} → Γ ⊢ A


tI : ∀{A} → ⊩ A ⊃ A
tI = 𝜆 𝑣 Z

tK : ∀{A B} → ⊩ A ⊃ B ⊃ A
tK = 𝜆 𝜆 𝑣 S Z

tS : ∀{A B C} → ⊩ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
tS = 𝜆 𝜆 𝜆 (𝑣 S S Z ∘ 𝑣 Z) ∘ (𝑣 S Z ∘ 𝑣 Z)


data _⊢_∷_ {n : ℕ} (Γ : Cx n) : (A : Ty) → Γ ⊢ A → Set where
  𝑣²_     : ∀{A}
          → (x : A ∈ Γ)
          → Γ ⊢ A ∷ 𝑣 x
  𝜆²_     : ∀{A B t}
          → Γ , A ⊢ B ∷ t
          → Γ ⊢ A ⊃ B ∷ 𝜆 t
  _∘²_    : ∀{A B t s}
          → Γ ⊢ A ⊃ B ∷ t    → Γ ⊢ A ∷ s
          → Γ ⊢ B ∷ t ∘ s
  𝑝²⟨_,_⟩ : ∀{A B t s}
          → Γ ⊢ A ∷ t        → Γ ⊢ B ∷ s
          → Γ ⊢ A ∧ B ∷ 𝑝⟨ t , s ⟩
  𝜋₀²_    : ∀{A B t}
          → Γ ⊢ A ∧ B ∷ t
          → Γ ⊢ A ∷ 𝜋₀ t
  𝜋₁²_    : ∀{A B t}
          → Γ ⊢ A ∧ B ∷ t
          → Γ ⊢ B ∷ 𝜋₁ t
  !_      : ∀{A t}
          → Γ ⊢ A ∷ t
          → Γ ⊢ A ∷ t

⊩_∷_ : (A : Ty) → ⊩ A → Set
⊩ A ∷ t = ∀{n} {Γ : Cx n} → Γ ⊢ A ∷ t


tI² : ∀{A} → ⊩ A ⊃ A
    ∷ 𝜆 𝑣 Z
tI² = 𝜆² (𝑣² Z)

tK² : ∀{A B} → ⊩ A ⊃ B ⊃ A
    ∷ 𝜆 𝜆 𝑣 S Z
tK² = 𝜆² 𝜆² 𝑣² S Z

tS² : ∀{A B C} → ⊩ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
    ∷ 𝜆 𝜆 𝜆 (𝑣 S S Z ∘ 𝑣 Z) ∘ (𝑣 S Z ∘ 𝑣 Z)
tS² = 𝜆² 𝜆² 𝜆² (𝑣² S S Z ∘² 𝑣² Z) ∘² (𝑣² S Z ∘² 𝑣² Z)


data _⊢_∷_∷_ {n : ℕ} (Γ : Cx n) : (A : Ty) → (t : Γ ⊢ A) → Γ ⊢ A ∷ t → Set where
  𝑣³_     : ∀{A}
          → (x : A ∈ Γ)
          → Γ ⊢ A ∷ 𝑣 x ∷ 𝑣² x
  𝜆³_     : ∀{A B t t₂}
          → Γ , A ⊢ B ∷ t ∷ t₂
          → Γ ⊢ A ⊃ B ∷ 𝜆 t ∷ 𝜆² t₂
  _∘³_    : ∀{A B t t₂ s s₂}
          → Γ ⊢ A ⊃ B ∷ t ∷ t₂   → Γ ⊢ A ∷ s ∷ s₂
          → Γ ⊢ B ∷ t ∘ s ∷ t₂ ∘² s₂
  𝑝³⟨_,_⟩ : ∀{A B t t₂ s s₂}
          → Γ ⊢ A ∷ t ∷ t₂       → Γ ⊢ B ∷ s ∷ s₂
          → Γ ⊢ A ∧ B ∷ 𝑝⟨ t , s ⟩ ∷ 𝑝²⟨ t₂ , s₂ ⟩
  𝜋₀³_    : ∀{A B t t₂}
          → Γ ⊢ A ∧ B ∷ t ∷ t₂
          → Γ ⊢ A ∷ 𝜋₀ t ∷ 𝜋₀² t₂
  𝜋₁³_    : ∀{A B t t₂}
          → Γ ⊢ A ∧ B ∷ t ∷ t₂
          → Γ ⊢ B ∷ 𝜋₁ t ∷ 𝜋₁² t₂
  !_      : ∀{A t t₂}
          → Γ ⊢ A ∷ t ∷ t₂
          → Γ ⊢ A ∷ t ∷ t₂

⇑_ : ∀{A n} {Γ : Cx n} {u : Γ ⊢ A}
   → (x : Γ ⊢ A ∷ u)
   → Γ ⊢ A ∷ u ∷ (! x)
⇑_ = {!!}

⇓_ : ∀{A n} {Γ : Cx n} {u : Γ ⊢ A}
   → Γ ⊢ A ∷ u
   → Γ ⊢ A
⇓_ {u = u} = λ _ → u

⊩_∷_∷_ : (A : Ty) → (t : ⊩ A) → ⊩ A ∷ t → Set
⊩ A ∷ t ∷ t₂ = ∀{n} {Γ : Cx n} → Γ ⊢ A ∷ t ∷ t₂


tI³ : ∀{A} → ⊩ A ⊃ A
    ∷ 𝜆 𝑣 Z
    ∷ 𝜆² 𝑣² Z
tI³ = 𝜆³ 𝑣³ Z

tK³ : ∀{A B} → ⊩ A ⊃ B ⊃ A
    ∷ 𝜆 𝜆 𝑣 S Z
    ∷ 𝜆² 𝜆² 𝑣² S Z
tK³ = 𝜆³ 𝜆³ 𝑣³ S Z

tS³ : ∀{A B C} → ⊩ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
    ∷ 𝜆 𝜆 𝜆 (𝑣 S S Z ∘ 𝑣 Z) ∘ (𝑣 S Z ∘ 𝑣 Z)
    ∷ 𝜆² 𝜆² 𝜆² (𝑣² S S Z ∘² 𝑣² Z) ∘² (𝑣² S Z ∘² 𝑣² Z)
tS³ = 𝜆³ 𝜆³ 𝜆³ (𝑣³ S S Z ∘³ 𝑣³ Z) ∘³ (𝑣³ S Z ∘³ 𝑣³ Z)
