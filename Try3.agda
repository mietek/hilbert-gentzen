{-# OPTIONS --allow-unsolved-metas #-}

module A201602.Try3 where

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


infixl 4 _∘_ _∘²_ _∘³_
infixr 3 𝜆_ 𝜆²_ 𝜆³_
infixl 2 _∧_
infixr 1 _⊃_
infixr 0 _⊢_ _⊢_∷_ _⊢_∷_∷_
infixr 0 ⊩_ ⊩_∷_ ⊩_∷_∷_
infixr 0 _F⊩_ _F⊩_∷_ _F⊩_∷_∷_


Var : Set
Var = ℕ

FCx : ℕ → Set
FCx = Vec Var


data Ty {k : ℕ} (Φ : FCx k) : Set where
  fv_ : ∀{x} → x ∈ Φ → Ty Φ
  _⊃_ : Ty Φ → Ty Φ → Ty Φ
  _∧_ : Ty Φ → Ty Φ → Ty Φ


Cx : {k : ℕ} {Φ : FCx k} → ℕ → Set
Cx {Φ = Φ} n = Vec (Ty Φ) n


data _⊢_ {k n : ℕ} {Φ : FCx k} (Γ : Cx n) : Ty Φ → Set where
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


⊩_ : Ty ∅ → Set
⊩ A = ∀{n} {Γ : Cx n} → Γ ⊢ A

_F⊩_ : ∀{k} (Φ : FCx k) → Ty Φ → Set
Φ F⊩ A = ∀{n} {Γ : Cx n} → Γ ⊢ A


tI : ∀{A} → ⊩ A ⊃ A
tI = 𝜆 𝑣 Z

tK : ∀{A B} → ⊩ A ⊃ B ⊃ A
tK = 𝜆 𝜆 𝑣 S Z

tS : ∀{A B C} → ⊩ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
tS = 𝜆 𝜆 𝜆 (𝑣 S S Z ∘ 𝑣 Z) ∘ (𝑣 S Z ∘ 𝑣 Z)

tJ : ∀{A} → ∅ , A F⊩ fv Z ⊃ fv Z
tJ = 𝜆 𝑣 Z



data _⊢_∷_ {k n : ℕ} {Φ : FCx k} (Γ : Cx n) : (A : Ty Φ) → Γ ⊢ A → Set where
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


⊩_∷_ : (A : Ty ∅) → ⊩ A → Set
⊩ A ∷ t = ∀{n} {Γ : Cx n} → Γ ⊢ A ∷ t

_F⊩_∷_ : ∀{k} (Φ : FCx k) (A : Ty Φ) → Φ F⊩ A → Set
Φ F⊩ A ∷ t = ∀{n} {Γ : Cx n} → Γ ⊢ A ∷ t


tI² : ∀{A} → ⊩ A ⊃ A
    ∷ 𝜆 𝑣 Z
tI² = 𝜆² (𝑣² Z)

tK² : ∀{A B} → ⊩ A ⊃ B ⊃ A
    ∷ 𝜆 𝜆 𝑣 S Z
tK² = 𝜆² 𝜆² 𝑣² S Z

tS² : ∀{A B C} → ⊩ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
    ∷ 𝜆 𝜆 𝜆 (𝑣 S S Z ∘ 𝑣 Z) ∘ (𝑣 S Z ∘ 𝑣 Z)
tS² = 𝜆² 𝜆² 𝜆² (𝑣² S S Z ∘² 𝑣² Z) ∘² (𝑣² S Z ∘² 𝑣² Z)


data _⊢_∷_∷_ {k n : ℕ} {Φ : FCx k} (Γ : Cx n) : (A : Ty Φ) → (t : Γ ⊢ A) → Γ ⊢ A ∷ t → Set where
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

⇑_ : ∀{k n} {Φ : FCx k} {Γ : Cx n} {A : Ty Φ} {u : Γ ⊢ A}
   → (x : Γ ⊢ A ∷ u)
   → Γ ⊢ A ∷ u ∷ (! x)
⇑_ = {!!}

⇓_ : ∀{k n} {Φ : FCx k} {Γ : Cx n} {A : Ty Φ} {u : Γ ⊢ A}
   → Γ ⊢ A ∷ u
   → Γ ⊢ A
⇓_ {u = u} = λ _ → u

⊩_∷_∷_ : (A : Ty ∅) → (t : ⊩ A) → ⊩ A ∷ t → Set
⊩ A ∷ t ∷ t₂ = ∀{n} {Γ : Cx n} → Γ ⊢ A ∷ t ∷ t₂

_F⊩_∷_∷_ : ∀{k} (Φ : FCx k) (A : Ty Φ) → (t : Φ F⊩ A) → Φ F⊩ A ∷ t → Set
Φ F⊩ A ∷ t ∷ t₂ = ∀{n} {Γ : Cx n} → Γ ⊢ A ∷ t ∷ t₂


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
