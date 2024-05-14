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

module Try4 where

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
infixr 0 _∙_⊢_ _⊩_ ⊪_
infixr 0 _∙_⊢_∷_ _⊩_∷_ ⊪_∷_
infixr 0 _∙_⊢_∷_∷_ _⊩_∷_∷_ ⊪_∷_∷_


data Ty : Set where
  ⊥   : Ty
  _⊃_ : Ty → Ty → Ty
  _∧_ : Ty → Ty → Ty


Cx : ℕ → Set
Cx = Vec Ty


data _∙_⊢_ {k n : ℕ} (Φ : Cx k) (Γ : Cx n) : Ty → Set where
  𝑓_     : ∀{A}
         → A ∈ Φ
         → Φ ∙ Γ ⊢ A
  𝑣_     : ∀{A}
         → A ∈ Γ
         → Φ ∙ Γ ⊢ A
  𝜆_     : ∀{A B}
         → Φ ∙ Γ , A ⊢ B
         → Φ ∙ Γ ⊢ A ⊃ B
  _∘_    : ∀{A B}
         → Φ ∙ Γ ⊢ A ⊃ B    → Φ ∙ Γ ⊢ A
         → Φ ∙ Γ ⊢ B
  𝑝⟨_,_⟩ : ∀{A B}
         → Φ ∙ Γ ⊢ A        → Φ ∙ Γ ⊢ B
         → Φ ∙ Γ ⊢ A ∧ B
  𝜋₀_    : ∀{A B}
         → Φ ∙ Γ ⊢ A ∧ B
         → Φ ∙ Γ ⊢ A
  𝜋₁_    : ∀{A B}
         → Φ ∙ Γ ⊢ A ∧ B
         → Φ ∙ Γ ⊢ B


_⊩_ : ∀{k} → Cx k → Ty → Set
Φ ⊩ A = ∀{n} {Γ : Cx n} → Φ ∙ Γ ⊢ A

⊪_ : Ty → Set
⊪ A = ∀{k} {Φ : Cx k} → Φ ⊩ A


tI : ∀{A}
   → ⊪ A ⊃ A
tI = 𝜆 𝑣 Z

tK : ∀{A B}
   → ⊪ A ⊃ B ⊃ A
tK = 𝜆 𝜆 𝑣 S Z

tS : ∀{A B C}
   → ⊪ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
tS = 𝜆 𝜆 𝜆 (𝑣 S S Z ∘ 𝑣 Z) ∘ (𝑣 S Z ∘ 𝑣 Z)


data _∙_⊢_∷_ {k n : ℕ} (Φ : Cx k) (Γ : Cx n) : (A : Ty) → Φ ∙ Γ ⊢ A → Set where
  𝑓²_     : ∀{A x}
          → A ∈ Φ
          → Φ ∙ Γ ⊢ A ∷ 𝑓 x
  𝑣²_     : ∀{A}
          → (x : A ∈ Γ)
          → Φ ∙ Γ ⊢ A ∷ 𝑣 x
  𝜆²_     : ∀{A B t}
          → Φ ∙ Γ , A ⊢ B ∷ t
          → Φ ∙ Γ ⊢ A ⊃ B ∷ 𝜆 t
  _∘²_    : ∀{A B t s}
          → Φ ∙ Γ ⊢ A ⊃ B ∷ t    → Φ ∙ Γ ⊢ A ∷ s
          → Φ ∙ Γ ⊢ B ∷ t ∘ s
  𝑝²⟨_,_⟩ : ∀{A B t s}
          → Φ ∙ Γ ⊢ A ∷ t        → Φ ∙ Γ ⊢ B ∷ s
          → Φ ∙ Γ ⊢ A ∧ B ∷ 𝑝⟨ t , s ⟩
  𝜋₀²_    : ∀{A B t}
          → Φ ∙ Γ ⊢ A ∧ B ∷ t
          → Φ ∙ Γ ⊢ A ∷ 𝜋₀ t
  𝜋₁²_    : ∀{A B t}
          → Φ ∙ Γ ⊢ A ∧ B ∷ t
          → Φ ∙ Γ ⊢ B ∷ 𝜋₁ t
  !_      : ∀{A t}
          → Φ ∙ Γ ⊢ A ∷ t
          → Φ ∙ Γ ⊢ A ∷ t


_⊩_∷_ : ∀{k} (Φ : Cx k) (A : Ty) → Φ ⊩ A → Set
Φ ⊩ A ∷ t = ∀{n} {Γ : Cx n} → Φ ∙ Γ ⊢ A ∷ t

⊪_∷_ : (A : Ty) → ⊪ A → Set
⊪ A ∷ t = ∀{k} {Φ : Cx k} → Φ ⊩ A ∷ t


tI² : ∀{A}
    → ⊪ A ⊃ A
      ∷ 𝜆 𝑣 Z
tI² = 𝜆² (𝑣² Z)

tK² : ∀{A B}
    → ⊪ A ⊃ B ⊃ A
      ∷ 𝜆 𝜆 𝑣 S Z
tK² = 𝜆² 𝜆² 𝑣² S Z

tS² : ∀{A B C}
    → ⊪ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
      ∷ 𝜆 𝜆 𝜆 (𝑣 S S Z ∘ 𝑣 Z) ∘ (𝑣 S Z ∘ 𝑣 Z)
tS² = 𝜆² 𝜆² 𝜆² (𝑣² S S Z ∘² 𝑣² Z) ∘² (𝑣² S Z ∘² 𝑣² Z)



data _∙_⊢_∷_∷_ {k n : ℕ} (Φ : Cx k) (Γ : Cx n) : (A : Ty) → (t : Φ ∙ Γ ⊢ A) → Φ ∙ Γ ⊢ A ∷ t → Set where
  𝑓³_      : ∀{A x}
          → A ∈ Φ
          → Φ ∙ Γ ⊢ A ∷ 𝑓 x ∷ 𝑓² x
  𝑣³_     : ∀{A}
          → (x : A ∈ Γ)
          → Φ ∙ Γ ⊢ A ∷ 𝑣 x ∷ 𝑣² x
  𝜆³_     : ∀{A B t t₂}
          → Φ ∙ Γ , A ⊢ B ∷ t ∷ t₂
          → Φ ∙ Γ ⊢ A ⊃ B ∷ 𝜆 t ∷ 𝜆² t₂
  _∘³_    : ∀{A B t t₂ s s₂}
          → Φ ∙ Γ ⊢ A ⊃ B ∷ t ∷ t₂   → Φ ∙ Γ ⊢ A ∷ s ∷ s₂
          → Φ ∙ Γ ⊢ B ∷ t ∘ s ∷ t₂ ∘² s₂
  𝑝³⟨_,_⟩ : ∀{A B t t₂ s s₂}
          → Φ ∙ Γ ⊢ A ∷ t ∷ t₂       → Φ ∙ Γ ⊢ B ∷ s ∷ s₂
          → Φ ∙ Γ ⊢ A ∧ B ∷ 𝑝⟨ t , s ⟩ ∷ 𝑝²⟨ t₂ , s₂ ⟩
  𝜋₀³_    : ∀{A B t t₂}
          → Φ ∙ Γ ⊢ A ∧ B ∷ t ∷ t₂
          → Φ ∙ Γ ⊢ A ∷ 𝜋₀ t ∷ 𝜋₀² t₂
  𝜋₁³_    : ∀{A B t t₂}
          → Φ ∙ Γ ⊢ A ∧ B ∷ t ∷ t₂
          → Φ ∙ Γ ⊢ B ∷ 𝜋₁ t ∷ 𝜋₁² t₂
  !_      : ∀{A t t₂}
          → Φ ∙ Γ ⊢ A ∷ t ∷ t₂
          → Φ ∙ Γ ⊢ A ∷ t ∷ t₂


⇑_ : ∀{k n} {Φ : Cx k} {Γ : Cx n} {A : Ty} {u : Φ ∙ Γ ⊢ A}
   → (x : Φ ∙ Γ ⊢ A ∷ u)
   → Φ ∙ Γ ⊢ A ∷ u ∷ (! x)
⇑_ = {!!}

⇓_ : ∀{k n} {Φ : Cx k} {Γ : Cx n} {A : Ty} {u : Φ ∙ Γ ⊢ A}
   → Φ ∙ Γ ⊢ A ∷ u
   → Φ ∙ Γ ⊢ A
⇓_ {u = u} = λ _ → u


_⊩_∷_∷_ : ∀{k} (Φ : Cx k) (A : Ty) (t : Φ ⊩ A) → Φ ⊩ A ∷ t → Set
Φ ⊩ A ∷ t ∷ t₂ = ∀{n} {Γ : Cx n} → Φ ∙ Γ ⊢ A ∷ t ∷ t₂

⊪_∷_∷_ : (A : Ty) (t : ⊪ A) → ⊪ A ∷ t → Set
⊪ A ∷ t ∷ t₂ = ∀{k} {Φ : Cx k} → Φ ⊩ A ∷ t ∷ t₂


tI³ : ∀{A} → ⊪ A ⊃ A
    ∷ 𝜆 𝑣 Z
    ∷ 𝜆² 𝑣² Z
tI³ = 𝜆³ 𝑣³ Z

tK³ : ∀{A B} → ⊪ A ⊃ B ⊃ A
    ∷ 𝜆 𝜆 𝑣 S Z
    ∷ 𝜆² 𝜆² 𝑣² S Z
tK³ = 𝜆³ 𝜆³ 𝑣³ S Z

tS³ : ∀{A B C} → ⊪ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
    ∷ 𝜆 𝜆 𝜆 (𝑣 S S Z ∘ 𝑣 Z) ∘ (𝑣 S Z ∘ 𝑣 Z)
    ∷ 𝜆² 𝜆² 𝜆² (𝑣² S S Z ∘² 𝑣² Z) ∘² (𝑣² S Z ∘² 𝑣² Z)
tS³ = 𝜆³ 𝜆³ 𝜆³ (𝑣³ S S Z ∘³ 𝑣³ Z) ∘³ (𝑣³ S Z ∘³ 𝑣³ Z)


-- tt : ∀{A x}
--    → ∅ , x ⊩ A ⊃ A
--            ∷ ?
--            ∷ 𝜆 ⇑ 𝑣 Z
-- tt = {!!}
