{-# OPTIONS --allow-unsolved-metas #-}

{-

An implementation of the Alt-Artëmov system λ∞
==============================================

Work in progress.

For easy editing with Emacs agda-mode, add to your .emacs file:

'(agda-input-user-translations
   (quote
    (("i" "⊃")  ("ii" "⫗")  ("e" "⊢")   ("ee" "⊩")  ("n" "¬")
     ("." "·")  (":" "∶")    (".:" "∴")   (":." "∵")   ("::" "∷")
     ("s" "𝐬")  ("t" "𝐭")    ("x" "𝐱")    ("y" "𝐲")    ("N" "ℕ")
     ("v" "𝑣")  ("v0" "𝑣⁰")  ("v1" "𝑣¹")  ("v2" "𝑣²")  ("vn" "𝑣ⁿ")
     ("l" "𝜆")  ("l0" "𝜆⁰")  ("l1" "𝜆¹")  ("l2" "𝜆²")  ("ln" "𝜆ⁿ")
     ("o" "∘")  ("o0" "∘⁰")  ("o1" "∘¹")  ("o2" "∘²")  ("on" "∘ⁿ")
     ("p" "𝑝")  ("p0" "𝑝⁰")  ("p1" "𝑝¹")  ("p2" "𝑝²")  ("pn" "𝑝ⁿ")
     ("1" "𝜋₀") ("10" "𝜋₀⁰") ("11" "𝜋₀¹") ("12" "𝜋₀²") ("1n" "𝜋₀ⁿ")
     ("2" "𝜋₁") ("20" "𝜋₁⁰") ("21" "𝜋₁¹") ("22" "𝜋₁²") ("2n" "𝜋₁ⁿ")
     ("u" "⇑")  ("u0" "⇑⁰")  ("u1" "⇑¹")  ("u2" "⇑²")  ("un" "⇑ⁿ")
     ("d" "⇓")  ("d0" "⇓⁰")  ("d1" "⇓¹")  ("d2" "⇓²")  ("dn" "⇓ⁿ"))))

-}


module A201602.Try16 where

open import Data.Nat
  using (ℕ ; zero ; suc)

open import Data.Product
  using (Σ ; proj₁ ; proj₂ ; _×_)
  renaming (_,_ to ⟨_,_⟩)

infixl 9 !_ 𝑣_ 𝑣²_
infixl 8 𝜋₀_ 𝜋₀²_ 𝜋₁_ 𝜋₁²_
infixl 7 _∘_ _∘²_
infixr 6 ⇑_ ⇑²_ ⇓_ ⇓²_
infixr 5 𝜆_·_ 𝜆²_·_
infixr 4 _∶_ _∷_
infixr 3 ¬_
infixl 2 _,_ _∧_
infixr 1 _⊃_ _⫗_
infixr 0 _⊢[_]_ ⊩[_]_


-- --------------------------------------------------------------------------
--
-- Type and term constructors


Var : Set
Var = ℕ


mutual
  data Ty : Set where
    -- Falsehood
    ⊥ : Ty

    -- Implication
    _⊃_ : Ty → Ty → Ty

    -- Conjunction
    _∧_ : Ty → Ty → Ty

    -- Explicit provability
    _∶_ : Tm → Ty → Ty


  data Tm : Set where
    -- Variable
    𝑣[_]_ : ℕ → Var → Tm

    -- Abstraction (⊃I)
    𝜆[_]_·_ : ℕ → Var → Tm → Tm

    -- Application (⊃E)
    _∘[_]_ : Tm → ℕ → Tm → Tm

    -- Pairing (∧I)
    𝑝[_]⟨_,_⟩ : ℕ → Tm → Tm → Tm

    -- First projection (∧E₀)
    𝜋₀[_]_ : ℕ → Tm → Tm

    -- Second projection (∧E₁)
    𝜋₁[_]_ : ℕ → Tm → Tm

    -- Artëmov’s “proof checker”
    !_ : Tm → Tm

    -- Reification
    ⇑[_]_ : ℕ → Tm → Tm

    -- Reflection
    ⇓[_]_ : ℕ → Tm → Tm


-- --------------------------------------------------------------------------
--
-- Example types


-- Truth
⊤ : Ty
⊤ = ⊥ ⊃ ⊥

-- Negation
¬_ : Ty → Ty
¬ A = A ⊃ ⊥

-- Equivalence
_⫗_ : Ty → Ty → Ty
A ⫗ B = A ⊃ B ∧ B ⊃ A


-- --------------------------------------------------------------------------
--
-- Simplified notation for level 1 and 2 term constructors


𝑣_ : Var → Tm
𝑣 x = 𝑣[ 1 ] x

𝜆_·_ : Var → Tm → Tm
𝜆 x · t = 𝜆[ 1 ] x · t

_∘_ : Tm → Tm → Tm
t ∘ s = t ∘[ 1 ] s

𝑝⟨_,_⟩ : Tm → Tm → Tm
𝑝⟨ t , s ⟩ = 𝑝[ 1 ]⟨ t , s ⟩

𝜋₀_ : Tm → Tm
𝜋₀ t = 𝜋₀[ 1 ] t

𝜋₁_ : Tm → Tm
𝜋₁ t = 𝜋₁[ 1 ] t

⇑_ : Tm → Tm
⇑ t = ⇑[ 1 ] t

⇓_ : Tm → Tm
⇓ t = ⇓[ 1 ] t


𝑣²_ : Var → Tm
𝑣² x₂ = 𝑣[ 2 ] x₂

𝜆²_·_ : Var → Tm → Tm
𝜆² x₂ · t₂ = 𝜆[ 2 ] x₂ · t₂

_∘²_ : Tm → Tm → Tm
t₂ ∘² s₂ = t₂ ∘[ 2 ] s₂

𝑝²⟨_,_⟩ : Tm → Tm → Tm
𝑝²⟨ t₂ , s₂ ⟩ = 𝑝[ 2 ]⟨ t₂ , s₂ ⟩

𝜋₀²_ : Tm → Tm
𝜋₀² t₂ = 𝜋₀[ 2 ] t₂

𝜋₁²_ : Tm → Tm
𝜋₁² t₂ = 𝜋₁[ 2 ] t₂

⇑²_ : Tm → Tm
⇑² t₂ = ⇑[ 2 ] t₂

⇓²_ : Tm → Tm
⇓² t₂ = ⇓[ 2 ] t₂


-- --------------------------------------------------------------------------
--
-- Generic vectors


data Vec (X : Set) : ℕ → Set where
  []  : Vec X zero
  _∷_ : ∀{n} → X → Vec X n → Vec X (suc n)


append : ∀{n} {X : Set}
        → Vec X n → X → Vec X (suc n)
append []      y = y ∷ []
append (x ∷ 𝐱) y = x ∷ append 𝐱 y

foldr : ∀{n} {X : Set} (Y : ℕ → Set)
      → (∀{k} → X → Y k → Y (suc k)) → Y zero → Vec X n → Y n
foldr Y f y₀ []      = y₀
foldr Y f y₀ (x ∷ 𝐱) = f x (foldr Y f y₀ 𝐱)

ixMap : ∀{n} {X Y : Set}
      → (ℕ → X → Y) → Vec X n → Vec Y n
ixMap {zero}  f []      = []
ixMap {suc n} f (x ∷ 𝐱) = f (suc n) x ∷ ixMap f 𝐱

ixZipWith : ∀{n} {X Y Z : Set}
          → (ℕ → X → Y → Z) → Vec X n → Vec Y n → Vec Z n
ixZipWith {zero}  f []      []       = []
ixZipWith {suc n} f (x ∷ 𝐱) (y ∷ 𝐲) = f (suc n) x y ∷ ixZipWith f 𝐱 𝐲


map : ∀{n} {X Y : Set}
    → (X → Y) → Vec X n → Vec Y n
map f = ixMap (λ _ x → f x)

zipWith : ∀{n} {X Y Z : Set}
        → (X → Y → Z) → Vec X n → Vec Y n → Vec Z n
zipWith f = ixZipWith (λ _ x y → f x y)


-- --------------------------------------------------------------------------
--
-- Vector notation for level n type assertions


Vars : ℕ → Set
Vars = Vec Var

Tms : ℕ → Set
Tms = Vec Tm


*ⁿ_∷_ : ∀{n} → Tms n → Ty → Ty
*ⁿ 𝐭 ∷ A = foldr (λ _ → Ty) _∶_ A 𝐭

𝑣ⁿ_∷_ : ∀{n} → Vars n → Ty → Ty
𝑣ⁿ 𝐱 ∷ A = *ⁿ (ixMap 𝑣[_]_ 𝐱) ∷ A

𝜆ⁿ_·_∷_ : ∀{n} → Vars n → Tms n → Ty → Ty
𝜆ⁿ 𝐱 · 𝐭 ∷ A = *ⁿ (ixZipWith 𝜆[_]_·_ 𝐱 𝐭) ∷ A

_∘ⁿ_∷_ : ∀{n} → Tms n → Tms n → Ty → Ty
𝐭 ∘ⁿ 𝐬 ∷ A = *ⁿ (ixZipWith (λ n t s → t ∘[ n ] s) 𝐭 𝐬) ∷ A

𝑝ⁿ⟨_,_⟩∷_ : ∀{n} → Tms n → Tms n → Ty → Ty
𝑝ⁿ⟨ 𝐭 , 𝐬 ⟩∷ A = *ⁿ (ixZipWith 𝑝[_]⟨_,_⟩ 𝐭 𝐬) ∷ A

𝜋₀ⁿ_∷_ : ∀{n} → Tms n → Ty → Ty
𝜋₀ⁿ 𝐭 ∷ A = *ⁿ (ixMap 𝜋₀[_]_ 𝐭) ∷ A

𝜋₁ⁿ_∷_ : ∀{n} → Tms n → Ty → Ty
𝜋₁ⁿ 𝐭 ∷ A = *ⁿ (ixMap 𝜋₁[_]_ 𝐭) ∷ A

⇑ⁿ_∷_ : ∀{n} → Tms n → Ty → Ty
⇑ⁿ 𝐭 ∷ A = *ⁿ (ixMap ⇑[_]_ 𝐭) ∷ A

⇓ⁿ_∷_ : ∀{n} → Tms n → Ty → Ty
⇓ⁿ 𝐭 ∷ A = *ⁿ (ixMap ⇓[_]_ 𝐭) ∷ A


-- --------------------------------------------------------------------------
--
-- Typing contexts


data Cx : ℕ → Set where
  ∅   : Cx zero
  _,_ : ∀{m} → Cx m → Ty → Cx (suc m)


data _∈_  : ∀{m} → Ty → Cx m → Set where
  Z  : ∀{m} {Γ : Cx m} {A : Ty}
     → A ∈ (Γ , A)

  S_ : ∀{m} {Γ : Cx m} {A B : Ty}
     → A ∈ Γ
     → A ∈ (Γ , B)


-- --------------------------------------------------------------------------
--
-- Typing judgment


data _⊢[_]_ {m : ℕ} (Γ : Cx m) (n : ℕ) : Ty → Set where
  M𝑣ⁿ  : {𝐭 : Tms n} {A : Ty}
       → (*ⁿ 𝐭 ∷ A) ∈ Γ
       → Γ ⊢[ n ] *ⁿ 𝐭 ∷ A

  M𝜆ⁿ  : {𝐱 : Vars n} {𝐭 : Tms n} {A B : Ty}
       → Γ , 𝑣ⁿ 𝐱 ∷ A ⊢[ n ] *ⁿ 𝐭 ∷ B
       → Γ ⊢[ n ] 𝜆ⁿ 𝐱 · 𝐭 ∷ (A ⊃ B)

  M∘ⁿ  : {𝐭 𝐬 : Tms n} {A B : Ty}
       → Γ ⊢[ n ] *ⁿ 𝐭 ∷ (A ⊃ B)    → Γ ⊢[ n ] *ⁿ 𝐬 ∷ A
       → Γ ⊢[ n ] 𝐭 ∘ⁿ 𝐬 ∷ B

  M𝑝ⁿ  : {𝐭 𝐬 : Tms n} {A B : Ty}
       → Γ ⊢[ n ] *ⁿ 𝐭 ∷ A          → Γ ⊢[ n ] *ⁿ 𝐬 ∷ B
       → Γ ⊢[ n ] 𝑝ⁿ⟨ 𝐭 , 𝐬 ⟩∷ (A ∧ B)

  M𝜋₀ⁿ : {𝐭 : Tms n} {A B : Ty}
       → Γ ⊢[ n ] *ⁿ 𝐭 ∷ (A ∧ B)
       → Γ ⊢[ n ] 𝜋₀ⁿ 𝐭 ∷ A

  M𝜋₁ⁿ : {𝐭 : Tms n} {A B : Ty}
       → Γ ⊢[ n ] *ⁿ 𝐭 ∷ (A ∧ B)
       → Γ ⊢[ n ] 𝜋₁ⁿ 𝐭 ∷ B

  M⇑ⁿ  : {𝐭 : Tms n} {u : Tm} {A : Ty}
       → Γ ⊢[ n ] *ⁿ 𝐭 ∷ (u ∶ A)
       → Γ ⊢[ n ] ⇑ⁿ 𝐭 ∷ (! u ∶ u ∶ A)

  M⇓ⁿ  : {𝐭 : Tms n} {u : Tm} {A : Ty}
       → Γ ⊢[ n ] *ⁿ 𝐭 ∷ (u ∶ A)
       → Γ ⊢[ n ] ⇓ⁿ 𝐭 ∷ A


⊩[_]_  : ℕ → Ty → Set
⊩[ n ] A = ∀{m} {Γ : Cx m} → Γ ⊢[ n ] A


-- --------------------------------------------------------------------------
--
-- Simplified notation for level 0 typing rules


M𝑣⁰  : ∀{A m} {Γ : Cx m}
     → A ∈ Γ
     → Γ ⊢[ 0 ] A
M𝑣⁰ = M𝑣ⁿ {𝐭 = []}

M𝑣¹⁻¹  : ∀{u A m} {Γ : Cx m}
       → (u ∶ A) ∈ Γ
       → Γ ⊢[ 0 ] u ∶ A
M𝑣¹⁻¹ = M𝑣ⁿ {𝐭 = []}

M𝜆⁰  : ∀{A B m} {Γ : Cx m}
     → Γ , A ⊢[ 0 ] B
     → Γ ⊢[ 0 ] A ⊃ B
M𝜆⁰ = M𝜆ⁿ {𝐱 = []} {𝐭 = []}

M∘⁰  : ∀{A B m} {Γ : Cx m}
     → Γ ⊢[ 0 ] A ⊃ B    → Γ ⊢[ 0 ] A
     → Γ ⊢[ 0 ] B
M∘⁰ = M∘ⁿ {𝐭 = []} {𝐬 = []}

M𝑝⁰  : ∀{A B m} {Γ : Cx m}
     → Γ ⊢[ 0 ] A        → Γ ⊢[ 0 ] B
     → Γ ⊢[ 0 ] A ∧ B
M𝑝⁰ = M𝑝ⁿ {𝐭 = []} {𝐬 = []}

M𝜋₀⁰ : ∀{A B m} {Γ : Cx m}
     → Γ ⊢[ 0 ] A ∧ B
     → Γ ⊢[ 0 ] A
M𝜋₀⁰ = M𝜋₀ⁿ {𝐭 = []}

M𝜋₁⁰ : ∀{A B m} {Γ : Cx m}
     → Γ ⊢[ 0 ] A ∧ B
     → Γ ⊢[ 0 ] B
M𝜋₁⁰ = M𝜋₁ⁿ {𝐭 = []}

M⇑⁰  : ∀{u A m} {Γ : Cx m}
     → Γ ⊢[ 0 ] u ∶ A
     → Γ ⊢[ 0 ] ! u ∶ u ∶ A
M⇑⁰ = M⇑ⁿ {𝐭 = []}

M⇓⁰  : ∀{u A m} {Γ : Cx m}
     → Γ ⊢[ 0 ] u ∶ A
     → Γ ⊢[ 0 ] A
M⇓⁰ = M⇓ⁿ {𝐭 = []}


-- --------------------------------------------------------------------------
--
-- Simplified notation for level 1 typing rules


M𝑣¹  : ∀{t A m} {Γ : Cx m}
     → (t ∶ A) ∈ Γ
     → Γ ⊢[ 1 ] t ∶ A
M𝑣¹ {t} = M𝑣ⁿ {𝐭 = t ∷ []}

M𝜆¹  : ∀{x t A B m} {Γ : Cx m}
     → Γ , 𝑣 x ∶ A ⊢[ 1 ] t ∶ B
     → Γ ⊢[ 1 ] 𝜆 x · t ∶ (A ⊃ B)
M𝜆¹ {x} {t} = M𝜆ⁿ {𝐱 = x ∷ []} {𝐭 = t ∷ []}

M∘¹  : ∀{t s A B m} {Γ : Cx m}
     → Γ ⊢[ 1 ] t ∶ (A ⊃ B)    → Γ ⊢[ 1 ] s ∶ A
     → Γ ⊢[ 1 ] t ∘ s ∶ B
M∘¹ {t} {s} = M∘ⁿ {𝐭 = t ∷ []} {𝐬 = s ∷ []}

M𝑝¹  : ∀{t s A B m} {Γ : Cx m}
     → Γ ⊢[ 1 ] t ∶ A          → Γ ⊢[ 1 ] s ∶ B
     → Γ ⊢[ 1 ] 𝑝⟨ t , s ⟩ ∶ (A ∧ B)
M𝑝¹ {t} {s} = M𝑝ⁿ {𝐭 = t ∷ []} {𝐬 = s ∷ []}

M𝜋₀¹ : ∀{t A B m} {Γ : Cx m}
     → Γ ⊢[ 1 ] t ∶ (A ∧ B)
     → Γ ⊢[ 1 ] 𝜋₀ t ∶ A
M𝜋₀¹ {t} = M𝜋₀ⁿ {𝐭 = t ∷ []}

M𝜋₁¹ : ∀{t A B m} {Γ : Cx m}
     → Γ ⊢[ 1 ] t ∶ (A ∧ B)
     → Γ ⊢[ 1 ] 𝜋₁ t ∶ B
M𝜋₁¹ {t} = M𝜋₁ⁿ {𝐭 = t ∷ []}

M⇑¹  : ∀{t u A m} {Γ : Cx m}
     → Γ ⊢[ 1 ] t ∶ u ∶ A
     → Γ ⊢[ 1 ] ⇑ t ∶ ! u ∶ u ∶ A
M⇑¹ {t} = M⇑ⁿ {𝐭 = t ∷ []}

M⇓¹  : ∀{t u A m} {Γ : Cx m}
     → Γ ⊢[ 1 ] t ∶ u ∶ A
     → Γ ⊢[ 1 ] ⇓ t ∶ A
M⇓¹ {t} = M⇓ⁿ {𝐭 = t ∷ []}


-- --------------------------------------------------------------------------
--
-- Simplified notation for level 2 typing rules


M𝑣²  : ∀{t₂ t₁ A m} {Γ : Cx m}
     → (t₂ ∶ t₁ ∶ A) ∈ Γ
     → Γ ⊢[ 2 ] t₂ ∶ t₁ ∶ A
M𝑣² {t₂} {t₁} = M𝑣ⁿ {𝐭 = t₂ ∷ t₁ ∷ []}

M𝜆²  : ∀{x₂ x₁ t₂ t₁ A B m} {Γ : Cx m}
     → Γ , 𝑣² x₂ ∶ 𝑣 x₁ ∶ A ⊢[ 2 ] t₂ ∶ t₁ ∶ B
     → Γ ⊢[ 2 ] 𝜆² x₂ · t₂ ∶ 𝜆 x₁ · t₁ ∶ (A ⊃ B)
M𝜆² {x₂} {x₁} {t₂} {t₁} = M𝜆ⁿ {𝐱 = x₂ ∷ x₁ ∷ []} {𝐭 = t₂ ∷ t₁ ∷ []}

M∘²  : ∀{t₂ t₁ s₂ s₁ A B m} {Γ : Cx m}
     → Γ ⊢[ 2 ] t₂ ∶ t₁ ∶ (A ⊃ B)    → Γ ⊢[ 2 ] s₂ ∶ s₁ ∶ A
     → Γ ⊢[ 2 ] t₂ ∘² s₂ ∶ t₁ ∘ s₁ ∶ B
M∘² {t₂} {t₁} {s₂} {s₁} = M∘ⁿ {𝐭 = t₂ ∷ t₁ ∷ []} {𝐬 = s₂ ∷ s₁ ∷ []}

M𝑝²  : ∀{t₂ t₁ s₂ s₁ A B m} {Γ : Cx m}
     → Γ ⊢[ 2 ] t₂ ∶ t₁ ∶ A          → Γ ⊢[ 2 ] s₂ ∶ s₁ ∶ B
     → Γ ⊢[ 2 ] 𝑝²⟨ t₂ , s₂ ⟩ ∶ 𝑝⟨ t₁ , s₁ ⟩ ∶ (A ∧ B)
M𝑝² {t₂} {t₁} {s₂} {s₁} = M𝑝ⁿ {𝐭 = t₂ ∷ t₁ ∷ []} {𝐬 = s₂ ∷ s₁ ∷ []}

M𝜋₀² : ∀{t₂ t₁ A B m} {Γ : Cx m}
     → Γ ⊢[ 2 ] t₂ ∶ t₁ ∶ (A ∧ B)
     → Γ ⊢[ 2 ] 𝜋₀² t₂ ∶ 𝜋₀ t₁ ∶ A
M𝜋₀² {t₂} {t₁} = M𝜋₀ⁿ {𝐭 = t₂ ∷ t₁ ∷ []}

M𝜋₁² : ∀{t₂ t₁ A B m} {Γ : Cx m}
     → Γ ⊢[ 2 ] t₂ ∶ t₁ ∶ (A ∧ B)
     → Γ ⊢[ 2 ] 𝜋₁² t₂ ∶ 𝜋₁ t₁ ∶ B
M𝜋₁² {t₂} {t₁} = M𝜋₁ⁿ {𝐭 = t₂ ∷ t₁ ∷ []}

M⇑²  : ∀{t₂ t₁ u A m} {Γ : Cx m}
     → Γ ⊢[ 2 ] t₂ ∶ t₁ ∶ u ∶ A
     → Γ ⊢[ 2 ] ⇑² t₂ ∶ ⇑ t₁ ∶ ! u ∶ u ∶ A
M⇑² {t₂} {t₁} = M⇑ⁿ {𝐭 = t₂ ∷ t₁ ∷ []}

M⇓²  : ∀{t₂ t₁ u A m} {Γ : Cx m}
     → Γ ⊢[ 2 ] t₂ ∶ t₁ ∶ u ∶ A
     → Γ ⊢[ 2 ] ⇓² t₂ ∶ ⇓ t₁ ∶ A
M⇓² {t₂} {t₁} = M⇓ⁿ {𝐭 = t₂ ∷ t₁ ∷ []}


-- --------------------------------------------------------------------------
--
-- Example terms for level 0, 1, and 2 IKS combinators


-- S4: A ⊃ A
eI⁰ : ∀{A}
    → ⊩[ 0 ] A ⊃ A
eI⁰ = M𝜆⁰ (M𝑣⁰ Z)

-- S4: □(A ⊃ A)
eI¹ : ∀{A x}
    → ⊩[ 1 ] 𝜆 x · 𝑣 x
        ∶ (A ⊃ A)
eI¹ = M𝜆¹ (M𝑣¹ Z)

-- S4: □□(A ⊃ A)
eI² : ∀{A x u}
    → ⊩[ 2 ] 𝜆² u · 𝑣² u
        ∶ 𝜆 x · 𝑣 x
          ∶ (A ⊃ A)
eI² = M𝜆² (M𝑣² Z)


-- S4: A ⊃ B ⊃ A
eK⁰ : ∀{A B}
    → ⊩[ 0 ] A ⊃ B ⊃ A
eK⁰ = M𝜆⁰ (M𝜆⁰ (M𝑣⁰ (S Z)))

-- S4: □(A ⊃ B ⊃ A)
eK¹ : ∀{A B x y}
    → ⊩[ 1 ] 𝜆 x · 𝜆 y · 𝑣 x
        ∶ (A ⊃ B ⊃ A)
eK¹ = M𝜆¹ (M𝜆¹ (M𝑣¹ (S Z)))

-- S4: □□(A ⊃ B ⊃ A)
eK² : ∀{A B x y u v}
    → ⊩[ 2 ] 𝜆² u · 𝜆² v · 𝑣² u
        ∶ 𝜆 x · 𝜆 y · 𝑣 x
          ∶ (A ⊃ B ⊃ A)
eK² = M𝜆² (M𝜆² (M𝑣² (S Z)))


-- S4: (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
eS⁰ : ∀{A B C}
    → ⊩[ 0 ] (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
eS⁰ = M𝜆⁰ (M𝜆⁰ (M𝜆⁰ (M∘⁰ (M∘⁰ (M𝑣⁰ (S S Z))
                              (M𝑣⁰ Z))
                    (M∘⁰ (M𝑣⁰ (S Z))
                         (M𝑣⁰ Z)))))

-- S4: □((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
eS¹ : ∀{A B C f g x}
    → ⊩[ 1 ] 𝜆 f · 𝜆 g · 𝜆 x · (𝑣 f ∘ 𝑣 x) ∘ (𝑣 g ∘ 𝑣 x)
        ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
eS¹ = M𝜆¹ (M𝜆¹ (M𝜆¹ (M∘¹ (M∘¹ (M𝑣¹ (S S Z))
                              (M𝑣¹ Z))
                    (M∘¹ (M𝑣¹ (S Z))
                         (M𝑣¹ Z)))))

-- S4: □□((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
eS² : ∀{A B C f g x p q u}
    → ⊩[ 2 ] 𝜆² p · 𝜆² q · 𝜆² u · (𝑣² p ∘² 𝑣² u) ∘² (𝑣² q ∘² 𝑣² u)
        ∶ 𝜆 f · 𝜆 g · 𝜆 x · (𝑣 f ∘ 𝑣 x) ∘ (𝑣 g ∘ 𝑣 x)
          ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
eS² = M𝜆² (M𝜆² (M𝜆² (M∘² (M∘² (M𝑣² (S S Z))
                              (M𝑣² Z))
                    (M∘² (M𝑣² (S Z))
                         (M𝑣² Z)))))


-- --------------------------------------------------------------------------
--
-- Example terms for S4 axioms


-- S4: □(A ⊃ B) ⊃ □A ⊃ □B
axK⁰ : ∀{A B f x}
     → ⊩[ 0 ] (f ∶ (A ⊃ B)) ⊃ x ∶ A ⊃ (f ∘ x) ∶ B
axK⁰ = {!M𝜆⁰ (M𝜆⁰ (M∘¹ (M𝑣¹ (S Z))
                     (M𝑣¹ Z)))!}

-- S4: □(□(A ⊃ B) ⊃ □A ⊃ □B)
axK¹ : ∀{A B f x p u}
     → ⊩[ 1 ] 𝜆 p · 𝜆 u · 𝑣 p ∘² 𝑣 u
         ∶ (f ∶ (A ⊃ B) ⊃ x ∶ A ⊃ (f ∘ x) ∶ B)
axK¹ = {!M𝜆¹ (M𝜆¹ (M∘² (M𝑣¹ (S Z))
                     (M𝑣¹ Z)))!}

-- S4: □A ⊃ A
axT⁰ : ∀{A x}
     → ⊩[ 0 ] x ∶ A ⊃ A
axT⁰ = {!M𝜆⁰ (M⇓⁰ (M𝑣¹ Z))!}

-- S4: □A ⊃ □□A
ax4⁰ : ∀{A x}
     → ⊩[ 0 ] x ∶ A ⊃ ! x ∶ x ∶ A
ax4⁰ = {!M𝜆⁰ (M⇑⁰ (M𝑣¹ Z))!}


-- --------------------------------------------------------------------------
--
-- Terms for example 1, p. 28 [1]


-- -- S4: □(□A ⊃ A)
-- e11 : ∀{A x y}
--     → ⊩[ 1 ] 𝜆 y · ⇓ 𝑣 y
--         ∶ (x ∶ A ⊃ A)
-- e11 = M𝜆¹ (M⇓¹ (M𝑣² Z))

-- -- S4: □(□A ⊃ □□A)
-- e12 : ∀{A x y}
--     → ⊩[ 1 ] 𝜆 y · ⇑ 𝑣 y
--         ∶ (x ∶ A ⊃ ! x ∶ x ∶ A)
-- e12 = M𝜆¹ (M⇑¹ (M𝑣² Z))

-- -- S4: □□(A ⊃ B ⊃ A ∧ B)
-- e13 : ∀{A B x y u v}
--     → ⊩[ 2 ] 𝜆² u · 𝜆² v · 𝑝²⟨ 𝑣² u , 𝑣² v ⟩
--         ∶ 𝜆 x · 𝜆 y · 𝑝⟨ 𝑣 x , 𝑣 y ⟩
--           ∶ (A ⊃ B ⊃ A ∧ B)
-- e13 = M𝜆² (M𝜆² (M𝑝² (M𝑣² (S Z))
--                     (M𝑣² Z)))

-- -- S4: □(□A ⊃ □B ⊃ □□(A ∧ B))
-- e14 : ∀{A B x y u v}
--     → ⊩[ 1 ] 𝜆 u · 𝜆 v · ⇑ 𝑝²⟨ 𝑣 u , 𝑣 v ⟩
--         ∶ (x ∶ A ⊃ y ∶ B ⊃ ! 𝑝⟨ x , y ⟩ ∶ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
-- e14 = M𝜆¹ (M𝜆¹ (M⇑¹ (M𝑝² (M𝑣¹ (S Z))
--                          (M𝑣¹ Z))))


-- -- --------------------------------------------------------------------------
-- --
-- -- Additional example terms


-- -- S4: □(□A ⊃ □B ⊃ □(A ∧ B))
-- ex1 : ∀{A B x y u v}
--     → ⊩[ 1 ] 𝜆 u · 𝜆 v · 𝑝²⟨ 𝑣 u , 𝑣 v ⟩
--         ∶ (x ∶ A ⊃ y ∶ B ⊃ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
-- ex1 = M𝜆¹ (M𝜆¹ (M𝑝² (M𝑣¹ (S Z))
--                     (M𝑣¹ Z)))

-- -- S4: □(□A ∧ □B ⊃ □□(A ∧ B))
-- ex2 : ∀{A B x y u}
--     → ⊩[ 1 ] 𝜆 u · ⇑ 𝑝²⟨ 𝜋₀ 𝑣 u , 𝜋₁ 𝑣 u ⟩
--         ∶ (x ∶ A ∧ y ∶ B ⊃ ! 𝑝⟨ x , y ⟩ ∶ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
-- ex2 = M𝜆¹ (M⇑¹ (M𝑝² (M𝜋₀¹ (M𝑣¹ Z))
--                     (M𝜋₁¹ (M𝑣¹ Z))))

-- -- S4: □(□A ∧ □B ⊃ □(A ∧ B))
-- ex3 : ∀{A B x y u}
--     → ⊩[ 1 ] 𝜆 u · 𝑝²⟨ 𝜋₀ 𝑣 u , 𝜋₁ 𝑣 u ⟩
--         ∶ (x ∶ A ∧ y ∶ B ⊃ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
-- ex3 = M𝜆¹ (M𝑝² (M𝜋₀¹ (M𝑣¹ Z))
--                (M𝜋₁¹ (M𝑣¹ Z)))


-- -- --------------------------------------------------------------------------
-- --
-- -- Terms for example 2, pp. 31–32 [1]


-- e2 : ∀{A x₃ x₂ x₁}
--    → ⊩[ 2 ] 𝜆² x₃ · ⇓² ⇑² 𝑣² x₃
--        ∶ 𝜆 x₂ · ⇓ ⇑ 𝑣 x₂
--          ∶ (x₁ ∶ A ⊃ x₁ ∶ A)
-- e2 = M𝜆² (M⇓² (M⇑² (M𝑣² Z)))

-- e2′ : ∀{A x₃ x₂ x₁}
--     → ⊩[ 2 ] 𝜆² x₃ · 𝑣² x₃
--         ∶ 𝜆 x₂ · 𝑣 x₂
--           ∶ (x₁ ∶ A ⊃ x₁ ∶ A)
-- e2′ = M𝜆² (M𝑣² Z)


-- -- --------------------------------------------------------------------------
-- --
-- -- Weakening


-- data _≲_ : ∀{m m′} → Cx m → Cx m′ → Set where
--   base : ∅ ≲ ∅

--   drop : ∀{A m m′} {Γ : Cx m} {Γ′ : Cx m′}
--        → Γ ≲ Γ′
--        → Γ ≲ (Γ′ , A)

--   keep : ∀{A m m′} {Γ : Cx m} {Γ′ : Cx m′}
--        → Γ ≲ Γ′
--        → (Γ , A) ≲ (Γ′ , A)


-- ∅≲Γ : ∀{m} {Γ : Cx m} → ∅ ≲ Γ
-- ∅≲Γ {Γ = ∅}     = base
-- ∅≲Γ {Γ = Γ , A} = drop ∅≲Γ


-- Γ≲Γ : ∀{m} {Γ : Cx m} → Γ ≲ Γ
-- Γ≲Γ {Γ = ∅}     = base
-- Γ≲Γ {Γ = Γ , A} = keep Γ≲Γ


-- wk∈ : ∀{A m m′} {Γ : Cx m} {Γ′ : Cx m′}
--     → Γ ≲ Γ′    → A ∈ Γ
--     → A ∈ Γ′
-- wk∈ base     ()
-- wk∈ (keep P) Z     = Z
-- wk∈ (keep P) (S i) = S (wk∈ P i)
-- wk∈ (drop P) i     = S (wk∈ P i)


-- wk⊢ : ∀{A m m′ n} {Γ : Cx m} {Γ′ : Cx m′}
--     → Γ ≲ Γ′    → Γ ⊢[ n ] A
--     → Γ′ ⊢[ n ] A
-- wk⊢ P (M𝑣ⁿ  {𝐭 = 𝐭} i)         = M𝑣ⁿ  {𝐭 = 𝐭} (wk∈ P i)
-- wk⊢ P (M𝜆ⁿ  {𝐱 = 𝐱} {𝐭} D)     = M𝜆ⁿ  {𝐱 = 𝐱} {𝐭} (wk⊢ (keep P) D)
-- wk⊢ P (M∘ⁿ  {𝐭 = 𝐭} {𝐬} Dₜ Dₛ) = M∘ⁿ  {𝐭 = 𝐭} {𝐬} (wk⊢ P Dₜ) (wk⊢ P Dₛ)
-- wk⊢ P (M𝑝ⁿ  {𝐭 = 𝐭} {𝐬} Dₜ Dₛ) = M𝑝ⁿ  {𝐭 = 𝐭} {𝐬} (wk⊢ P Dₜ) (wk⊢ P Dₛ)
-- wk⊢ P (M𝜋₀ⁿ {𝐭 = 𝐭} D)         = M𝜋₀ⁿ {𝐭 = 𝐭} (wk⊢ P D)
-- wk⊢ P (M𝜋₁ⁿ {𝐭 = 𝐭} D)         = M𝜋₁ⁿ {𝐭 = 𝐭} (wk⊢ P D)
-- wk⊢ P (M⇑ⁿ  {𝐭 = 𝐭} D)         = M⇑ⁿ  {𝐭 = 𝐭} (wk⊢ P D)
-- wk⊢ P (M⇓ⁿ  {𝐭 = 𝐭} D)         = M⇓ⁿ  {𝐭 = 𝐭} (wk⊢ P D)


-- -- --------------------------------------------------------------------------
-- --
-- -- Contraction


-- data _≳_ : ∀{m m′} → Cx m → Cx m′ → Set where
--   base : ∅ ≳ ∅

--   once : ∀{A m m′} {Γ : Cx m} {Γ′ : Cx m′}
--        → Γ ≳ Γ′
--        → (Γ , A) ≳ (Γ′ , A)

--   more : ∀{A m m′} {Γ : Cx m} {Γ′ : Cx m′}
--        → Γ ≳ Γ′
--        → (Γ , A , A) ≳ (Γ′ , A)


-- cn∈ : ∀{A m m′} {Γ : Cx m} {Γ′ : Cx m′}
--     → Γ ≳ Γ′    → A ∈ Γ
--     → A ∈ Γ′
-- cn∈ base     ()
-- cn∈ (once P) Z     = Z
-- cn∈ (once P) (S i) = S (cn∈ P i)
-- cn∈ (more P) Z     = Z
-- cn∈ (more P) (S i) = cn∈ (once P) i


-- cn⊢ : ∀{A m m′ n} {Γ : Cx m} {Γ′ : Cx m′}
--     → Γ ≳ Γ′    → Γ ⊢[ n ] A
--     → Γ′ ⊢[ n ] A
-- cn⊢ P (M𝑣ⁿ  {𝐭 = 𝐭} i)         = M𝑣ⁿ  {𝐭 = 𝐭} (cn∈ P i)
-- cn⊢ P (M𝜆ⁿ  {𝐱 = 𝐱} {𝐭} D)     = M𝜆ⁿ  {𝐱 = 𝐱} {𝐭} (cn⊢ (once P) D)
-- cn⊢ P (M∘ⁿ  {𝐭 = 𝐭} {𝐬} Dₜ Dₛ) = M∘ⁿ  {𝐭 = 𝐭} {𝐬} (cn⊢ P Dₜ) (cn⊢ P Dₛ)
-- cn⊢ P (M𝑝ⁿ  {𝐭 = 𝐭} {𝐬} Dₜ Dₛ) = M𝑝ⁿ  {𝐭 = 𝐭} {𝐬} (cn⊢ P Dₜ) (cn⊢ P Dₛ)
-- cn⊢ P (M𝜋₀ⁿ {𝐭 = 𝐭} D)         = M𝜋₀ⁿ {𝐭 = 𝐭} (cn⊢ P D)
-- cn⊢ P (M𝜋₁ⁿ {𝐭 = 𝐭} D)         = M𝜋₁ⁿ {𝐭 = 𝐭} (cn⊢ P D)
-- cn⊢ P (M⇑ⁿ  {𝐭 = 𝐭} D)         = M⇑ⁿ  {𝐭 = 𝐭} (cn⊢ P D)
-- cn⊢ P (M⇓ⁿ  {𝐭 = 𝐭} D)         = M⇓ⁿ  {𝐭 = 𝐭} (cn⊢ P D)


-- -- --------------------------------------------------------------------------
-- --
-- -- Exchange


-- data _≈_ : ∀{m} → Cx m → Cx m → Set where
--   base : ∅ ≈ ∅

--   just : ∀{A m} {Γ Γ′ : Cx m}
--        → Γ ≈ Γ′
--        → (Γ , A) ≈ (Γ′ , A)

--   same : ∀{A B m} {Γ Γ′ : Cx m}
--        → Γ ≈ Γ′
--        → (Γ , A , B) ≈ (Γ′ , A , B)

--   diff : ∀{A B m} {Γ Γ′ : Cx m}
--        → Γ ≈ Γ′
--        → (Γ , B , A) ≈ (Γ′ , A , B)


-- ex∈ : ∀{A m} {Γ Γ′ : Cx m}
--     → Γ ≈ Γ′    → A ∈ Γ
--     → A ∈ Γ′
-- ex∈ base     ()
-- ex∈ (just P) Z         = Z
-- ex∈ (just P) (S i)     = S (ex∈ P i)
-- ex∈ (same P) Z         = Z
-- ex∈ (same P) (S Z)     = S Z
-- ex∈ (same P) (S (S i)) = S (S (ex∈ P i))
-- ex∈ (diff P) Z         = S Z
-- ex∈ (diff P) (S Z)     = Z
-- ex∈ (diff P) (S (S i)) = S (S (ex∈ P i))


-- ex⊢ : ∀{A m n} {Γ Γ′ : Cx m}
--     → Γ ≈ Γ′    → Γ ⊢[ n ] A
--     → Γ′ ⊢[ n ] A
-- ex⊢ P (M𝑣ⁿ  {𝐭 = 𝐭} i)         = M𝑣ⁿ  {𝐭 = 𝐭} (ex∈ P i)
-- ex⊢ P (M𝜆ⁿ  {𝐱 = 𝐱} {𝐭} D)     = M𝜆ⁿ  {𝐱 = 𝐱} {𝐭} (ex⊢ (just P) D)
-- ex⊢ P (M∘ⁿ  {𝐭 = 𝐭} {𝐬} Dₜ Dₛ) = M∘ⁿ  {𝐭 = 𝐭} {𝐬} (ex⊢ P Dₜ) (ex⊢ P Dₛ)
-- ex⊢ P (M𝑝ⁿ  {𝐭 = 𝐭} {𝐬} Dₜ Dₛ) = M𝑝ⁿ  {𝐭 = 𝐭} {𝐬} (ex⊢ P Dₜ) (ex⊢ P Dₛ)
-- ex⊢ P (M𝜋₀ⁿ {𝐭 = 𝐭} D)         = M𝜋₀ⁿ {𝐭 = 𝐭} (ex⊢ P D)
-- ex⊢ P (M𝜋₁ⁿ {𝐭 = 𝐭} D)         = M𝜋₁ⁿ {𝐭 = 𝐭} (ex⊢ P D)
-- ex⊢ P (M⇑ⁿ  {𝐭 = 𝐭} D)         = M⇑ⁿ  {𝐭 = 𝐭} (ex⊢ P D)
-- ex⊢ P (M⇓ⁿ  {𝐭 = 𝐭} D)         = M⇓ⁿ  {𝐭 = 𝐭} (ex⊢ P D)


-- -- --------------------------------------------------------------------------
-- --
-- -- Theorem 1 (Internalisation principle), p. 29 [1]


-- level : ∀{A m n} {Γ : Cx m} → Γ ⊢[ n ] A → ℕ
-- level {n = n} D = n


-- prefix : ∀{m} → ℕ → Vars m → Cx m → Cx m
-- prefix n []      ∅       = ∅
-- prefix n (x ∷ 𝐱) (Γ , A) = prefix n 𝐱 Γ , 𝑣[ suc n ] x ∶ A


-- postulate fresh : Var    -- XXX: Fix this!


-- in∈ : ∀{A m} {𝐱 : Vars m} {Γ : Cx m}
--     → (n : ℕ)    → A ∈ Γ
--     → Σ Var (λ x → (𝑣[ suc n ] x ∶ A) ∈ prefix n 𝐱 Γ)
-- in∈ {𝐱 = []}    n ()
-- in∈ {𝐱 = x ∷ _} n Z     = ⟨ x , Z ⟩
-- in∈ {𝐱 = _ ∷ 𝐱} n (S i) = let ⟨ y , j ⟩ = in∈ {𝐱 = 𝐱} n i
--                           in
--                             ⟨ y , S j ⟩


-- -- in⊢ : ∀{A m} {𝐱 : Vars m} {Γ : Cx m}
-- --     → (n : ℕ)    → Γ ⊢ A
-- --     → Σ (Vars m → Tm) (λ t → prefix n 𝐱 Γ ⊢ t 𝐱 ∶ A)

-- -- in⊢ {𝐱 = 𝐱} n (M𝑣ⁿ {.n} {𝐭 = 𝐭} i)
-- --     = let ⟨ x , j ⟩ = in∈ {𝐱 = 𝐱} i
-- --       in
-- --         ⟨ (λ _ → 𝑣[ suc n ] x)
-- --         , M𝑣ⁿ {𝐭 = 𝑣[ suc n ] x ∷ 𝐭} {!!}
-- --         ⟩

-- -- in⊢ {𝐱 = 𝐱} n (M𝜆ⁿ {.n} {𝐱 = 𝐲} {𝐭} D)
-- --     = let xₘ₊₁      = fresh
-- --           ⟨ s , C ⟩ = in⊢ {𝐱 = xₘ₊₁ ∷ 𝐱} D
-- --       in
-- --         ⟨ (λ 𝐱 → 𝜆[ suc n ] xₘ₊₁ · s (xₘ₊₁ ∷ 𝐱))
-- --         , M𝜆ⁿ {𝐱 = xₘ₊₁ ∷ 𝐲} {𝐭 = s (xₘ₊₁ ∷ 𝐱) ∷ 𝐭} {!!}
-- --         ⟩

-- -- in⊢ {𝐱 = 𝐱} n (M∘ⁿ {.n} {𝐭} {𝐬} Dₜ Dₛ)
-- --     = let ⟨ sₜ , Cₜ ⟩ = in⊢ {𝐱 = 𝐱} Dₜ
-- --           ⟨ sₛ , Cₛ ⟩ = in⊢ {𝐱 = 𝐱} Dₛ
-- --       in
-- --         ⟨ (λ 𝐱 → sₜ 𝐱 ∘[ suc n ] sₛ 𝐱)
-- --         , M∘ⁿ {𝐭 = sₜ 𝐱 ∷ 𝐭} {𝐬 = sₛ 𝐱 ∷ 𝐬} Cₜ Cₛ
-- --         ⟩

-- -- in⊢ {𝐱 = 𝐱} n (M𝑝ⁿ {.n} {𝐭} {𝐬} Dₜ Dₛ)
-- --     = let ⟨ sₜ , Cₜ ⟩ = in⊢ {𝐱 = 𝐱} Dₜ
-- --           ⟨ sₛ , Cₛ ⟩ = in⊢ {𝐱 = 𝐱} Dₛ
-- --       in
-- --         ⟨ (λ 𝐱 → 𝑝[ suc n ]⟨ sₜ 𝐱 , sₛ 𝐱 ⟩)
-- --         , M𝑝ⁿ {𝐭 = sₜ 𝐱 ∷ 𝐭} {𝐬 = sₛ 𝐱 ∷ 𝐬} Cₜ Cₛ
-- --         ⟩

-- -- in⊢ {𝐱 = 𝐱} n (M𝜋₀ⁿ {.n} {𝐭} D)
-- --     = let ⟨ s , C ⟩ = in⊢ {𝐱 = 𝐱} D
-- --       in
-- --         ⟨ (λ 𝐱 → 𝜋₀[ suc n ] s 𝐱)
-- --         , M𝜋₀ⁿ {𝐭 = s 𝐱 ∷ 𝐭} C
-- --         ⟩

-- -- in⊢ {𝐱 = 𝐱} n (M𝜋₁ⁿ {.n} {𝐭} D)
-- --     = let ⟨ s , C ⟩ = in⊢ {𝐱 = 𝐱} D
-- --       in
-- --         ⟨ (λ 𝐱 → 𝜋₁[ suc n ] s 𝐱)
-- --         , M𝜋₁ⁿ {𝐭 = s 𝐱 ∷ 𝐭} C
-- --         ⟩

-- -- in⊢ {𝐱 = 𝐱} n (M⇑ⁿ {.n} {𝐭} D)
-- --     = let ⟨ s , C ⟩ = in⊢ {𝐱 = 𝐱} D
-- --       in
-- --         ⟨ (λ 𝐱 → ⇑[ suc n ] s 𝐱)
-- --         , M⇑ⁿ {𝐭 = s 𝐱 ∷ 𝐭} C
-- --         ⟩

-- -- in⊢ {𝐱 = 𝐱} n (M⇓ⁿ {.n} {𝐭} D)
-- --     = let ⟨ s , C ⟩ = in⊢ {𝐱 = 𝐱} D
-- --       in
-- --         ⟨ (λ 𝐱 → ⇓[ suc n ] s 𝐱)
-- --         , M⇓ⁿ {𝐭 = s 𝐱 ∷ 𝐭} C
-- --         ⟩


-- -- -- --------------------------------------------------------------------------
-- -- --
-- -- -- Constructive necessitation


-- -- nec : ∀{A}
-- --     → ∅ ⊢ A
-- --     → Σ Tm (λ t → ⊩ t ∶ A)
-- -- nec D = let ⟨ s , C ⟩ = in⊢ D
-- --         in
-- --           ⟨ s [] , wk⊢ ∅≲Γ C ⟩


-- -- eI¹′ : ∀{A}
-- --      → Σ Tm (λ t → ⊩ t ∶ (A ⊃ A))
-- -- eI¹′ = nec eI⁰

-- -- eI²′ : ∀{x A}
-- --      → Σ Tm (λ t → ⊩ t ∶ 𝜆 x · 𝑣 x ∶ (A ⊃ A))
-- -- eI²′ = nec eI¹

-- -- eI³′ : ∀{u x A}
-- --      → Σ Tm (λ t → ⊩ t ∶ 𝜆² u · 𝑣² u ∶ 𝜆 x · 𝑣 x ∶ (A ⊃ A))
-- -- eI³′ = nec eI²


-- -- eI²″ : ∀{A}
-- --      → Σ Tm (λ t → ⊩ t ∶ 𝜆 fresh · 𝑣 fresh ∶ (A ⊃ A))    -- XXX: Fix this!
-- -- eI²″ = nec (proj₂ (eI¹′))

-- -- eI³″ : ∀{A}
-- --      → Σ Tm (λ t → ⊩ t ∶ 𝜆² fresh · 𝑣² fresh ∶ 𝜆 fresh · 𝑣 fresh ∶ (A ⊃ A))    -- XXX: Fix this!
-- -- eI³″ = nec (proj₂ (eI²′))
