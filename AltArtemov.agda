{-

An implementation of the Alt-Artëmov system λ∞
==============================================

Miëtek Bak  <mietek@bak.io>


Work in progress.  Checked with Agda 2.4.2.5.

For easy editing with Emacs agda-mode, add to your .emacs file:

'(agda-input-user-translations
   (quote
    (("i" "⊃")  ("ii" "⫗")  ("e" "⊢")   ("ee" "⊩")  ("n" "¬")
     ("." "·")  (":" "∶")    (".:" "∴")   (":." "∵")   ("::" "∷")
     ("s" "𝐬")  ("t" "𝐭")    ("x" "𝐱")    ("y" "𝐲")    ("N" "ℕ")
     ("v" "𝑣")  ("v1" "𝑣¹")  ("v2" "𝑣²")  ("v3" "𝑣³")  ("vn" "𝑣ⁿ")
     ("l" "𝜆")  ("l1" "𝜆¹")  ("l2" "𝜆²")  ("l3" "𝜆³")  ("ln" "𝜆ⁿ")
     ("o" "∘")  ("o1" "∘¹")  ("o2" "∘²")  ("o3" "∘³")  ("on" "∘ⁿ")
     ("p" "𝑝")  ("p1" "𝑝¹")  ("p2" "𝑝²")  ("p3" "𝑝³")  ("pn" "𝑝ⁿ")
     ("1" "𝜋₀") ("11" "𝜋₀¹") ("12" "𝜋₀²") ("13" "𝜋₀³") ("1n" "𝜋₀ⁿ")
     ("2" "𝜋₁") ("21" "𝜋₁¹") ("22" "𝜋₁²") ("23" "𝜋₁³") ("2n" "𝜋₁ⁿ")
     ("u" "⇑")  ("u1" "⇑¹")  ("u2" "⇑²")  ("u3" "⇑³")  ("un" "⇑ⁿ")
     ("d" "⇓")  ("d1" "⇓¹")  ("d2" "⇓²")  ("d3" "⇓³")  ("dn" "⇓ⁿ"))))


[1]: Alt, J., Artëmov, S. (2001) Reflective λ-calculus,
     Proceedings of the 2001 International Seminar on Proof Theory in
     Computer Science (PTCS’01), Lecture Notes in Computer Science,
     vol. 2183, pp. 22–37.
     http://dx.doi.org/10.1007/3-540-45504-3_2

-}


module AltArtemov where

open import Data.Nat
  using (ℕ ; zero ; suc)

open import Data.Product
  using (Σ ; proj₁ ; proj₂)
  renaming (_,_ to ⟨_,_⟩)

infixl 9 !_ 𝑣_
infixl 8 𝜋₀_ 𝜋₀²_ 𝜋₁_ 𝜋₁²_
infixl 7 _∘_ _∘²_
infixr 6 ⇑_ ⇑²_ ⇓_ ⇓²_
infixr 5 𝜆_·_ 𝜆²_·_
infixr 4 _∶_ _∷_
infixr 3 ¬_
infixl 2 _,_ _∧_
infixr 1 _⊃_ _⫗_
infixr 0 _⊢_ ⊩_


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
    𝑣_ : Var → Tm

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
𝑣ⁿ 𝐱 ∷ A = *ⁿ (map 𝑣_ 𝐱) ∷ A

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


data _⊢_ {m : ℕ} (Γ : Cx m) : Ty → Set where
  M𝑣   : {A : Ty}
       → A ∈ Γ
       → Γ ⊢ A

  M𝜆ⁿ  : ∀{n} {𝐱 : Vars n} {𝐭 : Tms n} {A B : Ty}
       → Γ , 𝑣ⁿ 𝐱 ∷ A ⊢ *ⁿ 𝐭 ∷ B
       → Γ ⊢ 𝜆ⁿ 𝐱 · 𝐭 ∷ (A ⊃ B)

  M∘ⁿ  : ∀{n} {𝐭 𝐬 : Tms n} {A B : Ty}
       → Γ ⊢ *ⁿ 𝐭 ∷ (A ⊃ B)    → Γ ⊢ *ⁿ 𝐬 ∷ A
       → Γ ⊢ 𝐭 ∘ⁿ 𝐬 ∷ B

  M𝑝ⁿ  : ∀{n} {𝐭 𝐬 : Tms n} {A B : Ty}
       → Γ ⊢ *ⁿ 𝐭 ∷ A          → Γ ⊢ *ⁿ 𝐬 ∷ B
       → Γ ⊢ 𝑝ⁿ⟨ 𝐭 , 𝐬 ⟩∷ (A ∧ B)

  M𝜋₀ⁿ : ∀{n} {𝐭 : Tms n} {A B : Ty}
       → Γ ⊢ *ⁿ 𝐭 ∷ (A ∧ B)
       → Γ ⊢ 𝜋₀ⁿ 𝐭 ∷ A

  M𝜋₁ⁿ : ∀{n} {𝐭 : Tms n} {A B : Ty}
       → Γ ⊢ *ⁿ 𝐭 ∷ (A ∧ B)
       → Γ ⊢ 𝜋₁ⁿ 𝐭 ∷ B

  M⇑ⁿ  : ∀{n} {𝐭 : Tms n} {u : Tm} {A : Ty}
       → Γ ⊢ *ⁿ 𝐭 ∷ (u ∶ A)
       → Γ ⊢ ⇑ⁿ 𝐭 ∷ (! u ∶ u ∶ A)

  M⇓ⁿ  : ∀{n} {𝐭 : Tms n} {u : Tm} {A : Ty}
       → Γ ⊢ *ⁿ 𝐭 ∷ (u ∶ A)
       → Γ ⊢ ⇓ⁿ 𝐭 ∷ A


⊩_  : Ty → Set
⊩ A = ∀{m} {Γ : Cx m} → Γ ⊢ A


-- --------------------------------------------------------------------------
--
-- Simplified notation for level 1 typing rules


M𝜆  : ∀{A B m} {Γ : Cx m}
    → Γ , A ⊢ B
    → Γ ⊢ A ⊃ B
M𝜆 = M𝜆ⁿ {𝐱 = []} {𝐭 = []}

M∘  : ∀{A B m} {Γ : Cx m}
    → Γ ⊢ A ⊃ B    → Γ ⊢ A
    → Γ ⊢ B
M∘ = M∘ⁿ {𝐭 = []} {𝐬 = []}

M𝑝  : ∀{A B m} {Γ : Cx m}
    → Γ ⊢ A        → Γ ⊢ B
    → Γ ⊢ A ∧ B
M𝑝 = M𝑝ⁿ {𝐭 = []} {𝐬 = []}

M𝜋₀ : ∀{A B m} {Γ : Cx m}
    → Γ ⊢ A ∧ B
    → Γ ⊢ A
M𝜋₀ = M𝜋₀ⁿ {𝐭 = []}

M𝜋₁ : ∀{A B m} {Γ : Cx m}
    → Γ ⊢ A ∧ B
    → Γ ⊢ B
M𝜋₁ = M𝜋₁ⁿ {𝐭 = []}

M⇑  : ∀{u A m} {Γ : Cx m}
    → Γ ⊢ u ∶ A
    → Γ ⊢ ! u ∶ u ∶ A
M⇑ = M⇑ⁿ {𝐭 = []}

M⇓  : ∀{u A m} {Γ : Cx m}
    → Γ ⊢ u ∶ A
    → Γ ⊢ A
M⇓ = M⇓ⁿ {𝐭 = []}


-- --------------------------------------------------------------------------
--
-- Simplified notation for level 2 typing rules


M𝜆²  : ∀{x t A B m} {Γ : Cx m}
     → Γ , 𝑣 x ∶ A ⊢ t ∶ B
     → Γ ⊢ 𝜆 x · t ∶ (A ⊃ B)
M𝜆² {x} {t} = M𝜆ⁿ {𝐱 = x ∷ []} {𝐭 = t ∷ []}

M∘²  : ∀{t s A B m} {Γ : Cx m}
     → Γ ⊢ t ∶ (A ⊃ B)    → Γ ⊢ s ∶ A
     → Γ ⊢ t ∘ s ∶ B
M∘² {t} {s} = M∘ⁿ {𝐭 = t ∷ []} {𝐬 = s ∷ []}

M𝑝²  : ∀{t s A B m} {Γ : Cx m}
     → Γ ⊢ t ∶ A          → Γ ⊢ s ∶ B
     → Γ ⊢ 𝑝⟨ t , s ⟩ ∶ (A ∧ B)
M𝑝² {t} {s} = M𝑝ⁿ {𝐭 = t ∷ []} {𝐬 = s ∷ []}

M𝜋₀² : ∀{t A B m} {Γ : Cx m}
     → Γ ⊢ t ∶ (A ∧ B)
     → Γ ⊢ 𝜋₀ t ∶ A
M𝜋₀² {t} = M𝜋₀ⁿ {𝐭 = t ∷ []}

M𝜋₁² : ∀{t A B m} {Γ : Cx m}
     → Γ ⊢ t ∶ (A ∧ B)
     → Γ ⊢ 𝜋₁ t ∶ B
M𝜋₁² {t} = M𝜋₁ⁿ {𝐭 = t ∷ []}

M⇑²  : ∀{t u A m} {Γ : Cx m}
     → Γ ⊢ t ∶ u ∶ A
     → Γ ⊢ ⇑ t ∶ ! u ∶ u ∶ A
M⇑² {t} = M⇑ⁿ {𝐭 = t ∷ []}

M⇓²  : ∀{t u A m} {Γ : Cx m}
     → Γ ⊢ t ∶ u ∶ A
     → Γ ⊢ ⇓ t ∶ A
M⇓² {t} = M⇓ⁿ {𝐭 = t ∷ []}


-- --------------------------------------------------------------------------
--
-- Simplified notation for level 3 typing rules


M𝜆³  : ∀{x₂ x₁ t₂ t₁ A B m} {Γ : Cx m}
     → Γ , 𝑣 x₂ ∶ 𝑣 x₁ ∶ A ⊢ t₂ ∶ t₁ ∶ B
     → Γ ⊢ 𝜆² x₂ · t₂ ∶ 𝜆 x₁ · t₁ ∶ (A ⊃ B)
M𝜆³ {x₂} {x₁} {t₂} {t₁} = M𝜆ⁿ {𝐱 = x₂ ∷ x₁ ∷ []} {𝐭 = t₂ ∷ t₁ ∷ []}

M∘³  : ∀{t₂ t₁ s₂ s₁ A B m} {Γ : Cx m}
     → Γ ⊢ t₂ ∶ t₁ ∶ (A ⊃ B)    → Γ ⊢ s₂ ∶ s₁ ∶ A
     → Γ ⊢ t₂ ∘² s₂ ∶ t₁ ∘ s₁ ∶ B
M∘³ {t₂} {t₁} {s₂} {s₁} = M∘ⁿ {𝐭 = t₂ ∷ t₁ ∷ []} {𝐬 = s₂ ∷ s₁ ∷ []}

M𝑝³  : ∀{t₂ t₁ s₂ s₁ A B m} {Γ : Cx m}
     → Γ ⊢ t₂ ∶ t₁ ∶ A          → Γ ⊢ s₂ ∶ s₁ ∶ B
     → Γ ⊢ 𝑝²⟨ t₂ , s₂ ⟩ ∶ 𝑝⟨ t₁ , s₁ ⟩ ∶ (A ∧ B)
M𝑝³ {t₂} {t₁} {s₂} {s₁} = M𝑝ⁿ {𝐭 = t₂ ∷ t₁ ∷ []} {𝐬 = s₂ ∷ s₁ ∷ []}

M𝜋₀³ : ∀{t₂ t₁ A B m} {Γ : Cx m}
     → Γ ⊢ t₂ ∶ t₁ ∶ (A ∧ B)
     → Γ ⊢ 𝜋₀² t₂ ∶ 𝜋₀ t₁ ∶ A
M𝜋₀³ {t₂} {t₁} = M𝜋₀ⁿ {𝐭 = t₂ ∷ t₁ ∷ []}

M𝜋₁³ : ∀{t₂ t₁ A B m} {Γ : Cx m}
     → Γ ⊢ t₂ ∶ t₁ ∶ (A ∧ B)
     → Γ ⊢ 𝜋₁² t₂ ∶ 𝜋₁ t₁ ∶ B
M𝜋₁³ {t₂} {t₁} = M𝜋₁ⁿ {𝐭 = t₂ ∷ t₁ ∷ []}

M⇑³  : ∀{t₂ t₁ u A m} {Γ : Cx m}
     → Γ ⊢ t₂ ∶ t₁ ∶ u ∶ A
     → Γ ⊢ ⇑² t₂ ∶ ⇑ t₁ ∶ ! u ∶ u ∶ A
M⇑³ {t₂} {t₁} = M⇑ⁿ {𝐭 = t₂ ∷ t₁ ∷ []}

M⇓³  : ∀{t₂ t₁ u A m} {Γ : Cx m}
     → Γ ⊢ t₂ ∶ t₁ ∶ u ∶ A
     → Γ ⊢ ⇓² t₂ ∶ ⇓ t₁ ∶ A
M⇓³ {t₂} {t₁} = M⇓ⁿ {𝐭 = t₂ ∷ t₁ ∷ []}


-- --------------------------------------------------------------------------
--
-- Example terms for level 0, 1, and 2 IKS combinators


-- S4: A ⊃ A
eI : ∀{A}
   → ⊩ A ⊃ A
eI = M𝜆 (M𝑣 Z)

-- S4: □(A ⊃ A)
eI² : ∀{A x}
    → ⊩ 𝜆 x · 𝑣 x
        ∶ (A ⊃ A)
eI² = M𝜆² (M𝑣 Z)

-- S4: □□(A ⊃ A)
eI³ : ∀{A x u}
    → ⊩ 𝜆² u · 𝑣 u
        ∶ 𝜆 x · 𝑣 x
          ∶ (A ⊃ A)
eI³ = M𝜆³ (M𝑣 Z)


-- S4: A ⊃ B ⊃ A
eK : ∀{A B}
   → ⊩ A ⊃ B ⊃ A
eK = M𝜆 (M𝜆 (M𝑣 (S Z)))

-- S4: □(A ⊃ B ⊃ A)
eK² : ∀{A B x y}
    → ⊩ 𝜆 x · 𝜆 y · 𝑣 x
        ∶ (A ⊃ B ⊃ A)
eK² = M𝜆² (M𝜆² (M𝑣 (S Z)))

-- S4: □□(A ⊃ B ⊃ A)
eK³ : ∀{A B x y u v}
    → ⊩ 𝜆² u · 𝜆² v · 𝑣 u
        ∶ 𝜆 x · 𝜆 y · 𝑣 x
          ∶ (A ⊃ B ⊃ A)
eK³ = M𝜆³ (M𝜆³ (M𝑣 (S Z)))


-- S4: (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
eS : ∀{A B C}
   → ⊩ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
eS = M𝜆 (M𝜆 (M𝜆 (M∘ (M∘ (M𝑣 (S S Z))
                            (M𝑣 Z))
                    (M∘ (M𝑣 (S Z))
                            (M𝑣 Z)))))

-- S4: □((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
eS² : ∀{A B C f g x}
    → ⊩ 𝜆 f · 𝜆 g · 𝜆 x · (𝑣 f ∘ 𝑣 x) ∘ (𝑣 g ∘ 𝑣 x)
        ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
eS² = M𝜆² (M𝜆² (M𝜆² (M∘² (M∘² (M𝑣 (S S Z))
                              (M𝑣 Z))
                         (M∘² (M𝑣 (S Z))
                              (M𝑣 Z)))))

-- S4: □□((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
eS³ : ∀{A B C f g x p q u}
    → ⊩ 𝜆² p · 𝜆² q · 𝜆² u · (𝑣 p ∘² 𝑣 u) ∘² (𝑣 q ∘² 𝑣 u)
        ∶ 𝜆 f · 𝜆 g · 𝜆 x · (𝑣 f ∘ 𝑣 x) ∘ (𝑣 g ∘ 𝑣 x)
          ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
eS³ = M𝜆³ (M𝜆³ (M𝜆³ (M∘³ (M∘³ (M𝑣 (S S Z))
                              (M𝑣 Z))
                         (M∘³ (M𝑣 (S Z))
                              (M𝑣 Z)))))


-- --------------------------------------------------------------------------
--
-- Example terms for S4 axioms


-- S4: □(A ⊃ B) ⊃ □A ⊃ □B
axK : ∀{A B f x}
    → ⊩ (f ∶ (A ⊃ B)) ⊃ x ∶ A ⊃ (f ∘ x) ∶ B
axK = M𝜆 (M𝜆 (M∘² (M𝑣 (S Z))
                  (M𝑣 Z)))

-- S4: □(□(A ⊃ B) ⊃ □A ⊃ □B)
axK² : ∀{A B f x p u}
     → ⊩ 𝜆 p · 𝜆 u · 𝑣 p ∘² 𝑣 u
         ∶ (f ∶ (A ⊃ B) ⊃ x ∶ A ⊃ (f ∘ x) ∶ B)
axK² = M𝜆² (M𝜆² (M∘³ (M𝑣 (S Z))
                     (M𝑣 Z)))

-- S4: □A ⊃ A
axT : ∀{A x}
    → ⊩ x ∶ A ⊃ A
axT = M𝜆 (M⇓ (M𝑣 Z))

-- S4: □A ⊃ □□A
ax4 : ∀{A x}
     → ⊩ x ∶ A ⊃ ! x ∶ x ∶ A
ax4 = M𝜆 (M⇑ (M𝑣 Z))


-- --------------------------------------------------------------------------
--
-- Terms for example 1, p. 28 [1]


-- S4: □(□A ⊃ A)
e11 : ∀{A x y}
    → ⊩ 𝜆 y · ⇓ 𝑣 y
        ∶ (x ∶ A ⊃ A)
e11 = M𝜆² (M⇓² (M𝑣 Z))

-- S4: □(□A ⊃ □□A)
e12 : ∀{A x y}
    → ⊩ 𝜆 y · ⇑ 𝑣 y
        ∶ (x ∶ A ⊃ ! x ∶ x ∶ A)
e12 = M𝜆² (M⇑² (M𝑣 Z))

-- S4: □□(A ⊃ B ⊃ A ∧ B)
e13 : ∀{A B x y u v}
    → ⊩ 𝜆² u · 𝜆² v · 𝑝²⟨ 𝑣 u , 𝑣 v ⟩
        ∶ 𝜆 x · 𝜆 y · 𝑝⟨ 𝑣 x , 𝑣 y ⟩
          ∶ (A ⊃ B ⊃ A ∧ B)
e13 = M𝜆³ (M𝜆³ (M𝑝³ (M𝑣 (S Z))
                    (M𝑣 Z)))

-- S4: □(□A ⊃ □B ⊃ □□(A ∧ B))
e14 : ∀{A B x y u v}
    → ⊩ 𝜆 u · 𝜆 v · ⇑ 𝑝²⟨ 𝑣 u , 𝑣 v ⟩
        ∶ (x ∶ A ⊃ y ∶ B ⊃ ! 𝑝⟨ x , y ⟩ ∶ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
e14 = M𝜆² (M𝜆² (M⇑² (M𝑝³ (M𝑣 (S Z))
                         (M𝑣 Z))))


-- --------------------------------------------------------------------------
--
-- Additional example terms


-- S4: □(□A ⊃ □B ⊃ □(A ∧ B))
ex1 : ∀{A B x y u v}
    → ⊩ 𝜆 u · 𝜆 v · 𝑝²⟨ 𝑣 u , 𝑣 v ⟩
        ∶ (x ∶ A ⊃ y ∶ B ⊃ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
ex1 = M𝜆² (M𝜆² (M𝑝³ (M𝑣 (S Z))
                    (M𝑣 Z)))

-- S4: □(□A ∧ □B ⊃ □□(A ∧ B))
ex2 : ∀{A B x y u}
    → ⊩ 𝜆 u · ⇑ 𝑝²⟨ 𝜋₀ 𝑣 u , 𝜋₁ 𝑣 u ⟩
        ∶ (x ∶ A ∧ y ∶ B ⊃ ! 𝑝⟨ x , y ⟩ ∶ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
ex2 = M𝜆² (M⇑² (M𝑝³ (M𝜋₀² (M𝑣 Z))
                    (M𝜋₁² (M𝑣 Z))))

-- S4: □(□A ∧ □B ⊃ □(A ∧ B))
ex3 : ∀{A B x y u}
    → ⊩ 𝜆 u · 𝑝²⟨ 𝜋₀ 𝑣 u , 𝜋₁ 𝑣 u ⟩
        ∶ (x ∶ A ∧ y ∶ B ⊃ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
ex3 = M𝜆² (M𝑝³ (M𝜋₀² (M𝑣 Z))
               (M𝜋₁² (M𝑣 Z)))


-- --------------------------------------------------------------------------
--
-- Terms for example 2, pp. 31–32 [1]


e2 : ∀{A x₃ x₂ x₁}
   → ⊩ 𝜆² x₃ · ⇓² ⇑² 𝑣 x₃
       ∶ 𝜆 x₂ · ⇓ ⇑ 𝑣 x₂
         ∶ (x₁ ∶ A ⊃ x₁ ∶ A)
e2 = M𝜆³ (M⇓³ (M⇑³ (M𝑣 Z)))

e2′ : ∀{A x₃ x₂ x₁}
    → ⊩ 𝜆² x₃ · 𝑣 x₃
        ∶ 𝜆 x₂ · 𝑣 x₂
          ∶ (x₁ ∶ A ⊃ x₁ ∶ A)
e2′ = M𝜆³ (M𝑣 Z)


-- --------------------------------------------------------------------------
--
-- Weakening


data _≲_ : ∀{m m′} → Cx m → Cx m′ → Set where
  base : ∅ ≲ ∅

  drop : ∀{A m m′} {Γ : Cx m} {Γ′ : Cx m′}
       → Γ ≲ Γ′
       → Γ ≲ (Γ′ , A)

  keep : ∀{A m m′} {Γ : Cx m} {Γ′ : Cx m′}
       → Γ ≲ Γ′
       → (Γ , A) ≲ (Γ′ , A)


∅≲Γ : ∀{m} {Γ : Cx m} → ∅ ≲ Γ
∅≲Γ {Γ = ∅}     = base
∅≲Γ {Γ = Γ , A} = drop ∅≲Γ


Γ≲Γ : ∀{m} {Γ : Cx m} → Γ ≲ Γ
Γ≲Γ {Γ = ∅}     = base
Γ≲Γ {Γ = Γ , A} = keep Γ≲Γ


wk∈ : ∀{A m m′} {Γ : Cx m} {Γ′ : Cx m′}
    → Γ ≲ Γ′    → A ∈ Γ
    → A ∈ Γ′
wk∈ base     ()
wk∈ (keep P) Z     = Z
wk∈ (keep P) (S i) = S (wk∈ P i)
wk∈ (drop P) i     = S (wk∈ P i)


wk⊢ : ∀{A m m′} {Γ : Cx m} {Γ′ : Cx m′}
    → Γ ≲ Γ′    → Γ ⊢ A
    → Γ′ ⊢ A
wk⊢ P (M𝑣 i)                   = M𝑣 (wk∈ P i)
wk⊢ P (M𝜆ⁿ  {𝐱 = 𝐱} {𝐭} D)     = M𝜆ⁿ  {𝐱 = 𝐱} {𝐭} (wk⊢ (keep P) D)
wk⊢ P (M∘ⁿ  {𝐭 = 𝐭} {𝐬} Dₜ Dₛ) = M∘ⁿ  {𝐭 = 𝐭} {𝐬} (wk⊢ P Dₜ) (wk⊢ P Dₛ)
wk⊢ P (M𝑝ⁿ  {𝐭 = 𝐭} {𝐬} Dₜ Dₛ) = M𝑝ⁿ  {𝐭 = 𝐭} {𝐬} (wk⊢ P Dₜ) (wk⊢ P Dₛ)
wk⊢ P (M𝜋₀ⁿ {𝐭 = 𝐭} D)         = M𝜋₀ⁿ {𝐭 = 𝐭} (wk⊢ P D)
wk⊢ P (M𝜋₁ⁿ {𝐭 = 𝐭} D)         = M𝜋₁ⁿ {𝐭 = 𝐭} (wk⊢ P D)
wk⊢ P (M⇑ⁿ  {𝐭 = 𝐭} D)         = M⇑ⁿ  {𝐭 = 𝐭} (wk⊢ P D)
wk⊢ P (M⇓ⁿ  {𝐭 = 𝐭} D)         = M⇓ⁿ  {𝐭 = 𝐭} (wk⊢ P D)


-- --------------------------------------------------------------------------
--
-- Contraction


data _≳_ : ∀{m m′} → Cx m → Cx m′ → Set where
  base : ∅ ≳ ∅

  once : ∀{A m m′} {Γ : Cx m} {Γ′ : Cx m′}
       → Γ ≳ Γ′
       → (Γ , A) ≳ (Γ′ , A)

  more : ∀{A m m′} {Γ : Cx m} {Γ′ : Cx m′}
       → Γ ≳ Γ′
       → (Γ , A , A) ≳ (Γ′ , A)


cn∈ : ∀{A m m′} {Γ : Cx m} {Γ′ : Cx m′}
    → Γ ≳ Γ′    → A ∈ Γ
    → A ∈ Γ′
cn∈ base     ()
cn∈ (once P) Z     = Z
cn∈ (once P) (S i) = S (cn∈ P i)
cn∈ (more P) Z     = Z
cn∈ (more P) (S i) = cn∈ (once P) i


cn⊢ : ∀{A m m′} {Γ : Cx m} {Γ′ : Cx m′}
    → Γ ≳ Γ′    → Γ ⊢ A
    → Γ′ ⊢ A
cn⊢ P (M𝑣 i)                   = M𝑣 (cn∈ P i)
cn⊢ P (M𝜆ⁿ  {𝐱 = 𝐱} {𝐭} D)     = M𝜆ⁿ  {𝐱 = 𝐱} {𝐭} (cn⊢ (once P) D)
cn⊢ P (M∘ⁿ  {𝐭 = 𝐭} {𝐬} Dₜ Dₛ) = M∘ⁿ  {𝐭 = 𝐭} {𝐬} (cn⊢ P Dₜ) (cn⊢ P Dₛ)
cn⊢ P (M𝑝ⁿ  {𝐭 = 𝐭} {𝐬} Dₜ Dₛ) = M𝑝ⁿ  {𝐭 = 𝐭} {𝐬} (cn⊢ P Dₜ) (cn⊢ P Dₛ)
cn⊢ P (M𝜋₀ⁿ {𝐭 = 𝐭} D)         = M𝜋₀ⁿ {𝐭 = 𝐭} (cn⊢ P D)
cn⊢ P (M𝜋₁ⁿ {𝐭 = 𝐭} D)         = M𝜋₁ⁿ {𝐭 = 𝐭} (cn⊢ P D)
cn⊢ P (M⇑ⁿ  {𝐭 = 𝐭} D)         = M⇑ⁿ  {𝐭 = 𝐭} (cn⊢ P D)
cn⊢ P (M⇓ⁿ  {𝐭 = 𝐭} D)         = M⇓ⁿ  {𝐭 = 𝐭} (cn⊢ P D)


-- --------------------------------------------------------------------------
--
-- Exchange


data _≈_ : ∀{m} → Cx m → Cx m → Set where
  base : ∅ ≈ ∅

  just : ∀{A m} {Γ Γ′ : Cx m}
       → Γ ≈ Γ′
       → (Γ , A) ≈ (Γ′ , A)

  same : ∀{A B m} {Γ Γ′ : Cx m}
       → Γ ≈ Γ′
       → (Γ , A , B) ≈ (Γ′ , A , B)

  diff : ∀{A B m} {Γ Γ′ : Cx m}
       → Γ ≈ Γ′
       → (Γ , B , A) ≈ (Γ′ , A , B)


ex∈ : ∀{A m} {Γ Γ′ : Cx m}
    → Γ ≈ Γ′    → A ∈ Γ
    → A ∈ Γ′
ex∈ base     ()
ex∈ (just P) Z         = Z
ex∈ (just P) (S i)     = S (ex∈ P i)
ex∈ (same P) Z         = Z
ex∈ (same P) (S Z)     = S Z
ex∈ (same P) (S (S i)) = S (S (ex∈ P i))
ex∈ (diff P) Z         = S Z
ex∈ (diff P) (S Z)     = Z
ex∈ (diff P) (S (S i)) = S (S (ex∈ P i))


ex⊢ : ∀{A m} {Γ Γ′ : Cx m}
    → Γ ≈ Γ′    → Γ ⊢ A
    → Γ′ ⊢ A
ex⊢ P (M𝑣 i)                   = M𝑣 (ex∈ P i)
ex⊢ P (M𝜆ⁿ  {𝐱 = 𝐱} {𝐭} D)     = M𝜆ⁿ  {𝐱 = 𝐱} {𝐭} (ex⊢ (just P) D)
ex⊢ P (M∘ⁿ  {𝐭 = 𝐭} {𝐬} Dₜ Dₛ) = M∘ⁿ  {𝐭 = 𝐭} {𝐬} (ex⊢ P Dₜ) (ex⊢ P Dₛ)
ex⊢ P (M𝑝ⁿ  {𝐭 = 𝐭} {𝐬} Dₜ Dₛ) = M𝑝ⁿ  {𝐭 = 𝐭} {𝐬} (ex⊢ P Dₜ) (ex⊢ P Dₛ)
ex⊢ P (M𝜋₀ⁿ {𝐭 = 𝐭} D)         = M𝜋₀ⁿ {𝐭 = 𝐭} (ex⊢ P D)
ex⊢ P (M𝜋₁ⁿ {𝐭 = 𝐭} D)         = M𝜋₁ⁿ {𝐭 = 𝐭} (ex⊢ P D)
ex⊢ P (M⇑ⁿ  {𝐭 = 𝐭} D)         = M⇑ⁿ  {𝐭 = 𝐭} (ex⊢ P D)
ex⊢ P (M⇓ⁿ  {𝐭 = 𝐭} D)         = M⇓ⁿ  {𝐭 = 𝐭} (ex⊢ P D)


-- --------------------------------------------------------------------------
--
-- Theorem 1 (Internalisation principle), p. 29 [1]


prefix : ∀{m} → Vars m → Cx m → Cx m
prefix []      ∅       = ∅
prefix (x ∷ 𝐱) (Γ , A) = prefix 𝐱 Γ , 𝑣 x ∶ A


postulate fresh : Var    -- XXX: Fix this!


in∈ : ∀{A m} {𝐱 : Vars m} {Γ : Cx m}
    → A ∈ Γ
    → Σ Var (λ x → (𝑣 x ∶ A) ∈ prefix 𝐱 Γ)
in∈ {𝐱 = []}    ()
in∈ {𝐱 = x ∷ _} Z     = ⟨ x , Z ⟩
in∈ {𝐱 = _ ∷ 𝐱} (S i) = let ⟨ y , j ⟩ = in∈ {𝐱 = 𝐱} i
                        in
                          ⟨ y , S j ⟩


in⊢ : ∀{A m} {𝐱 : Vars m} {Γ : Cx m}
    → Γ ⊢ A
    → Σ (Vars m → Tm) (λ t → prefix 𝐱 Γ ⊢ t 𝐱 ∶ A)

in⊢ {𝐱 = 𝐱} (M𝑣 {A = A} i)
    = let ⟨ x , j ⟩ = in∈ {𝐱 = 𝐱} i
      in
        ⟨ (λ _ → 𝑣 x)
        , M𝑣 {A = 𝑣 x ∶ A} j
        ⟩

in⊢ {𝐱 = 𝐱} (M𝜆ⁿ {n} {𝐱 = 𝐲} {𝐭} D)
    = let xₘ₊₁      = fresh
          ⟨ s , C ⟩ = in⊢ {𝐱 = xₘ₊₁ ∷ 𝐱} D
      in
        ⟨ (λ 𝐱 → 𝜆[ suc n ] xₘ₊₁ · s (xₘ₊₁ ∷ 𝐱))
        , M𝜆ⁿ {𝐱 = xₘ₊₁ ∷ 𝐲} {𝐭 = s (xₘ₊₁ ∷ 𝐱) ∷ 𝐭} C
        ⟩

in⊢ {𝐱 = 𝐱} (M∘ⁿ {n} {𝐭} {𝐬} Dₜ Dₛ)
    = let ⟨ sₜ , Cₜ ⟩ = in⊢ {𝐱 = 𝐱} Dₜ
          ⟨ sₛ , Cₛ ⟩ = in⊢ {𝐱 = 𝐱} Dₛ
      in
        ⟨ (λ 𝐱 → sₜ 𝐱 ∘[ suc n ] sₛ 𝐱)
        , M∘ⁿ {𝐭 = sₜ 𝐱 ∷ 𝐭} {𝐬 = sₛ 𝐱 ∷ 𝐬} Cₜ Cₛ
        ⟩

in⊢ {𝐱 = 𝐱} (M𝑝ⁿ {n} {𝐭} {𝐬} Dₜ Dₛ)
    = let ⟨ sₜ , Cₜ ⟩ = in⊢ {𝐱 = 𝐱} Dₜ
          ⟨ sₛ , Cₛ ⟩ = in⊢ {𝐱 = 𝐱} Dₛ
      in
        ⟨ (λ 𝐱 → 𝑝[ suc n ]⟨ sₜ 𝐱 , sₛ 𝐱 ⟩)
        , M𝑝ⁿ {𝐭 = sₜ 𝐱 ∷ 𝐭} {𝐬 = sₛ 𝐱 ∷ 𝐬} Cₜ Cₛ
        ⟩

in⊢ {𝐱 = 𝐱} (M𝜋₀ⁿ {n} {𝐭} D)
    = let ⟨ s , C ⟩ = in⊢ {𝐱 = 𝐱} D
      in
        ⟨ (λ 𝐱 → 𝜋₀[ suc n ] s 𝐱)
        , M𝜋₀ⁿ {𝐭 = s 𝐱 ∷ 𝐭} C
        ⟩

in⊢ {𝐱 = 𝐱} (M𝜋₁ⁿ {n} {𝐭} D)
    = let ⟨ s , C ⟩ = in⊢ {𝐱 = 𝐱} D
      in
        ⟨ (λ 𝐱 → 𝜋₁[ suc n ] s 𝐱)
        , M𝜋₁ⁿ {𝐭 = s 𝐱 ∷ 𝐭} C
        ⟩

in⊢ {𝐱 = 𝐱} (M⇑ⁿ {n} {𝐭} D)
    = let ⟨ s , C ⟩ = in⊢ {𝐱 = 𝐱} D
      in
        ⟨ (λ 𝐱 → ⇑[ suc n ] s 𝐱)
        , M⇑ⁿ {𝐭 = s 𝐱 ∷ 𝐭} C
        ⟩

in⊢ {𝐱 = 𝐱} (M⇓ⁿ {n} {𝐭} D)
    = let ⟨ s , C ⟩ = in⊢ {𝐱 = 𝐱} D
      in
        ⟨ (λ 𝐱 → ⇓[ suc n ] s 𝐱)
        , M⇓ⁿ {𝐭 = s 𝐱 ∷ 𝐭} C
        ⟩


-- --------------------------------------------------------------------------
--
-- Constructive necessitation


nec : ∀{A}
    → ∅ ⊢ A
    → Σ Tm (λ t → ⊩ t ∶ A)
nec D = let ⟨ s , C ⟩ = in⊢ D
        in
          ⟨ s [] , wk⊢ ∅≲Γ C ⟩


eI²′ : ∀{A}
     → Σ Tm (λ t → ⊩ t ∶ (A ⊃ A))
eI²′ = nec eI

eI³′ : ∀{x A}
     → Σ Tm (λ t → ⊩ t ∶ 𝜆 x · 𝑣 x ∶ (A ⊃ A))
eI³′ = nec eI²

eI⁴′ : ∀{u x A}
     → Σ Tm (λ t → ⊩ t ∶ 𝜆² u · 𝑣 u ∶ 𝜆 x · 𝑣 x ∶ (A ⊃ A))
eI⁴′ = nec eI³


eI³″ : ∀{A}
     → Σ Tm (λ t → ⊩ t ∶ 𝜆 fresh · 𝑣 fresh ∶ (A ⊃ A))    -- XXX: Fix this!
eI³″ = nec (proj₂ (eI²′))

eI⁴″ : ∀{A}
     → Σ Tm (λ t → ⊩ t ∶ 𝜆² fresh · 𝑣 fresh ∶ 𝜆 fresh · 𝑣 fresh ∶ (A ⊃ A))    -- XXX: Fix this!
eI⁴″ = nec (proj₂ (eI³′))
