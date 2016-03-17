{-

An implementation of the Alt-Artëmov system λ∞
==============================================

Miëtek Bak  <mietek@bak.io>


Work in progress.  Checked with Agda 2.4.2.5.

For easy editing with Emacs agda-mode, add to your .emacs file:

'(agda-input-user-translations
   (quote
    (("i" "⊃") ("ii" "⫗") ("e" "⊢") ("ee" "⊩") ("n" "¬")
     ("s" "𝐬") ("t" "𝐭") ("x" "𝐱") ("y" "𝐲")
     ("N" "ℕ") ("*n" "*ⁿ")
     ("v" "𝑣") ("v2" "𝑣²") ("v3" "𝑣³") ("vn" "𝑣ⁿ")
     ("l" "𝜆") ("l2" "𝜆²") ("l3" "𝜆³") ("ln" "𝜆ⁿ")
     ("o" "∘") ("o2" "∘²") ("o3" "∘³") ("on" "∘ⁿ")
     ("p" "𝑝") ("p2" "𝑝²") ("p3" "𝑝³") ("pn" "𝑝ⁿ")
     ("1" "𝜋₀") ("12" "𝜋₀²") ("13" "𝜋₀³") ("1n" "𝜋₀ⁿ")
     ("2" "𝜋₁") ("22" "𝜋₁²") ("23" "𝜋₁³") ("2n" "𝜋₁ⁿ")
     ("u" "⇑") ("u2" "⇑²") ("u3" "⇑³") ("un" "⇑ⁿ")
     ("d" "⇓") ("d2" "⇓²") ("d3" "⇓³") ("dn" "⇓ⁿ"))))


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
  using (Σ ; proj₁ ; proj₂ ; _×_)
  renaming (_,_ to ⟨_,_⟩)

infixl 9 !_ 𝑣_ M𝑣_
infixl 8 𝜋₀_ 𝜋₀²_ M𝜋₀_ M𝜋₀²_ M𝜋₀³_
infixl 8 𝜋₁_ 𝜋₁²_ M𝜋₁_ M𝜋₁²_ M𝜋₁³_
infixl 7 _∘_ _∘²_ _M∘_ _M∘²_ _M∘³_
infixr 6 ⇑_ ⇑²_ M⇑_ M⇑²_ M⇑³_
infixr 6 ⇓_ ⇓²_ M⇓_ M⇓²_ M⇓³_
infixr 5 𝜆_ 𝜆²_ M𝜆_ M𝜆²_ M𝜆³_
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
    -- Variable index
    𝑣_ : Var → Tm

    -- Abstraction (⊃I)
    𝜆[_]_ : ℕ → Tm → Tm

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


𝜆_ : Tm → Tm
𝜆 t = 𝜆[ 1 ] t

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


𝜆²_ : Tm → Tm
𝜆² t₂ = 𝜆[ 2 ] t₂

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


replicate : {X : Set}
          → (n : ℕ) → X → Vec X n
replicate zero    x = []
replicate (suc n) x = x ∷ replicate n x

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
*ⁿ []      ∷ A = A
*ⁿ (x ∷ 𝐭) ∷ A = x ∶ *ⁿ 𝐭 ∷ A

𝑣[_]_∷_ : ℕ → Var → Ty → Ty
𝑣[ n ] x ∷ A = *ⁿ (replicate n (𝑣 x)) ∷ A

𝜆ⁿ_∷_ : ∀{n} → Tms n → Ty → Ty
𝜆ⁿ 𝐭 ∷ A = *ⁿ (ixMap 𝜆[_]_ 𝐭) ∷ A

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


Hyp : Set
Hyp = ℕ × Ty


data Cx : ℕ → Set where
  ∅   : Cx zero
  _,_ : ∀{m} → Cx m → Hyp → Cx (suc m)


data _∈[_]_ : ∀{m} → Hyp → ℕ → Cx m → Set where
  Z  : ∀{m} {Γ : Cx m} {A : Hyp}
     → A ∈[ zero ] (Γ , A)

  S_ : ∀{m x} {Γ : Cx m} {A B : Hyp}
     → A ∈[ x ] Γ
     → A ∈[ suc x ] (Γ , B)


-- --------------------------------------------------------------------------
--
-- Typing judgment


data _⊢_ {m : ℕ} (Γ : Cx m) : Ty → Set where
  M𝑣_ : ∀{n x} {A : Ty}
      → ⟨ n , A ⟩ ∈[ x ] Γ
      → Γ ⊢ 𝑣[ n ] x ∷ A

  M𝜆ⁿ_ : ∀{n} {𝐭 : Tms n} {A B : Ty}
      → Γ , ⟨ n , A ⟩ ⊢ *ⁿ 𝐭 ∷ B
      → Γ ⊢ 𝜆ⁿ 𝐭 ∷ (A ⊃ B)

  _M∘ⁿ_ : ∀{n} {𝐭 𝐬 : Tms n} {A B : Ty}
      → Γ ⊢ *ⁿ 𝐭 ∷ (A ⊃ B)    → Γ ⊢ *ⁿ 𝐬 ∷ A
      → Γ ⊢ 𝐭 ∘ⁿ 𝐬 ∷ B

  M𝑝ⁿ⟨_,_⟩ : ∀{n} {𝐭 𝐬 : Tms n} {A B : Ty}
      → Γ ⊢ *ⁿ 𝐭 ∷ A          → Γ ⊢ *ⁿ 𝐬 ∷ B
      → Γ ⊢ 𝑝ⁿ⟨ 𝐭 , 𝐬 ⟩∷ (A ∧ B)

  M𝜋₀ⁿ_ : ∀{n} {𝐭 : Tms n} {A B : Ty}
      → Γ ⊢ *ⁿ 𝐭 ∷ (A ∧ B)
      → Γ ⊢ 𝜋₀ⁿ 𝐭 ∷ A

  M𝜋₁ⁿ_ : ∀{n} {𝐭 : Tms n} {A B : Ty}
      → Γ ⊢ *ⁿ 𝐭 ∷ (A ∧ B)
      → Γ ⊢ 𝜋₁ⁿ 𝐭 ∷ B

  M⇑ⁿ_ : ∀{n} {𝐭 : Tms n} {u : Tm} {A : Ty}
      → Γ ⊢ *ⁿ 𝐭 ∷ (u ∶ A)
      → Γ ⊢ ⇑ⁿ 𝐭 ∷ (! u ∶ u ∶ A)

  M⇓ⁿ_ : ∀{n} {𝐭 : Tms n} {u : Tm} {A : Ty}
      → Γ ⊢ *ⁿ 𝐭 ∷ (u ∶ A)
      → Γ ⊢ ⇓ⁿ 𝐭 ∷ A


⊩_  : Ty → Set
⊩ A = ∅ ⊢ A


-- --------------------------------------------------------------------------
--
-- Simplified notation for level 1 typing rules


M𝜆_ : ∀{A B m} {Γ : Cx m}
    → Γ , ⟨ 0 , A ⟩ ⊢ B
    → Γ ⊢ A ⊃ B
M𝜆_ = M𝜆ⁿ_ {𝐭 = []}

_M∘_ : ∀{A B m} {Γ : Cx m}
    → Γ ⊢ A ⊃ B    → Γ ⊢ A
    → Γ ⊢ B
_M∘_ = _M∘ⁿ_ {𝐭 = []} {𝐬 = []}

M𝑝⟨_,_⟩ : ∀{A B m} {Γ : Cx m}
    → Γ ⊢ A        → Γ ⊢ B
    → Γ ⊢ A ∧ B
M𝑝⟨_,_⟩ = M𝑝ⁿ⟨_,_⟩ {𝐭 = []} {𝐬 = []}

M𝜋₀_ : ∀{A B m} {Γ : Cx m}
    → Γ ⊢ A ∧ B
    → Γ ⊢ A
M𝜋₀_ = M𝜋₀ⁿ_ {𝐭 = []}

M𝜋₁_ : ∀{A B m} {Γ : Cx m}
    → Γ ⊢ A ∧ B
    → Γ ⊢ B
M𝜋₁_ = M𝜋₁ⁿ_ {𝐭 = []}

M⇑_ : ∀{u A m} {Γ : Cx m}
    → Γ ⊢ u ∶ A
    → Γ ⊢ ! u ∶ u ∶ A
M⇑_ = M⇑ⁿ_ {𝐭 = []}

M⇓_ : ∀{u A m} {Γ : Cx m}
    → Γ ⊢ u ∶ A
    → Γ ⊢ A
M⇓_ = M⇓ⁿ_ {𝐭 = []}


-- --------------------------------------------------------------------------
--
-- Simplified notation for level 2 typing rules


M𝜆²_ : ∀{t A B m} {Γ : Cx m}
    → Γ , ⟨ 1 , A ⟩ ⊢ t ∶ B
    → Γ ⊢ 𝜆 t ∶ (A ⊃ B)
M𝜆²_ {t} = M𝜆ⁿ_ {𝐭 = t ∷ []}

_M∘²_ : ∀{t s A B m} {Γ : Cx m}
    → Γ ⊢ t ∶ (A ⊃ B)    → Γ ⊢ s ∶ A
    → Γ ⊢ t ∘ s ∶ B
_M∘²_ {t} {s} = _M∘ⁿ_ {𝐭 = t ∷ []} {𝐬 = s ∷ []}

M𝑝²⟨_,_⟩ : ∀{t s A B m} {Γ : Cx m}
    → Γ ⊢ t ∶ A          → Γ ⊢ s ∶ B
    → Γ ⊢ 𝑝⟨ t , s ⟩ ∶ (A ∧ B)
M𝑝²⟨_,_⟩ {t} {s} = M𝑝ⁿ⟨_,_⟩ {𝐭 = t ∷ []} {𝐬 = s ∷ []}

M𝜋₀²_ : ∀{t A B m} {Γ : Cx m}
    → Γ ⊢ t ∶ (A ∧ B)
    → Γ ⊢ 𝜋₀ t ∶ A
M𝜋₀²_ {t} = M𝜋₀ⁿ_ {𝐭 = t ∷ []}

M𝜋₁²_ : ∀{t A B m} {Γ : Cx m}
    → Γ ⊢ t ∶ (A ∧ B)
    → Γ ⊢ 𝜋₁ t ∶ B
M𝜋₁²_ {t} = M𝜋₁ⁿ_ {𝐭 = t ∷ []}

M⇑²_ : ∀{t u A m} {Γ : Cx m}
    → Γ ⊢ t ∶ u ∶ A
    → Γ ⊢ ⇑ t ∶ ! u ∶ u ∶ A
M⇑²_ {t} = M⇑ⁿ_ {𝐭 = t ∷ []}

M⇓²_ : ∀{t u A m} {Γ : Cx m}
    → Γ ⊢ t ∶ u ∶ A
    → Γ ⊢ ⇓ t ∶ A
M⇓²_ {t} = M⇓ⁿ_ {𝐭 = t ∷ []}


-- --------------------------------------------------------------------------
--
-- Simplified notation for level 3 typing rules


M𝜆³_ : ∀{t₂ t₁ A B m} {Γ : Cx m}
    → Γ , ⟨ 2 , A ⟩ ⊢ t₂ ∶ t₁ ∶ B
    → Γ ⊢ 𝜆² t₂ ∶ 𝜆 t₁ ∶ (A ⊃ B)
M𝜆³_ {t₂} {t₁} = M𝜆ⁿ_ {𝐭 = t₂ ∷ t₁ ∷ []}

_M∘³_ : ∀{t₂ t₁ s₂ s₁ A B m} {Γ : Cx m}
    → Γ ⊢ t₂ ∶ t₁ ∶ (A ⊃ B)    → Γ ⊢ s₂ ∶ s₁ ∶ A
    → Γ ⊢ t₂ ∘² s₂ ∶ t₁ ∘ s₁ ∶ B
_M∘³_ {t₂} {t₁} {s₂} {s₁} = _M∘ⁿ_ {𝐭 = t₂ ∷ t₁ ∷ []} {𝐬 = s₂ ∷ s₁ ∷ []}

M𝑝³⟨_,_⟩ : ∀{t₂ t₁ s₂ s₁ A B m} {Γ : Cx m}
    → Γ ⊢ t₂ ∶ t₁ ∶ A          → Γ ⊢ s₂ ∶ s₁ ∶ B
    → Γ ⊢ 𝑝²⟨ t₂ , s₂ ⟩ ∶ 𝑝⟨ t₁ , s₁ ⟩ ∶ (A ∧ B)
M𝑝³⟨_,_⟩ {t₂} {t₁} {s₂} {s₁} = M𝑝ⁿ⟨_,_⟩ {𝐭 = t₂ ∷ t₁ ∷ []} {𝐬 = s₂ ∷ s₁ ∷ []}

M𝜋₀³_ : ∀{t₂ t₁ A B m} {Γ : Cx m}
    → Γ ⊢ t₂ ∶ t₁ ∶ (A ∧ B)
    → Γ ⊢ 𝜋₀² t₂ ∶ 𝜋₀ t₁ ∶ A
M𝜋₀³_ {t₂} {t₁} = M𝜋₀ⁿ_ {𝐭 = t₂ ∷ t₁ ∷ []}

M𝜋₁³_ : ∀{t₂ t₁ A B m} {Γ : Cx m}
    → Γ ⊢ t₂ ∶ t₁ ∶ (A ∧ B)
    → Γ ⊢ 𝜋₁² t₂ ∶ 𝜋₁ t₁ ∶ B
M𝜋₁³_ {t₂} {t₁} = M𝜋₁ⁿ_ {𝐭 = t₂ ∷ t₁ ∷ []}

M⇑³_ : ∀{t₂ t₁ u A m} {Γ : Cx m}
    → Γ ⊢ t₂ ∶ t₁ ∶ u ∶ A
    → Γ ⊢ ⇑² t₂ ∶ ⇑ t₁ ∶ ! u ∶ u ∶ A
M⇑³_ {t₂} {t₁} = M⇑ⁿ_ {𝐭 = t₂ ∷ t₁ ∷ []}

M⇓³_ : ∀{t₂ t₁ u A m} {Γ : Cx m}
    → Γ ⊢ t₂ ∶ t₁ ∶ u ∶ A
    → Γ ⊢ ⇓² t₂ ∶ ⇓ t₁ ∶ A
M⇓³_ {t₂} {t₁} = M⇓ⁿ_ {𝐭 = t₂ ∷ t₁ ∷ []}


-- --------------------------------------------------------------------------
--
-- Example terms for level 0, 1, and 2 IKS combinators


-- S4: A ⊃ A
eI : ∀{A}
   → ⊩ A ⊃ A
eI = M𝜆 M𝑣 Z

-- S4: □(A ⊃ A)
eI² : ∀{A}
    → ⊩ 𝜆 𝑣 0
        ∶ (A ⊃ A)
eI² = M𝜆² M𝑣 Z

-- S4: □□(A ⊃ A)
eI³ : ∀{A}
    → ⊩ 𝜆² 𝑣 0
        ∶ 𝜆 𝑣 0
          ∶ (A ⊃ A)
eI³ = M𝜆³ M𝑣 Z


-- S4: A ⊃ B ⊃ A
eK : ∀{A B}
   → ⊩ A ⊃ B ⊃ A
eK = M𝜆 M𝜆 M𝑣 S Z

-- S4: □(A ⊃ B ⊃ A)
eK² : ∀{A B}
    → ⊩ 𝜆 𝜆 𝑣 1
        ∶ (A ⊃ B ⊃ A)
eK² = M𝜆² M𝜆² M𝑣 S Z

-- S4: □□(A ⊃ B ⊃ A)
eK³ : ∀{A B}
    → ⊩ 𝜆² 𝜆² 𝑣 1
        ∶ 𝜆 𝜆 𝑣 1
          ∶ (A ⊃ B ⊃ A)
eK³ = M𝜆³ M𝜆³ M𝑣 S Z


-- S4: (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
eS : ∀{A B C}
   → ⊩ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
eS = M𝜆 M𝜆 M𝜆 (M𝑣 S S Z M∘ M𝑣 Z) M∘ (M𝑣 S Z M∘ M𝑣 Z)

-- S4: □((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
eS² : ∀{A B C}
    → ⊩ 𝜆 𝜆 𝜆 (𝑣 2 ∘ 𝑣 0) ∘ (𝑣 1 ∘ 𝑣 0)
        ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
eS² = M𝜆² M𝜆² M𝜆² (M𝑣 S S Z M∘² M𝑣 Z) M∘² (M𝑣 S Z M∘² M𝑣 Z)

-- S4: □□((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
eS³ : ∀{A B C}
    → ⊩ 𝜆² 𝜆² 𝜆² (𝑣 2 ∘² 𝑣 0) ∘² (𝑣 1 ∘² 𝑣 0)
        ∶ 𝜆 𝜆 𝜆 (𝑣 2 ∘ 𝑣 0) ∘ (𝑣 1 ∘ 𝑣 0)
          ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
eS³ = M𝜆³ M𝜆³ M𝜆³ (M𝑣 S S Z M∘³ M𝑣 Z) M∘³ (M𝑣 S Z M∘³ M𝑣 Z)


-- --------------------------------------------------------------------------
--
-- Example terms for S4 axioms


-- S4: □(A ⊃ B) ⊃ □A ⊃ □B
axK : ∀{A B f x}
    → ⊩ (f ∶ (A ⊃ B)) ⊃ x ∶ A ⊃ (f ∘ x) ∶ B
axK = M𝜆 M𝜆 (M𝑣 S Z M∘² M𝑣 Z)

-- S4: □(□(A ⊃ B) ⊃ □A ⊃ □B)
axK² : ∀{A B f x}
     → ⊩ 𝜆 𝜆 𝑣 1 ∘² 𝑣 0
         ∶ (f ∶ (A ⊃ B) ⊃ x ∶ A ⊃ (f ∘ x) ∶ B)
axK² = M𝜆² M𝜆² (M𝑣 S Z M∘³ M𝑣 Z)

-- S4: □A ⊃ A
axT : ∀{A x}
    → ⊩ x ∶ A ⊃ A
axT = M𝜆 M⇓ M𝑣 Z

-- S4: □A ⊃ □□A
ax4 : ∀{A x}
     → ⊩ x ∶ A ⊃ ! x ∶ x ∶ A
ax4 = M𝜆 M⇑ M𝑣 Z


-- --------------------------------------------------------------------------
--
-- Terms for example 1, p. 28 [1]


-- S4: □(□A ⊃ A)
e11 : ∀{A x}
    → ⊩ 𝜆 ⇓ 𝑣 0
        ∶ (x ∶ A ⊃ A)
e11 = M𝜆² M⇓² M𝑣 Z

-- S4: □(□A ⊃ □□A)
e12 : ∀{A x}
    → ⊩ 𝜆 ⇑ 𝑣 0
        ∶ (x ∶ A ⊃ ! x ∶ x ∶ A)
e12 = M𝜆² M⇑² M𝑣 Z

-- S4: □□(A ⊃ B ⊃ A ∧ B)
e13 : ∀{A B}
    → ⊩ 𝜆² 𝜆² 𝑝²⟨ 𝑣 1 , 𝑣 0 ⟩
        ∶ 𝜆 𝜆 𝑝⟨ 𝑣 1 , 𝑣 0 ⟩
          ∶ (A ⊃ B ⊃ A ∧ B)
e13 = M𝜆³ M𝜆³ M𝑝³⟨ M𝑣 S Z , M𝑣 Z ⟩

-- S4: □(□A ⊃ □B ⊃ □□(A ∧ B))
e14 : ∀{A B x y}
    → ⊩ 𝜆 𝜆 ⇑ 𝑝²⟨ 𝑣 1 , 𝑣 0 ⟩
        ∶ (x ∶ A ⊃ y ∶ B ⊃ ! 𝑝⟨ x , y ⟩ ∶ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
e14 = M𝜆² M𝜆² M⇑² M𝑝³⟨ M𝑣 S Z , M𝑣 Z ⟩


-- --------------------------------------------------------------------------
--
-- Additional example terms


-- S4: □(□A ⊃ □B ⊃ □(A ∧ B))
ex1 : ∀{A B x y}
    → ⊩ 𝜆 𝜆 𝑝²⟨ 𝑣 1 , 𝑣 0 ⟩
        ∶ (x ∶ A ⊃ y ∶ B ⊃ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
ex1 = M𝜆² M𝜆² M𝑝³⟨ M𝑣 S Z , M𝑣 Z ⟩

-- S4: □(□A ∧ □B ⊃ □□(A ∧ B))
ex2 : ∀{A B x y}
    → ⊩ 𝜆 ⇑ 𝑝²⟨ 𝜋₀ 𝑣 0 , 𝜋₁ 𝑣 0 ⟩
        ∶ (x ∶ A ∧ y ∶ B ⊃ ! 𝑝⟨ x , y ⟩ ∶ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
ex2 = M𝜆² M⇑² M𝑝³⟨ M𝜋₀² M𝑣 Z , M𝜋₁² M𝑣 Z ⟩

-- S4: □(□A ∧ □B ⊃ □(A ∧ B))
ex3 : ∀{A B x y}
    → ⊩ 𝜆 𝑝²⟨ 𝜋₀ 𝑣 0 , 𝜋₁ 𝑣 0 ⟩
        ∶ (x ∶ A ∧ y ∶ B ⊃ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
ex3 = M𝜆² M𝑝³⟨ M𝜋₀² M𝑣 Z , M𝜋₁² M𝑣 Z ⟩


-- --------------------------------------------------------------------------
--
-- Terms for example 2, pp. 31–32 [1]


e2 : ∀{A x}
   → ⊩ 𝜆² ⇓² ⇑² 𝑣 0
       ∶ 𝜆 ⇓ ⇑ 𝑣 0
         ∶ (x ∶ A ⊃ x ∶ A)
e2 = M𝜆³ M⇓³ M⇑³ M𝑣 Z

e2′ : ∀{A x}
    → ⊩ 𝜆² 𝑣 0
        ∶ 𝜆 𝑣 0
          ∶ (x ∶ A ⊃ x ∶ A)
e2′ = M𝜆³ M𝑣 Z


-- --------------------------------------------------------------------------
--
-- Theorem 1 (Internalisation principle), p. 29 [1]


prefix : ∀{m} → Cx m → Cx m
prefix ∅               = ∅
prefix (Γ , ⟨ n , A ⟩) = prefix Γ , ⟨ suc n , A ⟩


in∈ : ∀{n A m k} {Γ : Cx m}
    → ⟨ n , A ⟩ ∈[ k ] Γ
    → ⟨ suc n , A ⟩ ∈[ k ] prefix Γ
in∈ Z     = Z
in∈ (S i) = S (in∈ i)


in⊢ : ∀{A m} {Γ : Cx m}
    → Γ ⊢ A
    → Σ Tm λ t → prefix Γ ⊢ t ∶ A

in⊢ (M𝑣_ {n} {k} i)
    = ⟨ 𝑣 k , M𝑣 (in∈ i) ⟩

in⊢ (M𝜆ⁿ_ {n} {𝐭} D)
    = let ⟨ s , C ⟩ = in⊢ D
      in
        ⟨ 𝜆[ suc n ] s
        , M𝜆ⁿ_ {𝐭 = s ∷ 𝐭} C
        ⟩

in⊢ (_M∘ⁿ_ {n} {𝐭} {𝐬} Dₜ Dₛ)
    = let ⟨ sₜ , Cₜ ⟩ = in⊢ Dₜ
          ⟨ sₛ , Cₛ ⟩ = in⊢ Dₛ
      in
        ⟨ sₜ ∘[ suc n ] sₛ
        , _M∘ⁿ_ {𝐭 = sₜ ∷ 𝐭} {𝐬 = sₛ ∷ 𝐬} Cₜ Cₛ
        ⟩

in⊢ (M𝑝ⁿ⟨_,_⟩ {n} {𝐭} {𝐬} Dₜ Dₛ)
    = let ⟨ sₜ , Cₜ ⟩ = in⊢ Dₜ
          ⟨ sₛ , Cₛ ⟩ = in⊢ Dₛ
      in
        ⟨ 𝑝[ suc n ]⟨ sₜ , sₛ ⟩
        , M𝑝ⁿ⟨_,_⟩ {𝐭 = sₜ ∷ 𝐭} {𝐬 = sₛ ∷ 𝐬} Cₜ Cₛ
        ⟩

in⊢ (M𝜋₀ⁿ_ {n} {𝐭} D)
    = let ⟨ s , C ⟩ = in⊢ D
      in
        ⟨ 𝜋₀[ suc n ] s
        , M𝜋₀ⁿ_ {𝐭 = s ∷ 𝐭} C
        ⟩

in⊢ (M𝜋₁ⁿ_ {n} {𝐭} D)
    = let ⟨ s , C ⟩ = in⊢ D
      in
        ⟨ 𝜋₁[ suc n ] s
        , M𝜋₁ⁿ_ {𝐭 = s ∷ 𝐭} C
        ⟩

in⊢ (M⇑ⁿ_ {n} {𝐭} D)
    = let ⟨ s , C ⟩ = in⊢ D
      in
        ⟨ ⇑[ suc n ] s
        , M⇑ⁿ_ {𝐭 = s ∷ 𝐭} C
        ⟩

in⊢ (M⇓ⁿ_ {n} {𝐭} D)
    = let ⟨ s , C ⟩ = in⊢ D
      in
        ⟨ ⇓[ suc n ] s
        , M⇓ⁿ_ {𝐭 = s ∷ 𝐭} C
        ⟩


-- --------------------------------------------------------------------------
--
-- Constructive necessitation


nec : ∀{A}
    → ⊩ A
    → Σ Tm λ t
       → ⊩ t ∶ A
nec D = let ⟨ s , C ⟩ = in⊢ D
        in
          ⟨ s , C ⟩


eI²′ : ∀{A}
    → Σ Tm λ t
       → ⊩ t ∶ (A ⊃ A)
eI²′ = nec eI

eI³′ : ∀{A}
    → Σ Tm λ t
       → ⊩ t ∶ 𝜆 𝑣 0 ∶ (A ⊃ A)
eI³′ = nec eI²

eI⁴′ : ∀{A}
    → Σ Tm λ t
       → ⊩ t ∶ 𝜆² 𝑣 0 ∶ 𝜆 𝑣 0 ∶ (A ⊃ A)
eI⁴′ = nec eI³


eI³″ : ∀{A}
    → Σ Tm λ t
       → ⊩ t ∶ 𝜆 𝑣 0 ∶ (A ⊃ A)
eI³″ = nec (proj₂ (eI²′))

eI⁴″ : ∀{A}
    → Σ Tm λ t
       → ⊩ t ∶ 𝜆² 𝑣 0 ∶ 𝜆 𝑣 0 ∶ (A ⊃ A)
eI⁴″ = nec (proj₂ (eI³′))
