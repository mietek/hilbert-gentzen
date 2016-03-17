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

infixl 9 !_ 𝑣_
infixl 8 𝜋₀_ 𝜋₀²_ 𝜋₁_ 𝜋₁²_
infixl 7 _∘_ _∘²_
infixr 6 ⇑_ ⇑²_ ⇓_ ⇓²_
infixr 5 𝜆_ 𝜆²_
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
*ⁿ 𝐭 ∷ A = foldr (λ _ → Ty) _∶_ A 𝐭

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


data _∈_  : ∀{m} → Hyp → Cx m → Set where
  Z  : ∀{m} {Γ : Cx m} {A : Hyp}
     → A ∈ (Γ , A)

  S_ : ∀{m} {Γ : Cx m} {A B : Hyp}
     → A ∈ Γ
     → A ∈ (Γ , B)


toℕ : ∀{m} {Γ : Cx m} {A : Hyp} → A ∈ Γ → ℕ
toℕ Z     = zero
toℕ (S i) = suc (toℕ i)


𝑣[_]_∷_ : (n : ℕ) → Var → Ty → Ty
𝑣[ n ] x ∷ A = *ⁿ (replicate n (𝑣 x)) ∷ A


-- --------------------------------------------------------------------------
--
-- Typing judgment


data _⊢_ {m : ℕ} (Γ : Cx m) : Ty → Set where
  M𝑣   : ∀{n} {A : Ty}
       → (i : ⟨ n , A ⟩ ∈ Γ)
       → Γ ⊢ 𝑣[ n ] (toℕ i) ∷ A

  M𝜆ⁿ  : ∀{n} {𝐭 : Tms n} {A B : Ty}
       → Γ , ⟨ n , A ⟩ ⊢ *ⁿ 𝐭 ∷ B
       → Γ ⊢ 𝜆ⁿ 𝐭 ∷ (A ⊃ B)

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
    → Γ , ⟨ 0 , A ⟩ ⊢ B
    → Γ ⊢ A ⊃ B
M𝜆 = M𝜆ⁿ {𝐭 = []}

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


M𝜆²  : ∀{t A B m} {Γ : Cx m}
     → Γ , ⟨ 1 , A ⟩ ⊢ t ∶ B
     → Γ ⊢ 𝜆 t ∶ (A ⊃ B)
M𝜆² {t} = M𝜆ⁿ {𝐭 = t ∷ []}

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


M𝜆³  : ∀{t₂ t₁ A B m} {Γ : Cx m}
     → Γ , ⟨ 2 , A ⟩ ⊢ t₂ ∶ t₁ ∶ B
     → Γ ⊢ 𝜆² t₂ ∶ 𝜆 t₁ ∶ (A ⊃ B)
M𝜆³ {t₂} {t₁} = M𝜆ⁿ {𝐭 = t₂ ∷ t₁ ∷ []}

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
eI² : ∀{A}
    → ⊩ 𝜆 𝑣 0
        ∶ (A ⊃ A)
eI² = M𝜆² (M𝑣 Z)

-- S4: □□(A ⊃ A)
eI³ : ∀{A}
    → ⊩ 𝜆² 𝑣 0
        ∶ 𝜆 𝑣 0
          ∶ (A ⊃ A)
eI³ = M𝜆³ (M𝑣 Z)


-- S4: A ⊃ B ⊃ A
eK : ∀{A B}
   → ⊩ A ⊃ B ⊃ A
eK = M𝜆 (M𝜆 (M𝑣 (S Z)))

-- S4: □(A ⊃ B ⊃ A)
eK² : ∀{A B}
    → ⊩ 𝜆 𝜆 𝑣 1
        ∶ (A ⊃ B ⊃ A)
eK² = M𝜆² (M𝜆² (M𝑣 (S Z)))

-- S4: □□(A ⊃ B ⊃ A)
eK³ : ∀{A B}
    → ⊩ 𝜆² 𝜆² 𝑣 1
        ∶ 𝜆 𝜆 𝑣 1
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
eS² : ∀{A B C}
    → ⊩ 𝜆 𝜆 𝜆 (𝑣 2 ∘ 𝑣 0) ∘ (𝑣 1 ∘ 𝑣 0)
        ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
eS² = M𝜆² (M𝜆² (M𝜆² (M∘² (M∘² (M𝑣 (S S Z))
                              (M𝑣 Z))
                         (M∘² (M𝑣 (S Z))
                              (M𝑣 Z)))))

-- S4: □□((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
eS³ : ∀{A B C}
    → ⊩ 𝜆² 𝜆² 𝜆² (𝑣 2 ∘² 𝑣 0) ∘² (𝑣 1 ∘² 𝑣 0)
        ∶ 𝜆 𝜆 𝜆 (𝑣 2 ∘ 𝑣 0) ∘ (𝑣 1 ∘ 𝑣 0)
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
axK² : ∀{A B f x}
     → ⊩ 𝜆 𝜆 𝑣 1 ∘² 𝑣 0
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
e11 : ∀{A x}
    → ⊩ 𝜆 ⇓ 𝑣 0
        ∶ (x ∶ A ⊃ A)
e11 = M𝜆² (M⇓² (M𝑣 Z))

-- S4: □(□A ⊃ □□A)
e12 : ∀{A x}
    → ⊩ 𝜆 ⇑ 𝑣 0
        ∶ (x ∶ A ⊃ ! x ∶ x ∶ A)
e12 = M𝜆² (M⇑² (M𝑣 Z))

-- S4: □□(A ⊃ B ⊃ A ∧ B)
e13 : ∀{A B}
    → ⊩ 𝜆² 𝜆² 𝑝²⟨ 𝑣 1 , 𝑣 0 ⟩
        ∶ 𝜆 𝜆 𝑝⟨ 𝑣 1 , 𝑣 0 ⟩
          ∶ (A ⊃ B ⊃ A ∧ B)
e13 = M𝜆³ (M𝜆³ (M𝑝³ (M𝑣 (S Z))
                    (M𝑣 Z)))

-- S4: □(□A ⊃ □B ⊃ □□(A ∧ B))
e14 : ∀{A B x y}
    → ⊩ 𝜆 𝜆 ⇑ 𝑝²⟨ 𝑣 1 , 𝑣 0 ⟩
        ∶ (x ∶ A ⊃ y ∶ B ⊃ ! 𝑝⟨ x , y ⟩ ∶ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
e14 = M𝜆² (M𝜆² (M⇑² (M𝑝³ (M𝑣 (S Z))
                         (M𝑣 Z))))


-- --------------------------------------------------------------------------
--
-- Additional example terms


-- S4: □(□A ⊃ □B ⊃ □(A ∧ B))
ex1 : ∀{A B x y}
    → ⊩ 𝜆 𝜆 𝑝²⟨ 𝑣 1 , 𝑣 0 ⟩
        ∶ (x ∶ A ⊃ y ∶ B ⊃ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
ex1 = M𝜆² (M𝜆² (M𝑝³ (M𝑣 (S Z))
                    (M𝑣 Z)))

-- S4: □(□A ∧ □B ⊃ □□(A ∧ B))
ex2 : ∀{A B x y}
    → ⊩ 𝜆 ⇑ 𝑝²⟨ 𝜋₀ 𝑣 0 , 𝜋₁ 𝑣 0 ⟩
        ∶ (x ∶ A ∧ y ∶ B ⊃ ! 𝑝⟨ x , y ⟩ ∶ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
ex2 = M𝜆² (M⇑² (M𝑝³ (M𝜋₀² (M𝑣 Z))
                    (M𝜋₁² (M𝑣 Z))))

-- S4: □(□A ∧ □B ⊃ □(A ∧ B))
ex3 : ∀{A B x y}
    → ⊩ 𝜆 𝑝²⟨ 𝜋₀ 𝑣 0 , 𝜋₁ 𝑣 0 ⟩
        ∶ (x ∶ A ∧ y ∶ B ⊃ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
ex3 = M𝜆² (M𝑝³ (M𝜋₀² (M𝑣 Z))
               (M𝜋₁² (M𝑣 Z)))


-- --------------------------------------------------------------------------
--
-- Terms for example 2, pp. 31–32 [1]


e2 : ∀{A x}
   → ⊩ 𝜆² ⇓² ⇑² 𝑣 0
       ∶ 𝜆 ⇓ ⇑ 𝑣 0
         ∶ (x ∶ A ⊃ x ∶ A)
e2 = M𝜆³ (M⇓³ (M⇑³ (M𝑣 Z)))

e2′ : ∀{A x}
    → ⊩ 𝜆² 𝑣 0
        ∶ 𝜆 𝑣 0
          ∶ (x ∶ A ⊃ x ∶ A)
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


{-
wk∈ : ∀{A m m′} {Γ : Cx m} {Γ′ : Cx m′}
    → Γ ≲ Γ′    → A ∈ Γ
    → A ∈ Γ′
wk∈ base     ()
wk∈ (keep P) Z     = Z
wk∈ (keep P) (S i) = S (wk∈ P i)
wk∈ (drop P) i     = S (wk∈ P i)
-}

postulate
  pwk∈ : ∀{n A m m′} {Γ : Cx m} {Γ′ : Cx m′}
      → Γ ≲ Γ′  → (i : ⟨ n , A ⟩ ∈ Γ)
      → Γ′ ⊢ 𝑣[ n ] (toℕ i) ∷ A


wk⊢ : ∀{A m m′} {Γ : Cx m} {Γ′ : Cx m′}
    → Γ ≲ Γ′    → Γ ⊢ A
    → Γ′ ⊢ A
wk⊢ P (M𝑣 i)                   = pwk∈ P i
wk⊢ P (M𝜆ⁿ  {𝐭 = 𝐭} D)         = M𝜆ⁿ  {𝐭 = 𝐭} (wk⊢ (keep P) D)
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


{-
cn∈ : ∀{A m m′} {Γ : Cx m} {Γ′ : Cx m′}
    → Γ ≳ Γ′    → A ∈ Γ
    → A ∈ Γ′
cn∈ base     ()
cn∈ (once P) Z     = Z
cn∈ (once P) (S i) = S (cn∈ P i)
cn∈ (more P) Z     = Z
cn∈ (more P) (S i) = cn∈ (once P) i
-}

postulate
  pcn∈ : ∀{n A m m′} {Γ : Cx m} {Γ′ : Cx m′}
      → Γ ≳ Γ′  → (i : ⟨ n , A ⟩ ∈ Γ)
      → Γ′ ⊢ 𝑣[ n ] (toℕ i) ∷ A


cn⊢ : ∀{A m m′} {Γ : Cx m} {Γ′ : Cx m′}
    → Γ ≳ Γ′    → Γ ⊢ A
    → Γ′ ⊢ A
cn⊢ P (M𝑣 i)                   = pcn∈ P i
cn⊢ P (M𝜆ⁿ  {𝐭 = 𝐭} D)         = M𝜆ⁿ  {𝐭 = 𝐭} (cn⊢ (once P) D)
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


{-
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
-}

postulate
  pex∈ : ∀{n A m} {Γ Γ′ : Cx m}
      → Γ ≈ Γ′  → (i : ⟨ n , A ⟩ ∈ Γ)
      → Γ′ ⊢ 𝑣[ n ] (toℕ i) ∷ A


ex⊢ : ∀{A m} {Γ Γ′ : Cx m}
    → Γ ≈ Γ′    → Γ ⊢ A
    → Γ′ ⊢ A
ex⊢ P (M𝑣 i)                   = pex∈ P i
ex⊢ P (M𝜆ⁿ  {𝐭 = 𝐭} D)         = M𝜆ⁿ  {𝐭 = 𝐭} (ex⊢ (just P) D)
ex⊢ P (M∘ⁿ  {𝐭 = 𝐭} {𝐬} Dₜ Dₛ) = M∘ⁿ  {𝐭 = 𝐭} {𝐬} (ex⊢ P Dₜ) (ex⊢ P Dₛ)
ex⊢ P (M𝑝ⁿ  {𝐭 = 𝐭} {𝐬} Dₜ Dₛ) = M𝑝ⁿ  {𝐭 = 𝐭} {𝐬} (ex⊢ P Dₜ) (ex⊢ P Dₛ)
ex⊢ P (M𝜋₀ⁿ {𝐭 = 𝐭} D)         = M𝜋₀ⁿ {𝐭 = 𝐭} (ex⊢ P D)
ex⊢ P (M𝜋₁ⁿ {𝐭 = 𝐭} D)         = M𝜋₁ⁿ {𝐭 = 𝐭} (ex⊢ P D)
ex⊢ P (M⇑ⁿ  {𝐭 = 𝐭} D)         = M⇑ⁿ  {𝐭 = 𝐭} (ex⊢ P D)
ex⊢ P (M⇓ⁿ  {𝐭 = 𝐭} D)         = M⇓ⁿ  {𝐭 = 𝐭} (ex⊢ P D)


-- --------------------------------------------------------------------------
--
-- Theorem 1 (Internalisation principle), p. 29 [1]


prefix : ∀{m} → Cx m → Cx m
prefix ∅               = ∅
prefix (Γ , ⟨ n , A ⟩) = prefix Γ , ⟨ suc n , A ⟩


{-
in∈ : ∀{n A m} {Γ : Cx m}
    → ⟨ n , A ⟩ ∈ Γ
    → ⟨ suc n , A ⟩ ∈ prefix Γ
in∈ Z     = Z
in∈ (S i) = S (in∈ i)
-}

postulate
  pin∈ : ∀{n A m} {Γ : Cx m}
      → (i : ⟨ n , A ⟩ ∈ Γ)
      → prefix Γ ⊢ 𝑣[ suc n ] (toℕ i) ∷ A


in⊢ : ∀{A m} {Γ : Cx m}
    → Γ ⊢ A
    → Σ Tm (λ t → prefix Γ ⊢ t ∶ A)

in⊢ (M𝑣 {n} i)
    = ⟨ 𝑣 (toℕ i) , pin∈ i ⟩

in⊢ (M𝜆ⁿ {n} {𝐭} D)
    = let ⟨ s , C ⟩ = in⊢ D
      in
        ⟨ 𝜆[ suc n ] s
        , M𝜆ⁿ {𝐭 = s ∷ 𝐭} C
        ⟩

in⊢ (M∘ⁿ {n} {𝐭} {𝐬} Dₜ Dₛ)
    = let ⟨ sₜ , Cₜ ⟩ = in⊢ Dₜ
          ⟨ sₛ , Cₛ ⟩ = in⊢ Dₛ
      in
        ⟨ sₜ ∘[ suc n ] sₛ
        , M∘ⁿ {𝐭 = sₜ ∷ 𝐭} {𝐬 = sₛ ∷ 𝐬} Cₜ Cₛ
        ⟩

in⊢ (M𝑝ⁿ {n} {𝐭} {𝐬} Dₜ Dₛ)
    = let ⟨ sₜ , Cₜ ⟩ = in⊢ Dₜ
          ⟨ sₛ , Cₛ ⟩ = in⊢ Dₛ
      in
        ⟨ 𝑝[ suc n ]⟨ sₜ , sₛ ⟩
        , M𝑝ⁿ {𝐭 = sₜ ∷ 𝐭} {𝐬 = sₛ ∷ 𝐬} Cₜ Cₛ
        ⟩

in⊢ (M𝜋₀ⁿ {n} {𝐭} D)
    = let ⟨ s , C ⟩ = in⊢ D
      in
        ⟨ 𝜋₀[ suc n ] s
        , M𝜋₀ⁿ {𝐭 = s ∷ 𝐭} C
        ⟩

in⊢ (M𝜋₁ⁿ {n} {𝐭} D)
    = let ⟨ s , C ⟩ = in⊢ D
      in
        ⟨ 𝜋₁[ suc n ] s
        , M𝜋₁ⁿ {𝐭 = s ∷ 𝐭} C
        ⟩

in⊢ (M⇑ⁿ {n} {𝐭} D)
    = let ⟨ s , C ⟩ = in⊢ D
      in
        ⟨ ⇑[ suc n ] s
        , M⇑ⁿ {𝐭 = s ∷ 𝐭} C
        ⟩

in⊢ (M⇓ⁿ {n} {𝐭} D)
    = let ⟨ s , C ⟩ = in⊢ D
      in
        ⟨ ⇓[ suc n ] s
        , M⇓ⁿ {𝐭 = s ∷ 𝐭} C
        ⟩


-- --------------------------------------------------------------------------
--
-- Constructive necessitation


nec : ∀{A}
    → ∅ ⊢ A
    → Σ Tm (λ t → ⊩ t ∶ A)
nec D = let ⟨ s , C ⟩ = in⊢ D
        in
          ⟨ s , wk⊢ ∅≲Γ C ⟩


eI²′ : ∀{A}
     → Σ Tm (λ t → ⊩ t ∶ (A ⊃ A))
eI²′ = nec eI

eI³′ : ∀{A}
     → Σ Tm (λ t → ⊩ t ∶ 𝜆 𝑣 0 ∶ (A ⊃ A))
eI³′ = nec eI²

eI⁴′ : ∀{A}
     → Σ Tm (λ t → ⊩ t ∶ 𝜆² 𝑣 0 ∶ 𝜆 𝑣 0 ∶ (A ⊃ A))
eI⁴′ = nec eI³


eI³″ : ∀{A}
     → Σ Tm (λ t → ⊩ t ∶ 𝜆 𝑣 0 ∶ (A ⊃ A))
eI³″ = nec (proj₂ (eI²′))

eI⁴″ : ∀{A}
     → Σ Tm (λ t → ⊩ t ∶ 𝜆² 𝑣 0 ∶ 𝜆 𝑣 0 ∶ (A ⊃ A))
eI⁴″ = nec (proj₂ (eI³′))
