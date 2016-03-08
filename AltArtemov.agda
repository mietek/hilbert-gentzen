{-

An implementation of the Alt-Artëmov system λ∞
==============================================

Miëtek Bak  <mietek@bak.io>


Work in progress.  Checked with Agda 2.4.2.5.

For easy editing with Emacs agda-mode, add to your .emacs file:

'(agda-input-user-translations
   (quote
    (("imp" "⊃") ("iff" "⊃⊂") ("not" "¬") ("ent" "⊢") ("thm" "⊩")
     ("s" "𝐬") ("t" "𝐭") ("x" "𝐱") ("y" "𝐲") ("N" "ℕ")
     ("v" "𝜈") ("v0" "𝜈⁰") ("v1" "𝜈") ("v2" "𝜈²") ("vn" "𝜈ⁿ")
     ("l" "𝜆") ("l0" "𝜆⁰") ("l1" "𝜆") ("l2" "𝜆²") ("ln" "𝜆ⁿ") ("." "．")
     ("o" "∘") ("o0" "∘⁰") ("o1" "∘") ("o2" "∘²") ("on" "∘ⁿ")
     ("p" "𝑝") ("p0" "𝑝⁰") ("p1" "𝑝") ("p2" "𝑝²") ("pn" "𝑝ⁿ")
     ("1" "𝜋₀") ("10" "𝜋₀⁰") ("11" "𝜋₀") ("12" "𝜋₀²") ("1n" "𝜋₀ⁿ")
     ("2" "𝜋₁") ("20" "𝜋₁⁰") ("21" "𝜋₁") ("12" "𝜋₁²") ("2n" "𝜋₁ⁿ")
     ("u" "⇑") ("u0" "⇑⁰") ("u1" "⇑") ("u2" "⇑²") ("un" "⇑ⁿ")
     ("d" "⇓") ("d0" "⇓⁰") ("d1" "⇓") ("d2" "⇓²") ("dn" "⇓ⁿ"))))


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
  using (Σ ; proj₂)
  renaming (_,_ to ⟨_,_⟩)

open import Data.Vec
  using (Vec ; _∷_ ; _∈_ ; foldr ; map ; zipWith)
  renaming ([] to ∅ ; here to Z ; there to S)

infixl 9 !_ 𝜈_
infixl 8 _∘_ _∘²_ _∘^[_]_
infixr 7 ⇑_ ⇑²_ ⇑^[_]_ ⇓_ ⇓²_ ⇓^[_]_
infixr 6 𝜆_．_ 𝜆²_．_ 𝜆^[_]_．_
infixr 5 _∶_
infixr 4 ¬_
infixl 3 _∧_
infixl 2 _,_
infixr 1 _⊃_ _⊃⊂_
infixr 0 _⊢_ ⊩_


mutual

  Var : Set
  Var = ℕ


  -- Term constructors

  data Tm : Set where
    𝜈_         : Var            → Tm    -- Variable
    𝜆^[_]_．_   : ℕ   → Var → Tm → Tm    -- Abstraction
    _∘^[_]_    : Tm  → ℕ   → Tm → Tm    -- Application
    𝑝^[_]⟨_,_⟩ : ℕ   → Tm  → Tm → Tm    -- Pairing
    𝜋₀^[_]_    : ℕ   → Tm       → Tm    -- Left projection
    𝜋₁^[_]_    : ℕ   → Tm       → Tm    -- Right projection
    !_         : Tm             → Tm    -- Proof checking
    ⇑^[_]_     : ℕ   → Tm       → Tm    -- Reification
    ⇓^[_]_     : ℕ   → Tm       → Tm    -- Reflection


  -- Type constructors

  data Ty : Set where
    ⊥   :           Ty    -- Falsehood
    _⊃_ : Ty → Ty → Ty    -- Implication
    _∧_ : Ty → Ty → Ty    -- Conjunction
    _∶_ : Tm → Ty → Ty    -- Provability


-- Example types

⊤      : Ty               -- Truth
⊤      = ⊥ ⊃ ⊥

¬_     : Ty → Ty          -- Negation
¬ A    = A ⊃ ⊥

_⊃⊂_   : Ty → Ty → Ty     -- Equivalence
A ⊃⊂ B = A ⊃ B ∧ B ⊃ A


-- --------------------------------------------------------------------------

-- Vectors

ixMap : ∀{n} {X Y : Set}
      → (ℕ → X → Y) → Vec X n → Vec Y n
ixMap {zero}  f ∅       = ∅
ixMap {suc n} f (x ∷ 𝐱) = f (suc n) x ∷ ixMap f 𝐱

ixZipWith : ∀{n} {X X′ Y : Set}
          → (ℕ → X → X′ → Y) → Vec X n → Vec X′ n → Vec Y n
ixZipWith {zero}  f ∅       ∅       = ∅
ixZipWith {suc n} f (x ∷ 𝐱) (y ∷ 𝐲) = f (suc n) x y ∷ ixZipWith f 𝐱 𝐲


VVar : ℕ → Set
VVar = Vec Var

VTm  : ℕ → Set
VTm  = Vec Tm

VTy  : ℕ → Set
VTy  = Vec Ty


-- Vector notation for type constructors

*ⁿ_∶_          : ∀{n} → VTm n → Ty → Ty
*ⁿ 𝐭 ∶ A       = foldr (λ _ → Ty) _∶_ A 𝐭

𝜈ⁿ_∶_          : ∀{n} → VVar n → Ty → Ty
𝜈ⁿ 𝐱 ∶ A       = *ⁿ (map 𝜈_ 𝐱) ∶ A

𝜆ⁿ_．_∶_        : ∀{n} → VVar n → VTm n → Ty → Ty
𝜆ⁿ 𝐱 ． 𝐭 ∶ A   = *ⁿ (ixZipWith 𝜆^[_]_．_ 𝐱 𝐭) ∶ A

_∘ⁿ_∶_         : ∀{n} → VTm n → VTm n → Ty → Ty
𝐭 ∘ⁿ 𝐬 ∶ A     = *ⁿ (ixZipWith (λ n t s → t ∘^[ n ] s) 𝐭 𝐬) ∶ A

𝑝ⁿ⟨_,_⟩∶_      : ∀{n} → VTm n → VTm n → Ty → Ty
𝑝ⁿ⟨ 𝐭 , 𝐬 ⟩∶ A = *ⁿ (ixZipWith 𝑝^[_]⟨_,_⟩ 𝐭 𝐬) ∶ A

𝜋₀ⁿ_∶_         : ∀{n} → VTm n → Ty → Ty
𝜋₀ⁿ 𝐭 ∶ A      = *ⁿ (ixMap 𝜋₀^[_]_ 𝐭) ∶ A

𝜋₁ⁿ_∶_         : ∀{n} → VTm n → Ty → Ty
𝜋₁ⁿ 𝐭 ∶ A      = *ⁿ (ixMap 𝜋₁^[_]_ 𝐭) ∶ A

⇑ⁿ_∶_          : ∀{n} → VTm n → Ty → Ty
⇑ⁿ 𝐭 ∶ A       = *ⁿ (ixMap ⇑^[_]_ 𝐭) ∶ A

⇓ⁿ_∶_          : ∀{n} → VTm n → Ty → Ty
⇓ⁿ 𝐭 ∶ A       = *ⁿ (ixMap ⇓^[_]_ 𝐭) ∶ A


-- --------------------------------------------------------------------------

-- Typing contexts

Cx : ℕ → Set
Cx = Vec Ty

_,_ : {m : ℕ} → Cx m → Ty → Cx (suc m)
Γ , A = A ∷ Γ


-- Typing rules

data _⊢_ {m : ℕ} (Γ : Cx m) : Ty → Set where
  R𝜈ⁿ  : ∀{n} {𝐱 : VVar n} {A : Ty}
       → 𝜈ⁿ 𝐱 ∶ A ∈ Γ
       → Γ ⊢ 𝜈ⁿ 𝐱 ∶ A

  R𝜆ⁿ  : ∀{n} {𝐱 : VVar n} {𝐭 : VTm n} {A B : Ty}
       → Γ , 𝜈ⁿ 𝐱 ∶ A ⊢ *ⁿ 𝐭 ∶ B
       → Γ ⊢ 𝜆ⁿ 𝐱 ． 𝐭 ∶ (A ⊃ B)

  R∘ⁿ  : ∀{n} {𝐭 𝐬 : VTm n} {A B : Ty}
       → Γ ⊢ *ⁿ 𝐭 ∶ (A ⊃ B)    → Γ ⊢ *ⁿ 𝐬 ∶ A
       → Γ ⊢ 𝐭 ∘ⁿ 𝐬 ∶ B

  R𝑝ⁿ  : ∀{n} {𝐭 𝐬 : VTm n} {A B : Ty}
       → Γ ⊢ *ⁿ 𝐭 ∶ A          → Γ ⊢ *ⁿ 𝐬 ∶ B
       → Γ ⊢ 𝑝ⁿ⟨ 𝐭 , 𝐬 ⟩∶ (A ∧ B)

  R𝜋₀ⁿ : ∀{n} {𝐭 : VTm n} {A B : Ty}
       → Γ ⊢ *ⁿ 𝐭 ∶ (A ∧ B)
       → Γ ⊢ 𝜋₀ⁿ 𝐭 ∶ A

  R𝜋₁ⁿ : ∀{n} {𝐭 : VTm n} {A B : Ty}
       → Γ ⊢ *ⁿ 𝐭 ∶ (A ∧ B)
       → Γ ⊢ 𝜋₁ⁿ 𝐭 ∶ B

  R⇑ⁿ  : ∀{n} {𝐭 : VTm n} {u : Tm} {A : Ty}
       → Γ ⊢ *ⁿ 𝐭 ∶ (u ∶ A)
       → Γ ⊢ ⇑ⁿ 𝐭 ∶ (! u ∶ u ∶ A)

  R⇓ⁿ  : ∀{n} {𝐭 : VTm n} {u : Tm} {A : Ty}
       → Γ ⊢ *ⁿ 𝐭 ∶ (u ∶ A)
       → Γ ⊢ ⇓ⁿ 𝐭 ∶ A


⊩_  : Ty → Set
⊩ A = ∀{m} {Γ : Cx m} → Γ ⊢ A


-- --------------------------------------------------------------------------

-- Simplified notation for level 0 typing rules

R𝜈⁰  : ∀{A m} {Γ : Cx m}
     → A ∈ Γ
     → Γ ⊢ A
R𝜈⁰ = R𝜈ⁿ {𝐱 = ∅}

R𝜆⁰  : ∀{A B m} {Γ : Cx m}
     → Γ , A ⊢ B
     → Γ ⊢ A ⊃ B
R𝜆⁰ = R𝜆ⁿ {𝐱 = ∅} {𝐭 = ∅}

R∘⁰  : ∀{A B m} {Γ : Cx m}
     → Γ ⊢ A ⊃ B    → Γ ⊢ A
     → Γ ⊢ B
R∘⁰ = R∘ⁿ {𝐭 = ∅} {𝐬 = ∅}

R𝑝⁰  : ∀{A B m} {Γ : Cx m}
     → Γ ⊢ A        → Γ ⊢ B
     → Γ ⊢ A ∧ B
R𝑝⁰ = R𝑝ⁿ {𝐭 = ∅} {𝐬 = ∅}

R𝜋₀⁰ : ∀{A B m} {Γ : Cx m}
     → Γ ⊢ A ∧ B
     → Γ ⊢ A
R𝜋₀⁰ = R𝜋₀ⁿ {𝐭 = ∅}

R𝜋₁⁰ : ∀{A B m} {Γ : Cx m}
     → Γ ⊢ A ∧ B
     → Γ ⊢ B
R𝜋₁⁰ = R𝜋₁ⁿ {𝐭 = ∅}

R⇑⁰  : ∀{u A m} {Γ : Cx m}
     → Γ ⊢ u ∶ A
     → Γ ⊢ ! u ∶ u ∶ A
R⇑⁰ = R⇑ⁿ {𝐭 = ∅}

R⇓⁰  : ∀{u A m} {Γ : Cx m}
     → Γ ⊢ u ∶ A
     → Γ ⊢ A
R⇓⁰ = R⇓ⁿ {𝐭 = ∅}


-- Level 0 examples

eI⁰ : ∀{A}
    → ⊩ A ⊃ A
eI⁰ = R𝜆⁰ (R𝜈⁰ Z)


eK⁰ : ∀{A B}
    → ⊩ A ⊃ B ⊃ A
eK⁰ = R𝜆⁰ (R𝜆⁰ (R𝜈⁰ (S Z)))


eS⁰ : ∀{A B C}
    → ⊩ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
eS⁰ = R𝜆⁰ (R𝜆⁰ (R𝜆⁰ (R∘⁰ (R∘⁰ (R𝜈⁰ (S (S Z)))
                              (R𝜈⁰ Z))
                         (R∘⁰ (R𝜈⁰ (S Z))
                              (R𝜈⁰ Z)))))


-- --------------------------------------------------------------------------

-- Simplified notation for level 1 term constructors

𝜆_．_       : Var → Tm → Tm
𝜆 x ． t    = 𝜆^[ 1 ] x ． t

_∘_        : Tm → Tm → Tm
t ∘ s      = t ∘^[ 1 ] s

𝑝⟨_,_⟩     : Tm → Tm → Tm
𝑝⟨ t , s ⟩ = 𝑝^[ 1 ]⟨ t , s ⟩

𝜋₀_        : Tm → Tm
𝜋₀ t       = 𝜋₀^[ 1 ] t

𝜋₁_        : Tm → Tm
𝜋₁ t       = 𝜋₁^[ 1 ] t

⇑_         : Tm → Tm
⇑ t        = ⇑^[ 1 ] t

⇓_         : Tm → Tm
⇓ t        = ⇓^[ 1 ] t


-- Simplified notation for level 1 typing rules

R𝜈  : ∀{x A m} {Γ : Cx m}
    → 𝜈 x ∶ A ∈ Γ
    → Γ ⊢ 𝜈 x ∶ A
R𝜈 {x} = R𝜈ⁿ {𝐱 = x ∷ ∅}

R𝜆  : ∀{x t A B m} {Γ : Cx m}
    → Γ , 𝜈 x ∶ A ⊢ t ∶ B
    → Γ ⊢ 𝜆 x ． t ∶ (A ⊃ B)
R𝜆 {x} {t} = R𝜆ⁿ {𝐱 = x ∷ ∅} {𝐭 = t ∷ ∅}

R∘  : ∀{t s A B m} {Γ : Cx m}
    → Γ ⊢ t ∶ (A ⊃ B)    → Γ ⊢ s ∶ A
    → Γ ⊢ t ∘ s ∶ B
R∘ {t} {s} = R∘ⁿ {𝐭 = t ∷ ∅} {𝐬 = s ∷ ∅}

R𝑝  : ∀{t s A B m} {Γ : Cx m}
    → Γ ⊢ t ∶ A          → Γ ⊢ s ∶ B
    → Γ ⊢ 𝑝⟨ t , s ⟩ ∶ (A ∧ B)
R𝑝 {t} {s} = R𝑝ⁿ {𝐭 = t ∷ ∅} {𝐬 = s ∷ ∅}

R𝜋₀ : ∀{t A B m} {Γ : Cx m}
    → Γ ⊢ t ∶ (A ∧ B)
    → Γ ⊢ 𝜋₀ t ∶ A
R𝜋₀ {t} = R𝜋₀ⁿ {𝐭 = t ∷ ∅}

R𝜋₁ : ∀{t A B m} {Γ : Cx m}
    → Γ ⊢ t ∶ (A ∧ B)
    → Γ ⊢ 𝜋₁ t ∶ B
R𝜋₁ {t} = R𝜋₁ⁿ {𝐭 = t ∷ ∅}

R⇑  : ∀{t u A m} {Γ : Cx m}
    → Γ ⊢ t ∶ u ∶ A
    → Γ ⊢ ⇑ t ∶ ! u ∶ u ∶ A
R⇑ {t} = R⇑ⁿ {𝐭 = t ∷ ∅}

R⇓  : ∀{t u A m} {Γ : Cx m}
    → Γ ⊢ t ∶ u ∶ A
    → Γ ⊢ ⇓ t ∶ A
R⇓ {t} = R⇓ⁿ {𝐭 = t ∷ ∅}


-- Level 1 examples

eI : ∀{x A}
   → ⊩ 𝜆 x ． 𝜈 x
       ∶ (A ⊃ A)
eI = R𝜆 (R𝜈 Z)


eK : ∀{x y A B}
   → ⊩ 𝜆 x ． 𝜆 y ． 𝜈 x
       ∶ (A ⊃ B ⊃ A)
eK = R𝜆 (R𝜆 (R𝜈 (S Z)))


eS : ∀{f g x A B C}
   → ⊩ 𝜆 f ． 𝜆 g ． 𝜆 x ． (𝜈 f ∘ 𝜈 x) ∘ (𝜈 g ∘ 𝜈 x)
       ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
eS = R𝜆 (R𝜆 (R𝜆 (R∘ (R∘ (R𝜈 (S (S Z)))
                        (R𝜈 Z))
                    (R∘ (R𝜈 (S Z))
                        (R𝜈 Z)))))


-- --------------------------------------------------------------------------

-- Simplified notation for level 2 term constructors

𝜆²_．_       : Var → Tm → Tm
𝜆² x ． t    = 𝜆^[ 2 ] x ． t

_∘²_        : Tm → Tm → Tm
t ∘² s      = t ∘^[ 2 ] s

𝑝²⟨_,_⟩     : Tm → Tm → Tm
𝑝²⟨ t , s ⟩ = 𝑝^[ 2 ]⟨ t , s ⟩

𝜋₀²_        : Tm → Tm
𝜋₀² t       = 𝜋₀^[ 2 ] t

𝜋₁²_        : Tm → Tm
𝜋₁² t       = 𝜋₁^[ 2 ] t

⇑²_         : Tm → Tm
⇑² t        = ⇑^[ 2 ] t

⇓²_         : Tm → Tm
⇓² t        = ⇓^[ 2 ] t


-- Simplified notation for level 2 typing rules

R𝜈²  : ∀{x₂ x₁ A m} {Γ : Cx m}
     → 𝜈 x₂ ∶ 𝜈 x₁ ∶ A ∈ Γ
     → Γ ⊢ 𝜈 x₂ ∶ 𝜈 x₁ ∶ A
R𝜈² {x₂} {x₁} = R𝜈ⁿ {𝐱 = x₂ ∷ x₁ ∷ ∅}

R𝜆²  : ∀{x₂ x₁ t₂ t₁ A B m} {Γ : Cx m}
     → Γ , 𝜈 x₂ ∶ 𝜈 x₁ ∶ A ⊢ t₂ ∶ t₁ ∶ B
     → Γ ⊢ 𝜆² x₂ ． t₂ ∶ 𝜆 x₁ ． t₁ ∶ (A ⊃ B)
R𝜆² {x₂} {x₁} {t₂} {t₁} = R𝜆ⁿ {𝐱 = x₂ ∷ x₁ ∷ ∅} {𝐭 = t₂ ∷ t₁ ∷ ∅}

R∘²  : ∀{t₂ t₁ s₂ s₁ A B m} {Γ : Cx m}
     → Γ ⊢ t₂ ∶ t₁ ∶ (A ⊃ B)    → Γ ⊢ s₂ ∶ s₁ ∶ A
     → Γ ⊢ t₂ ∘² s₂ ∶ t₁ ∘ s₁ ∶ B
R∘² {t₂} {t₁} {s₂} {s₁} = R∘ⁿ {𝐭 = t₂ ∷ t₁ ∷ ∅} {𝐬 = s₂ ∷ s₁ ∷ ∅}

R𝑝²  : ∀{t₂ t₁ s₂ s₁ A B m} {Γ : Cx m}
     → Γ ⊢ t₂ ∶ t₁ ∶ A          → Γ ⊢ s₂ ∶ s₁ ∶ B
     → Γ ⊢ 𝑝²⟨ t₂ , s₂ ⟩ ∶ 𝑝⟨ t₁ , s₁ ⟩ ∶ (A ∧ B)
R𝑝² {t₂} {t₁} {s₂} {s₁} = R𝑝ⁿ {𝐭 = t₂ ∷ t₁ ∷ ∅} {𝐬 = s₂ ∷ s₁ ∷ ∅}

R𝜋₀² : ∀{t₂ t₁ A B m} {Γ : Cx m}
     → Γ ⊢ t₂ ∶ t₁ ∶ (A ∧ B)
     → Γ ⊢ 𝜋₀² t₂ ∶ 𝜋₀ t₁ ∶ A
R𝜋₀² {t₂} {t₁} = R𝜋₀ⁿ {𝐭 = t₂ ∷ t₁ ∷ ∅}

R𝜋₁² : ∀{t₂ t₁ A B m} {Γ : Cx m}
     → Γ ⊢ t₂ ∶ t₁ ∶ (A ∧ B)
     → Γ ⊢ 𝜋₁² t₂ ∶ 𝜋₁ t₁ ∶ B
R𝜋₁² {t₂} {t₁} = R𝜋₁ⁿ {𝐭 = t₂ ∷ t₁ ∷ ∅}

R⇑²  : ∀{t₂ t₁ u A m} {Γ : Cx m}
     → Γ ⊢ t₂ ∶ t₁ ∶ u ∶ A
     → Γ ⊢ ⇑² t₂ ∶ ⇑ t₁ ∶ ! u ∶ u ∶ A
R⇑² {t₂} {t₁} = R⇑ⁿ {𝐭 = t₂ ∷ t₁ ∷ ∅}

R⇓²  : ∀{t₂ t₁ u A m} {Γ : Cx m}
     → Γ ⊢ t₂ ∶ t₁ ∶ u ∶ A
     → Γ ⊢ ⇓² t₂ ∶ ⇓ t₁ ∶ A
R⇓² {t₂} {t₁} = R⇓ⁿ {𝐭 = t₂ ∷ t₁ ∷ ∅}


-- Level 2 examples

eI² : ∀{u x A}
    → ⊩ 𝜆² u ． 𝜈 u
        ∶ 𝜆 x ． 𝜈 x
          ∶ (A ⊃ A)
eI² = R𝜆² (R𝜈² Z)


eK² : ∀{u x v y A B}
    → ⊩ 𝜆² u ． 𝜆² v ． 𝜈 u
        ∶ 𝜆 x ． 𝜆 y ． 𝜈 x
          ∶ (A ⊃ B ⊃ A)
eK² = R𝜆² (R𝜆² (R𝜈² (S Z)))


eS² : ∀{f g x A B C}
    → ⊩ 𝜆² f ． 𝜆² g ． 𝜆² x ． (𝜈 f ∘² 𝜈 x) ∘² (𝜈 g ∘² 𝜈 x)
        ∶ 𝜆 f ． 𝜆 g ． 𝜆 x ． (𝜈 f ∘ 𝜈 x) ∘ (𝜈 g ∘ 𝜈 x)
          ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
eS² = R𝜆² (R𝜆² (R𝜆² (R∘² (R∘² (R𝜈² (S (S Z)))
                              (R𝜈² Z))
                         (R∘² (R𝜈² (S Z))
                              (R𝜈² Z)))))


-- --------------------------------------------------------------------------

-- Example 1, p. 28 [1]

e11 : ∀{x y A}
    → ⊩ 𝜆 y ． ⇓ 𝜈 y
        ∶ (𝜈 x ∶ A ⊃ A)
e11 = R𝜆 (R⇓ (R𝜈 Z))

e12 : ∀{x y A}
    → ⊩ 𝜆 y ． ⇑ 𝜈 y
        ∶ (𝜈 x ∶ A ⊃ ! 𝜈 x ∶ 𝜈 x ∶ A)
e12 = R𝜆 (R⇑ (R𝜈 Z))

e13 : ∀{u x v y A B}
    → ⊩ 𝜆² u ． 𝜆² v ． 𝑝²⟨ 𝜈 u , 𝜈 v ⟩
        ∶ 𝜆 x ． 𝜆 y ． 𝑝⟨ 𝜈 x , 𝜈 y ⟩
          ∶ (A ⊃ B ⊃ A ∧ B)
e13 = R𝜆² (R𝜆² (R𝑝² (R𝜈² (S Z))
                    (R𝜈² Z)))

e14 : ∀{u x v y A B}
    → ⊩ 𝜆 u ． 𝜆 v ． ⇑ 𝑝²⟨ 𝜈 u , 𝜈 v ⟩
        ∶ (𝜈 x ∶ A ⊃ 𝜈 y ∶ B ⊃ ! 𝑝⟨ 𝜈 x , 𝜈 y ⟩ ∶ 𝑝⟨ 𝜈 x , 𝜈 y ⟩ ∶ (A ∧ B))
e14 = R𝜆 (R𝜆 (R⇑ (R𝑝² (R𝜈 (S Z))
                      (R𝜈 Z))))


-- Example 2, pp. 31–32 [1]

e2 : ∀{x₃ x₂ x₁ A}
   → ⊩ 𝜆² x₃ ． ⇓² ⇑² 𝜈 x₃
       ∶ 𝜆 x₂ ． ⇓ ⇑ 𝜈 x₂
         ∶ (𝜈 x₁ ∶ A ⊃ 𝜈 x₁ ∶ A)
e2 = R𝜆² (R⇓² (R⇑² (R𝜈² Z)))

e2′ : ∀{x₃ x₂ x₁ A}
    → ⊩ 𝜆² x₃ ． 𝜈 x₃
        ∶ 𝜆 x₂ ． 𝜈 x₂
          ∶ (𝜈 x₁ ∶ A ⊃ 𝜈 x₁ ∶ A)
e2′ = R𝜆² (R𝜈² Z)


-- --------------------------------------------------------------------------

-- Weakening

data _≲_ : ∀{m m′} → Cx m → Cx m′ → Set where
  base : ∅ ≲ ∅

  keep : ∀{A m m′} {Γ : Cx m} {Γ′ : Cx m′}
       → Γ ≲ Γ′
       → (Γ , A) ≲ (Γ′ , A)

  drop : ∀{A m m′} {Γ : Cx m} {Γ′ : Cx m′}
       → Γ ≲ Γ′
       → Γ ≲ (Γ′ , A)


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
wk⊢ P (R𝜈ⁿ  {𝐱 = 𝐱} i)         = R𝜈ⁿ  {𝐱 = 𝐱} (wk∈ P i)
wk⊢ P (R𝜆ⁿ  {𝐱 = 𝐱} {𝐭} D)     = R𝜆ⁿ  {𝐱 = 𝐱} {𝐭} (wk⊢ (keep P) D)
wk⊢ P (R∘ⁿ  {𝐭 = 𝐭} {𝐬} Dₜ Dₛ) = R∘ⁿ  {𝐭 = 𝐭} {𝐬} (wk⊢ P Dₜ) (wk⊢ P Dₛ)
wk⊢ P (R𝑝ⁿ  {𝐭 = 𝐭} {𝐬} Dₜ Dₛ) = R𝑝ⁿ  {𝐭 = 𝐭} {𝐬} (wk⊢ P Dₜ) (wk⊢ P Dₛ)
wk⊢ P (R𝜋₀ⁿ {𝐭 = 𝐭} D)         = R𝜋₀ⁿ {𝐭 = 𝐭} (wk⊢ P D)
wk⊢ P (R𝜋₁ⁿ {𝐭 = 𝐭} D)         = R𝜋₁ⁿ {𝐭 = 𝐭} (wk⊢ P D)
wk⊢ P (R⇑ⁿ  {𝐭 = 𝐭} D)         = R⇑ⁿ  {𝐭 = 𝐭} (wk⊢ P D)
wk⊢ P (R⇓ⁿ  {𝐭 = 𝐭} D)         = R⇓ⁿ  {𝐭 = 𝐭} (wk⊢ P D)


-- --------------------------------------------------------------------------

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
cn⊢ P (R𝜈ⁿ  {𝐱 = 𝐱} i)         = R𝜈ⁿ  {𝐱 = 𝐱} (cn∈ P i)
cn⊢ P (R𝜆ⁿ  {𝐱 = 𝐱} {𝐭} D)     = R𝜆ⁿ  {𝐱 = 𝐱} {𝐭} (cn⊢ (once P) D)
cn⊢ P (R∘ⁿ  {𝐭 = 𝐭} {𝐬} Dₜ Dₛ) = R∘ⁿ  {𝐭 = 𝐭} {𝐬} (cn⊢ P Dₜ) (cn⊢ P Dₛ)
cn⊢ P (R𝑝ⁿ  {𝐭 = 𝐭} {𝐬} Dₜ Dₛ) = R𝑝ⁿ  {𝐭 = 𝐭} {𝐬} (cn⊢ P Dₜ) (cn⊢ P Dₛ)
cn⊢ P (R𝜋₀ⁿ {𝐭 = 𝐭} D)         = R𝜋₀ⁿ {𝐭 = 𝐭} (cn⊢ P D)
cn⊢ P (R𝜋₁ⁿ {𝐭 = 𝐭} D)         = R𝜋₁ⁿ {𝐭 = 𝐭} (cn⊢ P D)
cn⊢ P (R⇑ⁿ  {𝐭 = 𝐭} D)         = R⇑ⁿ  {𝐭 = 𝐭} (cn⊢ P D)
cn⊢ P (R⇓ⁿ  {𝐭 = 𝐭} D)         = R⇓ⁿ  {𝐭 = 𝐭} (cn⊢ P D)


-- --------------------------------------------------------------------------

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
ex⊢ P (R𝜈ⁿ  {𝐱 = 𝐱} i)         = R𝜈ⁿ  {𝐱 = 𝐱} (ex∈ P i)
ex⊢ P (R𝜆ⁿ  {𝐱 = 𝐱} {𝐭} D)     = R𝜆ⁿ  {𝐱 = 𝐱} {𝐭} (ex⊢ (just P) D)
ex⊢ P (R∘ⁿ  {𝐭 = 𝐭} {𝐬} Dₜ Dₛ) = R∘ⁿ  {𝐭 = 𝐭} {𝐬} (ex⊢ P Dₜ) (ex⊢ P Dₛ)
ex⊢ P (R𝑝ⁿ  {𝐭 = 𝐭} {𝐬} Dₜ Dₛ) = R𝑝ⁿ  {𝐭 = 𝐭} {𝐬} (ex⊢ P Dₜ) (ex⊢ P Dₛ)
ex⊢ P (R𝜋₀ⁿ {𝐭 = 𝐭} D)         = R𝜋₀ⁿ {𝐭 = 𝐭} (ex⊢ P D)
ex⊢ P (R𝜋₁ⁿ {𝐭 = 𝐭} D)         = R𝜋₁ⁿ {𝐭 = 𝐭} (ex⊢ P D)
ex⊢ P (R⇑ⁿ  {𝐭 = 𝐭} D)         = R⇑ⁿ  {𝐭 = 𝐭} (ex⊢ P D)
ex⊢ P (R⇓ⁿ  {𝐭 = 𝐭} D)         = R⇓ⁿ  {𝐭 = 𝐭} (ex⊢ P D)


-- --------------------------------------------------------------------------

-- Theorem 1 (Internalisation principle), p. 29 [1]

{- “Let λ∞ derive
        A₁, A₂, …, Aₘ ⊢ B.
    Then one can build a well-defined term t(x₁, x₂, …, xₘ) with fresh
    variables 𝐱 such that λ∞ also derives
        x₁ ∶ A₁, x₂ ∶ A₂, …, xₘ ∶ Aₘ ⊢ t(x₁, x₂, …, xₘ) ∶ B.” -}

postulate fresh : Var    -- XXX: Fix this!


data _⅋_~_ : ∀{m} → VVar m → Cx m → Cx m → Set where
  base : ∅ ⅋ ∅ ~ ∅

  step : ∀{x A m} {𝐱 : VVar m} {Γ Γ′ : Cx m}
       → 𝐱 ⅋ Γ ~ Γ′
       → (x ∷ 𝐱) ⅋ (Γ , A) ~ (Γ′ , 𝜈 x ∶ A)


in∈ : ∀{A m} {𝐱 : VVar m} {Γ Γ′ : Cx m}
    → 𝐱 ⅋ Γ ~ Γ′    → A ∈ Γ
    → Σ Var (λ x → 𝜈 x ∶ A ∈ Γ′)
in∈ {𝐱 = ∅}              base     ()
in∈ {𝐱 = x ∷ _} (step P) Z     = ⟨ x , Z ⟩
in∈ {𝐱 = _ ∷ 𝐱} (step P) (S i) = let ⟨ y , j ⟩ = in∈ {𝐱 = 𝐱} P i
                                 in
                                   ⟨ y , S j ⟩


in⊢ : ∀{B m} {𝐱 : VVar m} {Γ Γ′ : Cx m}
    → 𝐱 ⅋ Γ ~ Γ′    → Γ ⊢ B
    → Σ (VVar m → Tm) (λ t → Γ′ ⊢ t 𝐱 ∶ B)

in⊢ {𝐱 = 𝐱} P (R𝜈ⁿ {𝐱 = 𝐲} i)
    = let ⟨ x , j ⟩ = in∈ {𝐱 = 𝐱} P i
      in
        ⟨ (λ _ → 𝜈 x)
        , R𝜈ⁿ {𝐱 = x ∷ 𝐲} j
        ⟩

in⊢ {𝐱 = 𝐱} P (R𝜆ⁿ {n} {𝐱 = 𝐲} {𝐭} D)
    = let xₘ₊₁      = fresh
          ⟨ s , C ⟩ = in⊢ {𝐱 = xₘ₊₁ ∷ 𝐱} (step P) D
      in
        ⟨ (λ 𝐱 → 𝜆^[ suc n ] xₘ₊₁ ． s (xₘ₊₁ ∷ 𝐱))
        , R𝜆ⁿ {𝐱 = xₘ₊₁ ∷ 𝐲} {𝐭 = s (xₘ₊₁ ∷ 𝐱) ∷ 𝐭} C
        ⟩

in⊢ {𝐱 = 𝐱} P (R∘ⁿ {n} {𝐭} {𝐬} Dₜ Dₛ)
    = let ⟨ sₜ , Cₜ ⟩ = in⊢ {𝐱 = 𝐱} P Dₜ
          ⟨ sₛ , Cₛ ⟩ = in⊢ {𝐱 = 𝐱} P Dₛ
      in
        ⟨ (λ 𝐱 → sₜ 𝐱 ∘^[ suc n ] sₛ 𝐱)
        , R∘ⁿ {𝐭 = sₜ 𝐱 ∷ 𝐭} {𝐬 = sₛ 𝐱 ∷ 𝐬} Cₜ Cₛ
        ⟩

in⊢ {𝐱 = 𝐱} P (R𝑝ⁿ {n} {𝐭} {𝐬} Dₜ Dₛ)
    = let ⟨ sₜ , Cₜ ⟩ = in⊢ {𝐱 = 𝐱} P Dₜ
          ⟨ sₛ , Cₛ ⟩ = in⊢ {𝐱 = 𝐱} P Dₛ
      in
        ⟨ (λ 𝐱 → 𝑝^[ suc n ]⟨ sₜ 𝐱 , sₛ 𝐱 ⟩)
        , R𝑝ⁿ {𝐭 = sₜ 𝐱 ∷ 𝐭} {𝐬 = sₛ 𝐱 ∷ 𝐬} Cₜ Cₛ
        ⟩

in⊢ {𝐱 = 𝐱} P (R𝜋₀ⁿ {n} {𝐭} D)
    = let ⟨ s , C ⟩ = in⊢ {𝐱 = 𝐱} P D
      in
        ⟨ (λ 𝐱 → 𝜋₀^[ suc n ] s 𝐱)
        , R𝜋₀ⁿ {𝐭 = s 𝐱 ∷ 𝐭} C
        ⟩

in⊢ {𝐱 = 𝐱} P (R𝜋₁ⁿ {n} {𝐭} D)
    = let ⟨ s , C ⟩ = in⊢ {𝐱 = 𝐱} P D
      in
        ⟨ (λ 𝐱 → 𝜋₁^[ suc n ] s 𝐱)
        , R𝜋₁ⁿ {𝐭 = s 𝐱 ∷ 𝐭} C
        ⟩

in⊢ {𝐱 = 𝐱} P (R⇑ⁿ {n} {𝐭} D)
    = let ⟨ s , C ⟩ = in⊢ {𝐱 = 𝐱} P D
      in
        ⟨ (λ 𝐱 → ⇑^[ suc n ] s 𝐱)
        , R⇑ⁿ {𝐭 = s 𝐱 ∷ 𝐭} C
        ⟩

in⊢ {𝐱 = 𝐱} P (R⇓ⁿ {n} {𝐭} D)
    = let ⟨ s , C ⟩ = in⊢ {𝐱 = 𝐱} P D
      in
        ⟨ (λ 𝐱 → ⇓^[ suc n ] s 𝐱)
        , R⇓ⁿ {𝐭 = s 𝐱 ∷ 𝐭} C
        ⟩


-- --------------------------------------------------------------------------

-- Work in progress

mk≲ : ∀{m} {Γ : Cx m} → ∅ ≲ Γ
mk≲ {Γ = ∅}     = base
mk≲ {Γ = x ∷ Γ} = drop (mk≲ {Γ = Γ})


_⅋_ : ∀{m} → VVar m → Cx m → Cx m
𝐱 ⅋ Γ = zipWith _∶_ (map 𝜈_ 𝐱) Γ


mk~ : ∀{m} {𝐱 : VVar m} {Γ : Cx m} → 𝐱 ⅋ Γ ~ (𝐱 ⅋ Γ)
mk~ {𝐱 = ∅}     {Γ = ∅}     = base
mk~ {𝐱 = x ∷ 𝐱} {Γ = A ∷ Γ} = step (mk~ {𝐱 = 𝐱} {Γ = Γ})


int : ∀{B m} {𝐱 : VVar m} {Γ : Cx m}
    → Γ ⊢ B
    → Σ (VVar m → Tm) (λ t → 𝐱 ⅋ Γ ⊢ t 𝐱 ∶ B)
int D = in⊢ mk~ D


nec : ∀{B}
    → ∅ ⊢ B
    → Σ Tm (λ t → ∀{m} {Γ : Cx m} → Γ ⊢ t ∶ B)
nec D = let ⟨ s , C ⟩ = int D
        in
          ⟨ s ∅ , wk⊢ mk≲ C ⟩


eI′  : ∀{A m} {Γ : Cx m}
     → Σ Tm (λ t → ⊩ t ∶ (A ⊃ A))
eI′  = nec eI⁰

eI²′ : ∀{x A m} {Γ : Cx m}
     → Σ Tm (λ t → ⊩ t ∶ 𝜆 x ． 𝜈 x ∶ (A ⊃ A))
eI²′ = nec eI

eI³′ : ∀{u x A m} {Γ : Cx m}
     → Σ Tm (λ t → ⊩ t ∶ 𝜆² u ． 𝜈 u ∶ 𝜆 x ． 𝜈 x ∶ (A ⊃ A))
eI³′ = nec eI²


eI²″ : ∀{A m} {Γ : Cx m}
     → Σ Tm (λ t → ⊩ t ∶ 𝜆 fresh ． 𝜈 fresh ∶ (A ⊃ A))    -- XXX: Fix this!
eI²″ {Γ = Γ} = nec (proj₂ (eI′ {Γ = Γ}))

eI³″ : ∀{A m} {Γ : Cx m}
     → Σ Tm (λ t → ⊩ t ∶ 𝜆² fresh ． 𝜈 fresh ∶ 𝜆 fresh ． 𝜈 fresh ∶ (A ⊃ A))    -- XXX: Fix this!
eI³″ {Γ = Γ} = nec (proj₂ (eI²′ {Γ = Γ}))
