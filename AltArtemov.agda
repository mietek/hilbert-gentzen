{-

An implementation of the Alt-Artëmov system λ∞
==============================================

Miëtek Bak  <mietek@bak.io>


Work in progress.  Checked with Agda 2.4.2.5.

For easy editing with Emacs agda-mode, add to your .emacs file:
 '(agda-input-user-translations
   (quote
    (("N" "ℕ")
     ("not" "¬") ("imp" "⊃") ("iff" "⊃⊂") ("ent" "⊢") ("thm" "⊩")
     ("z" "𝑧") ("s" "𝑠")
     ("x" "𝐱") ("y" "𝐲") ("t" "𝐭") ("s" "𝐬") ("A" "𝐀")
     ("*n" "⋆ⁿ") (",n" ",ⁿ") (",,n" "„ⁿ")
     ("v" "𝜈") ("v2" "𝜈²") ("vn" "𝜈ⁿ")
     ("l" "𝜆") ("l2" "𝜆²") ("ln" "𝜆ⁿ") ("." "．")
     ("o2" "∘²") ("on" "∘ⁿ")
     ("p" "𝑝") ("p2" "𝑝²") ("pn" "𝑝ⁿ")
     ("1" "𝜋₀") ("12" "𝜋₀²") ("1n" "𝜋₀ⁿ")
     ("2" "𝜋₁") ("12" "𝜋₁²") ("2n" "𝜋₁ⁿ")
     ("u" "⇑") ("u2" "⇑²") ("un" "⇑ⁿ")
     ("d" "⇓") ("d2" "⇓²") ("dn" "⇓ⁿ"))))


[1]: Alt, J., Artëmov, S. (2001) Reflective λ-calculus, Proceedings of the
     2001 International Seminar on Proof Theory in Computer Science (PTCS’01),
     Lecture Notes in Computer Science, vol. 2183, pp. 22–37.
     http://dx.doi.org/10.1007/3-540-45504-3_2

-}


module AltArtemov where

open import Data.Fin using (Fin ; zero ; suc)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (Σ ; _×_) renaming (_,_ to _∙_)

infixl 9 _∘_ _∘²_ _∘^[_]_
infixr 8 𝜈_ !_ ⇓_ ⇑_ ⇓²_ ⇑²_ ⇓^[_]_ ⇑^[_]_
infixr 7 𝜆_．_ 𝜆²_．_ 𝜆^[_]_．_
infixr 6 _∶_ _∷_
infixr 5 ¬_
infixl 4 _∧_
infixr 3 _⊃_ _⊃⊂_
infixl 2 _,_
infixr 1 _∈_ _⊆_
infixr 0 _⊢_ ⊩_


-- ---------------------------------------------------------------------------

-- Generic lists

data List (X : Set) : Set where
  ∅   :                        List X
  _,_ : (L : List X) (x : X) → List X


data _∈_ {X : Set} (x : X) : List X → Set where
  𝑧 : {L : List X}
    → x ∈ L , x
    
  𝑠 : {L : List X} {y : X}
    → x ∈ L
    → x ∈ L , y


data _⊆_ {X : Set} : (L L′ : List X) → Set where
  base : ∅ ⊆ ∅
  
  keep : {x : X} {L L′ : List X}
       → L ⊆ L′
       → L , x ⊆ L′ , x
       
  drop : {x : X} {L L′ : List X}
       → L ⊆ L′
       → L ⊆ L′ , x


-- Generic vectors

data Vec (X : Set) : ℕ → Set where
  ∅   :                                   Vec X zero
  _∷_ : (x : X) {n : ℕ} → (𝒙 : Vec X n) → Vec X (suc n)


foldl : {n : ℕ} {X Y : Set}
      → (f : Y → X → Y) (y₀ : Y) (𝐱 : Vec X n) → Y
foldl {zero}  f y₀ ∅       = y₀
foldl {suc n} f y₀ (x ∷ 𝐱) = f (foldl f y₀ 𝐱) x

foldr : {n : ℕ} {X Y : Set}
      → (f : X → Y → Y) (𝐱 : Vec X n) (y₀ : Y) → Y
foldr f ∅       y₀ = y₀
foldr f (x ∷ 𝐱) y₀ = f x (foldr f 𝐱 y₀)

map# : {n : ℕ} {X Y : Set}
     → (f : ℕ → X → Y) (𝐱 : Vec X n) → Vec Y n
map# {zero}  f ∅       = ∅
map# {suc n} f (x ∷ 𝐱) = f (suc n) x ∷ map# f 𝐱

map : {n : ℕ} {X Y : Set}
    → (f : X → Y) (𝐱 : Vec X n) → Vec Y n
map f 𝐱 = map# (λ _ x → f x) 𝐱

map2# : {n : ℕ} {X Y Z : Set}
      → (f : ℕ → X → Y → Z) (𝐱 : Vec X n) (𝐲 : Vec Y n) → Vec Z n
map2# {zero}  f ∅       ∅       = ∅
map2# {suc n} f (x ∷ 𝐱) (y ∷ 𝐲) = f (suc n) x y ∷ map2# f 𝐱 𝐲

map2 : {n : ℕ} {X Y Z : Set}
     → (f : X → Y → Z) (𝐱 : Vec X n) (𝐲 : Vec Y n) → Vec Z n
map2 f 𝐱 𝐲 = map2# (λ _ x y → f x y) 𝐱 𝐲


-- ---------------------------------------------------------------------------

-- Untyped syntax

mutual

  -- Variables

  data Var : Set where    -- XXX: Variable freshness!


  -- Term constructors

  data Tm : Set where
    𝜈_         : (x : Var)                  → Tm    -- Variable
    𝜆^[_]_．_   : (n : ℕ) (x : Var) (t : Tm) → Tm    -- Abstraction
    _∘^[_]_    : (t : Tm) (n : ℕ) (s : Tm)  → Tm    -- Application
    𝑝^[_]⟨_,_⟩ : (n : ℕ) (t s : Tm)         → Tm    -- Pairing
    𝜋₀^[_]_    : (n : ℕ) (t : Tm)           → Tm    -- Left projection
    𝜋₁^[_]_    : (n : ℕ) (t : Tm)           → Tm    -- Right projection
    !_         : (t : Tm)                   → Tm    -- Proof checking
    ⇑^[_]_     : (n : ℕ) (t : Tm)           → Tm    -- Reification
    ⇓^[_]_     : (n : ℕ) (t : Tm)           → Tm    -- Reflection


  -- Type constructors

  data Ty : Set where
    ⊥   :                     Ty    -- Falsehood
    _⊃_ : (A B : Ty)        → Ty    -- Implication
    _∧_ : (A B : Ty)        → Ty    -- Conjunction
    _∶_ : (x : Tm) (A : Ty) → Ty    -- Provability


-- Additional types

⊤ : Ty                    -- Truth
⊤ = ⊥ ⊃ ⊥

¬_ : (A : Ty) → Ty        -- Negation
¬ A = A ⊃ ⊥

_⊃⊂_ : (A B : Ty) → Ty    -- Equivalence
A ⊃⊂ B = A ⊃ B ∧ B ⊃ A


-- ---------------------------------------------------------------------------

-- Typing contexts

Cx : Set
Cx = List Ty


-- Vectors

VVar : (n : ℕ) → Set
VVar n = Vec Var n

VTm : (n : ℕ) → Set
VTm n = Vec Tm n

VTy : (n : ℕ) → Set
VTy n = Vec Ty n


-- Vector notation for nesting contexts

_,ⁿ_ : {n : ℕ} → (Γ : Cx) (𝐀 : VTy n) → Cx
_,ⁿ_ Γ 𝐀 = foldl _,_ Γ 𝐀

_„ⁿ_∶_ : {n : ℕ} → (Γ : Cx) (𝐱 : VVar n) (𝐀 : VTy n) → Cx
_„ⁿ_∶_ Γ 𝐱 𝐀 = Γ ,ⁿ map2 _∶_ (map 𝜈_ 𝐱) 𝐀


-- Vector notation for nesting terms inside types

⋆ⁿ_∶_ : {n : ℕ} → (𝐭 : VTm n) (A : Ty) → Ty
⋆ⁿ 𝐭 ∶ A = foldr _∶_ 𝐭 A


-- Vector notation for nesting term constructors inside types

𝜈ⁿ_∶_ : {n : ℕ} → (𝐱 : VVar n) (A : Ty) → Ty
𝜈ⁿ 𝐱 ∶ A = ⋆ⁿ (map 𝜈_ 𝐱) ∶ A

𝜆ⁿ_．_∶_ : {n : ℕ} → (𝐱 : VVar n) (𝐭 : VTm n) (A : Ty) → Ty
𝜆ⁿ 𝐱 ． 𝐭 ∶ A = ⋆ⁿ (map2# 𝜆^[_]_．_ 𝐱 𝐭) ∶ A

_∘ⁿ_∶_ : {n : ℕ} → (𝐭 𝐬 : VTm n) (A : Ty) → Ty
𝐭 ∘ⁿ 𝐬 ∶ A = ⋆ⁿ (map2# (λ n t s → t ∘^[ n ] s) 𝐭 𝐬) ∶ A

𝑝ⁿ⟨_,_⟩∶_ : {n : ℕ} → (𝐭 𝐬 : VTm n) (A : Ty) → Ty
𝑝ⁿ⟨ 𝐭 , 𝐬 ⟩∶ A = ⋆ⁿ (map2# 𝑝^[_]⟨_,_⟩ 𝐭 𝐬) ∶ A

𝜋₀ⁿ_∶_ : {n : ℕ} → (𝐭 : VTm n) (A : Ty) → Ty
𝜋₀ⁿ 𝐭 ∶ A = ⋆ⁿ (map# 𝜋₀^[_]_ 𝐭) ∶ A

𝜋₁ⁿ_∶_ : {n : ℕ} → (𝐭 : VTm n) (A : Ty) → Ty
𝜋₁ⁿ 𝐭 ∶ A = ⋆ⁿ (map# 𝜋₁^[_]_ 𝐭) ∶ A

⇑ⁿ_∶_ : {n : ℕ} → (𝐭 : VTm n) (A : Ty) → Ty
⇑ⁿ 𝐭 ∶ A = ⋆ⁿ (map# ⇑^[_]_ 𝐭) ∶ A

⇓ⁿ_∶_ : {n : ℕ} → (𝐭 : VTm n) (A : Ty) → Ty
⇓ⁿ 𝐭 ∶ A = ⋆ⁿ (map# ⇓^[_]_ 𝐭) ∶ A


-- Typing rules

data _⊢_ (Γ : Cx) : Ty → Set where
  R𝜈ⁿ  : {n n′ : ℕ} {𝐱 : VVar n} {𝐱′ : VVar n′} {A : Ty}
       → 𝜈ⁿ 𝐱 ∶ A ∈ Γ
       → Γ ⊢ 𝜈ⁿ 𝐱′ ∶ 𝜈ⁿ 𝐱 ∶ A

  R𝜆ⁿ  : {n : ℕ} {𝐱 : VVar n} {𝐭 : VTm n} {A B : Ty}
       → Γ , 𝜈ⁿ 𝐱 ∶ A ⊢ ⋆ⁿ 𝐭 ∶ B
       → Γ ⊢ 𝜆ⁿ 𝐱 ． 𝐭 ∶ (A ⊃ B)

  R∘ⁿ  : {n : ℕ} {𝐭 𝐬 : VTm n} {A B : Ty}
       → Γ ⊢ ⋆ⁿ 𝐭 ∶ (A ⊃ B)    → Γ ⊢ ⋆ⁿ 𝐬 ∶ A
       → Γ ⊢ 𝐭 ∘ⁿ 𝐬 ∶ B

  R𝑝ⁿ  : {n : ℕ} {𝐭 𝐬 : VTm n} {A B : Ty}
       → Γ ⊢ ⋆ⁿ 𝐭 ∶ A    → Γ ⊢ ⋆ⁿ 𝐬 ∶ B
       → Γ ⊢ 𝑝ⁿ⟨ 𝐭 , 𝐬 ⟩∶ (A ∧ B)

  R𝜋₀ⁿ : {n : ℕ} {𝐭 : VTm n} {A B : Ty}
       → Γ ⊢ ⋆ⁿ 𝐭 ∶ (A ∧ B)
       → Γ ⊢ 𝜋₀ⁿ 𝐭 ∶ A

  R𝜋₁ⁿ : {n : ℕ} {𝐭 : VTm n} {A B : Ty}
       → Γ ⊢ ⋆ⁿ 𝐭 ∶ (A ∧ B)
       → Γ ⊢ 𝜋₁ⁿ 𝐭 ∶ B

  R⇑ⁿ  : {n : ℕ} {𝐭 : VTm n} {u : Tm} {A : Ty}
       → Γ ⊢ ⋆ⁿ 𝐭 ∶ (u ∶ A)
       → Γ ⊢ ⇑ⁿ 𝐭 ∶ (! u ∶ u ∶ A)

  R⇓ⁿ  : {n : ℕ} {𝐭 : VTm n} {u : Tm} {A : Ty}
       → Γ ⊢ ⋆ⁿ 𝐭 ∶ (u ∶ A)
       → Γ ⊢ ⇓ⁿ 𝐭 ∶ A


-- “As soon as we are able to establish that F is a type (…), we are entitled
--  to use variables of type F as new axioms.” (p. 27[1])

R𝜈ⁿ′ : {n : ℕ} {𝐱 : VVar n} {A : Ty} {Γ : Cx}
     → A ∈ Γ
     → Γ ⊢ 𝜈ⁿ 𝐱 ∶ A
R𝜈ⁿ′ {_} {𝐱} = R𝜈ⁿ {𝐱 = ∅} {𝐱′ = 𝐱}


-- Theorems

⊩_  : (A : Ty) → Set
⊩ A = {Γ : Cx} → Γ ⊢ A


-- ---------------------------------------------------------------------------

-- Simple notation for level 0 typing rules

R𝜈⁰ : {A : Ty} {Γ : Cx}
    → A ∈ Γ
    → Γ ⊢ A
R𝜈⁰ = R𝜈ⁿ {𝐱 = ∅} {𝐱′ = ∅}

R𝜆⁰ : {A B : Ty} {Γ : Cx}
    → Γ , A ⊢ B
    → Γ ⊢ A ⊃ B
R𝜆⁰ = R𝜆ⁿ {𝐱 = ∅} {𝐭 = ∅}

R∘⁰ : {A B : Ty} {Γ : Cx}
    → Γ ⊢ A ⊃ B    → Γ ⊢ A
    → Γ ⊢ B
R∘⁰ = R∘ⁿ {𝐭 = ∅} {𝐬 = ∅}

R𝑝⁰ : {A B : Ty} {Γ : Cx}
    → Γ ⊢ A    → Γ ⊢ B
    → Γ ⊢ A ∧ B
R𝑝⁰ = R𝑝ⁿ {𝐭 = ∅} {𝐬 = ∅}

R𝜋₀⁰ : {A B : Ty} {Γ : Cx}
     → Γ ⊢ A ∧ B
     → Γ ⊢ A
R𝜋₀⁰ = R𝜋₀ⁿ {𝐭 = ∅}

R𝜋₁⁰ : {A B : Ty} {Γ : Cx}
     → Γ ⊢ A ∧ B
     → Γ ⊢ B
R𝜋₁⁰ = R𝜋₁ⁿ {𝐭 = ∅}

R⇑⁰ : {u : Tm} {A : Ty} {Γ : Cx}
    → Γ ⊢ u ∶ A
    → Γ ⊢ ! u ∶ u ∶ A
R⇑⁰ = R⇑ⁿ {𝐭 = ∅}

R⇓⁰ : {u : Tm} {A : Ty} {Γ : Cx}
    → Γ ⊢ u ∶ A
    → Γ ⊢ A
R⇓⁰ = R⇓ⁿ {𝐭 = ∅}


-- Simple level 0 examples

exmI⁰ : {x : Var} {A : Ty}
      → ⊩ A ⊃ A
exmI⁰ = R𝜆⁰ (R𝜈⁰ 𝑧)


exmK⁰ : {x y : Var} {A B : Ty}
      → ⊩ A ⊃ B ⊃ A
exmK⁰ = R𝜆⁰ (R𝜆⁰ (R𝜈⁰ (𝑠 𝑧)))


exmS⁰ : {f g x : Var} {A B C : Ty}
      → ⊩ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
exmS⁰ = R𝜆⁰ (R𝜆⁰ (R𝜆⁰ (R∘⁰ (R∘⁰ (R𝜈⁰ (𝑠 (𝑠 𝑧)))
                                (R𝜈⁰ 𝑧))
                           (R∘⁰ (R𝜈⁰ (𝑠 𝑧))
                                (R𝜈⁰ 𝑧)))))


-- ---------------------------------------------------------------------------

-- Simple notation for level 1 terms

𝜆_．_ : (x : Var) (t : Tm) → Tm
𝜆 x ． t = 𝜆^[ 1 ] x ． t

_∘_ : (t s : Tm) → Tm
t ∘ s = t ∘^[ 1 ] s

𝑝⟨_,_⟩ : (t s : Tm) → Tm
𝑝⟨ t , s ⟩ = 𝑝^[ 1 ]⟨ t , s ⟩

𝜋₀_ : (t : Tm) → Tm
𝜋₀ t = 𝜋₀^[ 1 ] t

𝜋₁_ : (t : Tm) → Tm
𝜋₁ t = 𝜋₁^[ 1 ] t

⇑_ : (t : Tm) → Tm
⇑ t = ⇑^[ 1 ] t

⇓_ : (t : Tm) → Tm
⇓ t = ⇓^[ 1 ] t


-- Simple notation for level 1 typing rules

R𝜈 : {x : Var} {A : Ty} {Γ : Cx}
   → 𝜈 x ∶ A ∈ Γ
   → Γ ⊢ 𝜈 x ∶ A
R𝜈 {x} = R𝜈ⁿ {𝐱 = x ∷ ∅} {𝐱′ = ∅}

R𝜈′ : {x : Var} {A : Ty} {Γ : Cx}
    → A ∈ Γ
    → Γ ⊢ 𝜈 x ∶ A
R𝜈′ {x} = R𝜈ⁿ′ {𝐱 = x ∷ ∅}

R𝜆 : {x : Var} {t : Tm} {A B : Ty} {Γ : Cx}
   → Γ , 𝜈 x ∶ A ⊢ t ∶ B
   → Γ ⊢ 𝜆 x ． t ∶ (A ⊃ B)
R𝜆 {x} {t} = R𝜆ⁿ {𝐱 = x ∷ ∅} {𝐭 = t ∷ ∅}

R∘ : {t s : Tm} {A B : Ty} {Γ : Cx}
   → Γ ⊢ t ∶ (A ⊃ B)    → Γ ⊢ s ∶ A
   → Γ ⊢ t ∘ s ∶ B
R∘ {t} {s} = R∘ⁿ {𝐭 = t ∷ ∅} {𝐬 = s ∷ ∅}

R𝑝 : {t s : Tm} {A B : Ty} {Γ : Cx}
   → Γ ⊢ t ∶ A    → Γ ⊢ s ∶ B
   → Γ ⊢ 𝑝⟨ t , s ⟩ ∶ (A ∧ B)
R𝑝 {t} {s} = R𝑝ⁿ {𝐭 = t ∷ ∅} {𝐬 = s ∷ ∅}

R𝜋₀ : {t : Tm} {A B : Ty} {Γ : Cx}
    → Γ ⊢ t ∶ (A ∧ B)
    → Γ ⊢ 𝜋₀ t ∶ A
R𝜋₀ {t} = R𝜋₀ⁿ {𝐭 = t ∷ ∅}

R𝜋₁ : {t : Tm} {A B : Ty} {Γ : Cx}
    → Γ ⊢ t ∶ (A ∧ B)
    → Γ ⊢ 𝜋₁ t ∶ B
R𝜋₁ {t} = R𝜋₁ⁿ {𝐭 = t ∷ ∅}

R⇑ : {t u : Tm} {A : Ty} {Γ : Cx}
   → Γ ⊢ t ∶ u ∶ A
   → Γ ⊢ ⇑ t ∶ ! u ∶ u ∶ A
R⇑ {t} = R⇑ⁿ {𝐭 = t ∷ ∅}

R⇓ : {t u : Tm} {A : Ty} {Γ : Cx}
   → Γ ⊢ t ∶ u ∶ A
   → Γ ⊢ ⇓ t ∶ A
R⇓ {t} = R⇓ⁿ {𝐭 = t ∷ ∅}


-- Simple level 1 examples

exmI : {x : Var} {A : Ty}
     → ⊩ 𝜆 x ． 𝜈 x
         ∶ (A ⊃ A)
exmI = R𝜆 (R𝜈 𝑧)


exmK : {x y : Var} {A B : Ty}
     → ⊩ 𝜆 x ． 𝜆 y ． 𝜈 x
         ∶ (A ⊃ B ⊃ A)
exmK = R𝜆 (R𝜆 (R𝜈 (𝑠 𝑧)))


exmS : {f g x : Var} {A B C : Ty}
     → ⊩ 𝜆 f ． 𝜆 g ． 𝜆 x ． ((𝜈 f) ∘ (𝜈 x)) ∘ ((𝜈 g) ∘ (𝜈 x))
         ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
exmS = R𝜆 (R𝜆 (R𝜆 (R∘ (R∘ (R𝜈 (𝑠 (𝑠 𝑧)))
                          (R𝜈 𝑧))
                      (R∘ (R𝜈 (𝑠 𝑧))
                          (R𝜈 𝑧)))))


-- ---------------------------------------------------------------------------

-- Simple notation for level 2 terms

𝜆²_．_ : (x : Var) (t : Tm) → Tm
𝜆² x ． t = 𝜆^[ 2 ] x ． t

_∘²_ : (t s : Tm) → Tm
t ∘² s = t ∘^[ 2 ] s

𝑝²⟨_,_⟩ : (t s : Tm) → Tm
𝑝²⟨ t , s ⟩ = 𝑝^[ 2 ]⟨ t , s ⟩

𝜋₀²_ : (t : Tm) → Tm
𝜋₀² t = 𝜋₀^[ 2 ] t

𝜋₁²_ : (t : Tm) → Tm
𝜋₁² t = 𝜋₁^[ 2 ] t

⇑²_ : (t : Tm) → Tm
⇑² t = ⇑^[ 2 ] t

⇓²_ : (t : Tm) → Tm
⇓² t = ⇓^[ 2 ] t


-- Simple notation for level 2 typing rules

R𝜈² : {x₂ x₁ : Var} {A : Ty} {Γ : Cx}
    → 𝜈 x₂ ∶ 𝜈 x₁ ∶ A ∈ Γ
    → Γ ⊢ 𝜈 x₂ ∶ 𝜈 x₁ ∶ A
R𝜈² {x₂} {x₁} = R𝜈ⁿ {𝐱 = x₂ ∷ x₁ ∷ ∅} {𝐱′ = ∅}

R𝜈²′ : {x₂ x₁ : Var} {A : Ty} {Γ : Cx}
     → A ∈ Γ
     → Γ ⊢ 𝜈 x₂ ∶ 𝜈 x₁ ∶ A
R𝜈²′ {x₂} {x₁} = R𝜈ⁿ′ {𝐱 = x₂ ∷ x₁ ∷ ∅}

R𝜆² : {x₂ x₁ : Var} {t₂ t₁ : Tm} {A B : Ty} {Γ : Cx}
    → Γ , 𝜈 x₂ ∶ 𝜈 x₁ ∶ A ⊢ t₂ ∶ t₁ ∶ B
    → Γ ⊢ 𝜆² x₂ ． t₂ ∶ 𝜆 x₁ ． t₁ ∶ (A ⊃ B)
R𝜆² {x₂} {x₁} {t₂} {t₁} = R𝜆ⁿ {𝐱 = x₂ ∷ x₁ ∷ ∅} {𝐭 = t₂ ∷ t₁ ∷ ∅}

R∘² : {t₂ t₁ s₂ s₁ : Tm} {A B : Ty} {Γ : Cx}
    → Γ ⊢ t₂ ∶ t₁ ∶ (A ⊃ B)    → Γ ⊢ s₂ ∶ s₁ ∶ A
    → Γ ⊢ t₂ ∘² s₂ ∶ t₁ ∘ s₁ ∶ B
R∘² {t₂} {t₁} {s₂} {s₁} = R∘ⁿ {𝐭 = t₂ ∷ t₁ ∷ ∅} {𝐬 = s₂ ∷ s₁ ∷ ∅}

R𝑝² : {t₂ t₁ s₂ s₁ : Tm} {A B : Ty} {Γ : Cx}
    → Γ ⊢ t₂ ∶ t₁ ∶ A    → Γ ⊢ s₂ ∶ s₁ ∶ B
    → Γ ⊢ 𝑝²⟨ t₂ , s₂ ⟩ ∶ 𝑝⟨ t₁ , s₁ ⟩ ∶ (A ∧ B)
R𝑝² {t₂} {t₁} {s₂} {s₁} = R𝑝ⁿ {𝐭 = t₂ ∷ t₁ ∷ ∅} {𝐬 = s₂ ∷ s₁ ∷ ∅}

R𝜋₀² : {t₂ t₁ : Tm} {A B : Ty} {Γ : Cx}
     → Γ ⊢ t₂ ∶ t₁ ∶ (A ∧ B)
     → Γ ⊢ 𝜋₀² t₂ ∶ 𝜋₀ t₁ ∶ A
R𝜋₀² {t₂} {t₁} = R𝜋₀ⁿ {𝐭 = t₂ ∷ t₁ ∷ ∅}

R𝜋₁² : {t₂ t₁ : Tm} {A B : Ty} {Γ : Cx}
     → Γ ⊢ t₂ ∶ t₁ ∶ (A ∧ B)
     → Γ ⊢ 𝜋₁² t₂ ∶ 𝜋₁ t₁ ∶ B
R𝜋₁² {t₂} {t₁} = R𝜋₁ⁿ {𝐭 = t₂ ∷ t₁ ∷ ∅}

R⇑² : {t₂ t₁ u : Tm} {A : Ty} {Γ : Cx}
    → Γ ⊢ t₂ ∶ t₁ ∶ u ∶ A
    → Γ ⊢ ⇑² t₂ ∶ ⇑ t₁ ∶ ! u ∶ u ∶ A
R⇑² {t₂} {t₁} = R⇑ⁿ {𝐭 = t₂ ∷ t₁ ∷ ∅}

R⇓² : {t₂ t₁ u : Tm} {A : Ty} {Γ : Cx}
    → Γ ⊢ t₂ ∶ t₁ ∶ u ∶ A
    → Γ ⊢ ⇓² t₂ ∶ ⇓ t₁ ∶ A
R⇓² {t₂} {t₁} = R⇓ⁿ {𝐭 = t₂ ∷ t₁ ∷ ∅}


-- Simple level 2 examples

eI² : {u x : Var} {A : Ty}
    → ⊩ 𝜆² u ． 𝜈 u
        ∶ 𝜆 x ． 𝜈 x
          ∶ (A ⊃ A)
eI² = R𝜆² (R𝜈² 𝑧)


eK² : {u x v y : Var} {A B : Ty}
    → ⊩ 𝜆² u ． 𝜆² v ． 𝜈 u
        ∶ 𝜆 x ． 𝜆 y ． 𝜈 x
          ∶ (A ⊃ B ⊃ A)
eK² = R𝜆² (R𝜆² (R𝜈² (𝑠 𝑧)))


eS² : {f g x : Var} {A B C : Ty}
    → ⊩ 𝜆² f ． 𝜆² g ． 𝜆² x ． ((𝜈 f) ∘² (𝜈 x)) ∘² ((𝜈 g) ∘² (𝜈 x))
        ∶ 𝜆 f ． 𝜆 g ． 𝜆 x ． ((𝜈 f) ∘ (𝜈 x)) ∘ ((𝜈 g) ∘ (𝜈 x))
          ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
eS² = R𝜆² (R𝜆² (R𝜆² (R∘² (R∘² (R𝜈² (𝑠 (𝑠 𝑧)))
                              (R𝜈² 𝑧))
                         (R∘² (R𝜈² (𝑠 𝑧))
                              (R𝜈² 𝑧)))))


-- ---------------------------------------------------------------------------

-- Example 1 (p. 28[1])

e1a : {x y : Var} {A : Ty}
    → ⊩ 𝜆 y ． ⇓ 𝜈 y
        ∶ (𝜈 x ∶ A ⊃ A)
e1a = R𝜆 (R⇓ (R𝜈 𝑧))

e1b : {x y : Var} {A : Ty}
    → ⊩ 𝜆 y ． ⇑ 𝜈 y
        ∶ (𝜈 x ∶ A ⊃ ! 𝜈 x ∶ 𝜈 x ∶ A)
e1b = R𝜆 (R⇑ (R𝜈 𝑧))


e1c : {u x v y : Var} {A B : Ty}
    → ⊩ 𝜆² u ． 𝜆² v ． 𝑝²⟨ 𝜈 u , 𝜈 v ⟩
        ∶ 𝜆 x ． 𝜆 y ． 𝑝⟨ 𝜈 x , 𝜈 y ⟩
          ∶ (A ⊃ B ⊃ A ∧ B)
e1c = R𝜆² (R𝜆² (R𝑝² (R𝜈² (𝑠 𝑧))
                    (R𝜈² 𝑧)))

e1d : {u x v y : Var} {A B : Ty}
    → ⊩ 𝜆 u ． 𝜆 v ． ⇑ 𝑝²⟨ 𝜈 u , 𝜈 v ⟩
        ∶ (𝜈 x ∶ A ⊃ 𝜈 y ∶ B ⊃ ! 𝑝⟨ 𝜈 x , 𝜈 y ⟩ ∶ 𝑝⟨ 𝜈 x , 𝜈 y ⟩ ∶ (A ∧ B))
e1d = R𝜆 (R𝜆 (R⇑ (R𝑝² (R𝜈 (𝑠 𝑧))
                      (R𝜈 𝑧))))


-- Example 2 (pp. 31–32[1])

e2a : {x₃ x₂ x₁ : Var} {A : Ty}
    → ⊩ 𝜆² x₃ ． ⇓² ⇑² 𝜈 x₃
        ∶ 𝜆 x₂ ． ⇓ ⇑ 𝜈 x₂
          ∶ (𝜈 x₁ ∶ A ⊃ 𝜈 x₁ ∶ A)
e2a = R𝜆² (R⇓² (R⇑² (R𝜈² 𝑧)))

e2b : {x₃ x₂ x₁ : Var} {A : Ty}
    → ⊩ 𝜆² x₃ ． 𝜈 x₃
        ∶ 𝜆 x₂ ． 𝜈 x₂
          ∶ (𝜈 x₁ ∶ A ⊃ 𝜈 x₁ ∶ A)
e2b = R𝜆² (R𝜈² 𝑧)


-- ---------------------------------------------------------------------------

-- Generalised weakening principle

weak∈ : {Γ Γ′ : Cx} {A : Ty}
      → Γ ⊆ Γ′    → A ∈ Γ
      → A ∈ Γ′
weak∈ (keep Γ⊆Γ′) 𝑧     = 𝑧
weak∈ (keep Γ⊆Γ′) (𝑠 i) = 𝑠 (weak∈ Γ⊆Γ′ i)
weak∈ (drop Γ⊆Γ′) i     = 𝑠 (weak∈ Γ⊆Γ′ i)


weak⊢ : {Γ Γ′ : Cx} {A : Ty}
      → Γ ⊆ Γ′    → Γ ⊢ A
      → Γ′ ⊢ A
weak⊢ Γ⊆Γ′ (R𝜈ⁿ  {_} {_} {𝐱} {𝐱′} i)    = R𝜈ⁿ  {𝐱 = 𝐱} {𝐱′ = 𝐱′} (weak∈ Γ⊆Γ′ i)
weak⊢ Γ⊆Γ′ (R𝜆ⁿ  {_} {𝐱} {𝐭} D)     = R𝜆ⁿ  {𝐱 = 𝐱} {𝐭 = 𝐭} (weak⊢ (keep Γ⊆Γ′) D)
weak⊢ Γ⊆Γ′ (R∘ⁿ  {_} {𝐭} {𝐬} Dₜ Dₛ) = R∘ⁿ  {𝐭 = 𝐭} {𝐬 = 𝐬} (weak⊢ Γ⊆Γ′ Dₜ) (weak⊢ Γ⊆Γ′ Dₛ)
weak⊢ Γ⊆Γ′ (R𝑝ⁿ  {_} {𝐭} {𝐬} Dₜ Dₛ) = R𝑝ⁿ  {𝐭 = 𝐭} {𝐬 = 𝐬} (weak⊢ Γ⊆Γ′ Dₜ) (weak⊢ Γ⊆Γ′ Dₛ)
weak⊢ Γ⊆Γ′ (R𝜋₀ⁿ {_} {𝐭} D)         = R𝜋₀ⁿ {𝐭 = 𝐭} (weak⊢ Γ⊆Γ′ D)
weak⊢ Γ⊆Γ′ (R𝜋₁ⁿ {_} {𝐭} D)         = R𝜋₁ⁿ {𝐭 = 𝐭} (weak⊢ Γ⊆Γ′ D)
weak⊢ Γ⊆Γ′ (R⇑ⁿ  {_} {𝐭} D)         = R⇑ⁿ  {𝐭 = 𝐭} (weak⊢ Γ⊆Γ′ D)
weak⊢ Γ⊆Γ′ (R⇓ⁿ  {_} {𝐭} D)         = R⇓ⁿ  {𝐭 = 𝐭} (weak⊢ Γ⊆Γ′ D)


-- ---------------------------------------------------------------------------

-- Theorem 1.  Internalisation principle

postulate
  fresh : {m : ℕ} → (𝐱 : VVar m) → Var    -- XXX: Variable freshness!

  lem1 : {m : ℕ} {𝐀 : VTy m} {𝐱 : VVar m} {A : Ty} {Γ : Cx}    -- XXX: Prove this!
      → A ∈ Γ ,ⁿ 𝐀
      → A ∈ Γ „ⁿ 𝐱 ∶ 𝐀


-- “Let λ∞ derive
--      A₁, A₂, …, Aₘ ⊢ B.
--  Then one can build a well-defined term t(x₁, x₂, …, xₘ) with fresh
--  variables 𝐱 such that λ∞ also derives
--      x₁ ∶ A₁, x₂ ∶ A₂, …, xₘ ∶ Aₘ ⊢ t(x₁, x₂, …, xₘ) ∶ B.”

thm1 : {m : ℕ} {𝐀 : VTy m} {B : Ty} {Γ : Cx}
     → Γ ,ⁿ 𝐀 ⊢ B
     → Σ ((𝐱 : VVar m) → Tm)
         (λ t → {𝐱 : VVar m} → (Γ „ⁿ 𝐱 ∶ 𝐀) ⊢ t 𝐱 ∶ B)

thm1 {_} {𝐀} (R𝜈ⁿ {n} {m′} {𝐲} {𝐲′} {A} i) =
    (λ 𝐱   → let xₘ₊₁ = fresh 𝐱
             in  𝜈 xₘ₊₁)
  ∙ (λ {𝐱} → let xₘ₊₁ = fresh 𝐱
             in R𝜈ⁿ {𝐱 = 𝐲} {𝐱′ = xₘ₊₁ ∷ 𝐲′} (lem1 {𝐀 = 𝐀} {𝐱 = 𝐱} i))

thm1 {_} {𝐀} (R𝜆ⁿ {n} {𝐲} {𝐭} {A} D) =
  let
    s ∙ E = thm1 {𝐀 = 𝜈ⁿ 𝐲 ∶ A ∷ 𝐀} D
  in
    (λ 𝐱   → let xₘ₊₁ = fresh 𝐱
             in  𝜆^[ suc n ] xₘ₊₁ ． s (xₘ₊₁ ∷ 𝐱))
  ∙ (λ {𝐱} → let xₘ₊₁ = fresh 𝐱
             in  R𝜆ⁿ {𝐱 = xₘ₊₁ ∷ 𝐲} {𝐭 = s (xₘ₊₁ ∷ 𝐱) ∷ 𝐭} E)

thm1 {_} {𝐀} (R∘ⁿ {n} {𝐭} {𝐬} Dₜ Dₛ) =
  let
    sₜ ∙ Eₜ = thm1 {𝐀 = 𝐀} Dₜ
    sₛ ∙ Eₛ = thm1 {𝐀 = 𝐀} Dₛ
  in
    (λ 𝐱   → sₜ 𝐱 ∘^[ suc n ] sₛ 𝐱)
  ∙ (λ {𝐱} → R∘ⁿ {𝐭 = sₜ 𝐱 ∷ 𝐭} {𝐬 = sₛ 𝐱 ∷ 𝐬} Eₜ Eₛ)

thm1 {_} {𝐀} (R𝑝ⁿ {n} {𝐭} {𝐬} Dₜ Dₛ) =
  let
    sₜ ∙ Eₜ = thm1 {𝐀 = 𝐀} Dₜ
    sₛ ∙ Eₛ = thm1 {𝐀 = 𝐀} Dₛ
  in
    (λ 𝐱   → 𝑝^[ suc n ]⟨ sₜ 𝐱 , sₛ 𝐱 ⟩)
  ∙ (λ {𝐱} → R𝑝ⁿ {𝐭 = sₜ 𝐱 ∷ 𝐭} {𝐬 = sₛ 𝐱 ∷ 𝐬} Eₜ Eₛ)

thm1 {_} {𝐀} (R𝜋₀ⁿ {n} {𝐭} D) =
  let
    s ∙ E = thm1 {𝐀 = 𝐀} D
  in
    (λ 𝐱   → 𝜋₀^[ suc n ] s 𝐱)
  ∙ (λ {𝐱} → R𝜋₀ⁿ {𝐭 = s 𝐱 ∷ 𝐭} E)

thm1 {_} {𝐀} (R𝜋₁ⁿ {n} {𝐭} D) =
  let
    s ∙ E = thm1 {𝐀 = 𝐀} D
  in
    (λ 𝐱   → 𝜋₁^[ suc n ] s 𝐱)
  ∙ (λ {𝐱} → R𝜋₁ⁿ {𝐭 = s 𝐱 ∷ 𝐭} E)

thm1 {_} {𝐀} (R⇑ⁿ {n} {𝐭} D) =
  let
    s ∙ E = thm1 {𝐀 = 𝐀} D
  in
    (λ 𝐱   → ⇑^[ suc n ] s 𝐱)
  ∙ (λ {𝐱} → R⇑ⁿ {𝐭 = s 𝐱 ∷ 𝐭} E)

thm1 {_} {𝐀} (R⇓ⁿ {n} {𝐭} D) =
  let
    s ∙ E = thm1 {𝐀 = 𝐀} D
  in
    (λ 𝐱   → ⇓^[ suc n ] s 𝐱)
  ∙ (λ {𝐱} → R⇓ⁿ {𝐭 = s 𝐱 ∷ 𝐭} E)
