{-

An implementation of the Alt-Artëmov system λ∞

Miëtek Bak <mietek@bak.io>

Checked with Agda 2.4.2.5

For easy editing with Emacs agda-mode, add to your .emacs file:
 '(agda-input-user-translations
   (quote 
    (("N" "ℕ")
     ("not" "¬") ("imp" "⊃") ("iff" "⊃⊂") ("ent" "⊢") ("thm" "⊩") 
     ("x" "𝒙") ("y" "𝒚") ("t" "𝒕") ("s" "𝒔") ("A" "𝑨")
     ("*n" "⋆ⁿ") (",n" ",ⁿ")
     ("v" "𝑣") ("v2" "𝑣²") ("vn" "𝑣ⁿ")
     ("l" "𝜆") ("l2" "𝜆²") ("ln" "𝜆ⁿ") ("." "．")
     ("o2" "∘²") ("on" "∘ⁿ")
     ("p" "𝑝") ("p2" "𝑝²") ("pn" "𝑝ⁿ")
     ("1" "𝜋₀") ("12" "𝜋₀²") ("1n" "𝜋₀ⁿ")
     ("2" "𝜋₁") ("12" "𝜋₁²") ("2n" "𝜋₁ⁿ")
     ("u" "⇑") ("u2" "⇑²") ("un" "⇑ⁿ")
     ("d" "⇓") ("d2" "⇓²") ("dn" "⇓ⁿ"))))

Alt, J., Artëmov, S. (2001) Reflective λ-calculus, Proceedings of the
2001 International Seminar on Proof Theory in Computer Science (PTCS’01),
Lecture Notes in Computer Science, vol. 2183, pp. 22–37.
http://dx.doi.org/10.1007/3-540-45504-3_2

-}

{-# OPTIONS --no-termination-check #-}    -- XXX: Temporary! Only for Theorem 1!

module AltArtemov where

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (Σ ; _,_ ; proj₁ ; proj₂ ; _×_)

infixl 9 _∘_ _∘²_ _∘^[_]_
infixr 8 𝑣_ !_ ⇓_ ⇑_ ⇓²_ ⇑²_ ⇓^[_]_ ⇑^[_]_ 
infixr 7 𝜆_．_ 𝜆²_．_ 𝜆^[_]_．_
infixr 6 _∶_ _∷_
infixr 5 ¬_
infixl 4 _∧_
infixr 3 _⊃_ _⊃⊂_
infixl 2 _,_
infixr 1 _∈_ _⊆_
infixr 0 _⊢_ ⊩_


------------------------------------------------------------------------------

-- Generic lists

data List (X : Set) : Set where
  ∅   :                        List X
  _,_ : (L : List X) (x : X) → List X

data _∈_ {X : Set} (x : X) : List X → Set where
  Z : {L : List X}         → x ∈ L , x
  S : {L : List X} {y : X} → x ∈ L → x ∈ L , y


-- Generic vectors

data Vec (X : Set) : ℕ → Set where
  ∅   :                                  Vec X zero
  _∷_ : (xₙ : X) {n : ℕ} (𝒙 : Vec X n) → Vec X (suc n)

foldl : {n : ℕ} {X Y : Set}
      → (f : Y → X → Y) (𝒙 : Vec X n) (y : Y) → Y
foldl f ∅        y = y
foldl f (xₙ ∷ 𝒙) y = f (foldl f 𝒙 y) xₙ

foldr : {n : ℕ} {X Y : Set}
      → (f : X → Y → Y) (𝒙 : Vec X n) (y : Y) → Y
foldr f ∅        y = y
foldr f (xₙ ∷ 𝒙) y = f xₙ (foldr f 𝒙 y)

map# : {n : ℕ} {X Y : Set}
     → (f : ℕ → X → Y) (𝒙 : Vec X n) → Vec Y n
map# {zero}  f ∅        = ∅
map# {suc n} f (xₙ ∷ 𝒙) = f (suc n) xₙ ∷ map# f 𝒙

map : {n : ℕ} {X Y : Set}
    → (f : X → Y) (𝒙 : Vec X n) → Vec Y n
map f 𝒙 = map# (λ _ x → f x) 𝒙

map2# : {n : ℕ} {X Y Z : Set}
      → (f : ℕ → X → Y → Z) (𝒙 : Vec X n) (𝒚 : Vec Y n) → Vec Z n
map2# {zero}  f ∅        ∅        = ∅
map2# {suc n} f (xₙ ∷ 𝒙) (yₙ ∷ 𝒚) = f (suc n) xₙ yₙ ∷ map2# f 𝒙 𝒚

map2 : {n : ℕ} {X Y Z : Set}
     → (f : X → Y → Z) (𝒙 : Vec X n) (𝒚 : Vec Y n) → Vec Z n
map2 f 𝒙 𝒚 = map2# (λ _ x y → f x y) 𝒙 𝒚


------------------------------------------------------------------------------

-- Untyped syntax

mutual

  -- Variables

  Var : Set
  Var = ℕ


  -- Term constructors

  data Tm : Set where
    𝑣_         : (x : Var)                  → Tm    -- Variable
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


------------------------------------------------------------------------------

-- Typing contexts

Cx : Set
Cx = List Ty


-- Vectors

VVar : ℕ → Set
VVar n = Vec Var n

VTm : ℕ → Set
VTm n = Vec Tm n

VTy : ℕ → Set
VTy n = Vec Ty n


-- Vector notation for nesting contexts

_,ⁿ_ : (Γ : Cx) {n : ℕ} (𝑨 : VTy n) → Cx
_,ⁿ_ Γ 𝑨 = foldl _,_ 𝑨 Γ

_,,ⁿ_∶_ : {n : ℕ} (Γ : Cx) (𝒙 : VVar n) (𝑨 : VTy n) → Cx
Γ ,,ⁿ ∅        ∶ ∅        = Γ
Γ ,,ⁿ (xₙ ∷ 𝒙) ∶ (Aₙ ∷ 𝑨) = (Γ ,,ⁿ 𝒙 ∶ 𝑨) , (𝑣 xₙ ∶ Aₙ)


-- Vector notation for nesting terms inside types

⋆ⁿ_∶_ : {n : ℕ} (𝒕 : VTm n) (A : Ty) → Ty
⋆ⁿ 𝒕 ∶ A = foldr _∶_ 𝒕 A


-- Vector notation for nesting term constructors inside types

𝑣ⁿ_∶_ : {n : ℕ} (𝒙 : VVar n) (A : Ty) → Ty
𝑣ⁿ 𝒙 ∶ A = ⋆ⁿ (map 𝑣_ 𝒙) ∶ A

𝜆ⁿ_．_∶_ : {n : ℕ} (𝒙 : VVar n) (𝒕 : VTm n) (A : Ty) → Ty
𝜆ⁿ 𝒙 ． 𝒕 ∶ A = ⋆ⁿ (map2# 𝜆^[_]_．_ 𝒙 𝒕) ∶ A

_∘ⁿ_∶_ : {n : ℕ} (𝒕 𝒔 : VTm n) (A : Ty) → Ty
𝒕 ∘ⁿ 𝒔 ∶ A = ⋆ⁿ (map2# (λ n t s → t ∘^[ n ] s) 𝒕 𝒔) ∶ A

𝑝ⁿ⟨_,_⟩∶_ : {n : ℕ} (𝒕 𝒔 : VTm n) (A : Ty) → Ty
𝑝ⁿ⟨ 𝒕 , 𝒔 ⟩∶ A = ⋆ⁿ (map2# 𝑝^[_]⟨_,_⟩ 𝒕 𝒔) ∶ A

𝜋₀ⁿ_∶_ : {n : ℕ} (𝒕 : VTm n) (A : Ty) → Ty
𝜋₀ⁿ 𝒕 ∶ A = ⋆ⁿ (map# 𝜋₀^[_]_ 𝒕) ∶ A

𝜋₁ⁿ_∶_ : {n : ℕ} (𝒕 : VTm n) (A : Ty) → Ty
𝜋₁ⁿ 𝒕 ∶ A = ⋆ⁿ (map# 𝜋₁^[_]_ 𝒕) ∶ A

⇑ⁿ_∶_ : {n : ℕ} (𝒕 : VTm n) (A : Ty) → Ty
⇑ⁿ 𝒕 ∶ A = ⋆ⁿ (map# ⇑^[_]_ 𝒕) ∶ A

⇓ⁿ_∶_ : {n : ℕ} (𝒕 : VTm n) (A : Ty) → Ty
⇓ⁿ 𝒕 ∶ A = ⋆ⁿ (map# ⇓^[_]_ 𝒕) ∶ A


-- Typing rules

data _⊢_ (Γ : Cx) : Ty → Set where
  R𝑣ⁿ  : {n : ℕ} {𝒙 : VVar n} {A : Ty}
       → 𝑣ⁿ 𝒙 ∶ A ∈ Γ
       → Γ ⊢ 𝑣ⁿ 𝒙 ∶ A

  R𝜆ⁿ  : {n : ℕ} {𝒙 : VVar n} {𝒕 : VTm n} {A B : Ty}
       → Γ , 𝑣ⁿ 𝒙 ∶ A ⊢ ⋆ⁿ 𝒕 ∶ B
       → Γ ⊢ 𝜆ⁿ 𝒙 ． 𝒕 ∶ (A ⊃ B)

  R∘ⁿ  : {n : ℕ} {𝒕 𝒔 : VTm n} {A B : Ty}
       → Γ ⊢ ⋆ⁿ 𝒕 ∶ (A ⊃ B)    → Γ ⊢ ⋆ⁿ 𝒔 ∶ A
       → Γ ⊢ 𝒕 ∘ⁿ 𝒔 ∶ B

  R𝑝ⁿ  : {n : ℕ} {𝒕 𝒔 : VTm n} {A B : Ty}
       → Γ ⊢ ⋆ⁿ 𝒕 ∶ A    → Γ ⊢ ⋆ⁿ 𝒔 ∶ B
       → Γ ⊢ 𝑝ⁿ⟨ 𝒕 , 𝒔 ⟩∶ (A ∧ B)

  R𝜋₀ⁿ : {n : ℕ} {𝒕 : VTm n} {A B : Ty}
       → Γ ⊢ ⋆ⁿ 𝒕 ∶ (A ∧ B)
       → Γ ⊢ 𝜋₀ⁿ 𝒕 ∶ A

  R𝜋₁ⁿ : {n : ℕ} {𝒕 : VTm n} {A B : Ty}
       → Γ ⊢ ⋆ⁿ 𝒕 ∶ (A ∧ B)
       → Γ ⊢ 𝜋₁ⁿ 𝒕 ∶ B

  R⇑ⁿ  : {n : ℕ} {𝒕 : VTm n} {u : Tm} {A : Ty}
       → Γ ⊢ ⋆ⁿ 𝒕 ∶ (u ∶ A)
       → Γ ⊢ ⇑ⁿ 𝒕 ∶ (! u ∶ u ∶ A)

  R⇓ⁿ  : {n : ℕ} {𝒕 : VTm n} {u : Tm} {A : Ty}
       → Γ ⊢ ⋆ⁿ 𝒕 ∶ (u ∶ A)
       → Γ ⊢ ⇓ⁿ 𝒕 ∶ A


-- Theorems

⊩_  : (A : Ty) → Set
⊩ A = {Γ : Cx} → Γ ⊢ A


------------------------------------------------------------------------------

-- Simple notation for level 0 typing rules

R𝑣⁰ : {A : Ty} {Γ : Cx}
    → A ∈ Γ
    → Γ ⊢ A
R𝑣⁰ = R𝑣ⁿ {𝒙 = ∅}

R𝜆⁰ : {A B : Ty} {Γ : Cx}
    → Γ , A ⊢ B
    → Γ ⊢ A ⊃ B
R𝜆⁰ = R𝜆ⁿ {𝒙 = ∅} {𝒕 = ∅}

R∘⁰ : {A B : Ty} {Γ : Cx}
    → Γ ⊢ A ⊃ B    → Γ ⊢ A
    → Γ ⊢ B
R∘⁰ = R∘ⁿ {𝒕 = ∅} {𝒔 = ∅}

R𝑝⁰ : {A B : Ty} {Γ : Cx}
    → Γ ⊢ A    → Γ ⊢ B
    → Γ ⊢ A ∧ B
R𝑝⁰ = R𝑝ⁿ {𝒕 = ∅} {𝒔 = ∅}

R𝜋₀⁰ : {A B : Ty} {Γ : Cx}
     → Γ ⊢ A ∧ B
     → Γ ⊢ A
R𝜋₀⁰ = R𝜋₀ⁿ {𝒕 = ∅}

R𝜋₁⁰ : {A B : Ty} {Γ : Cx}
     → Γ ⊢ A ∧ B
     → Γ ⊢ B
R𝜋₁⁰ = R𝜋₁ⁿ {𝒕 = ∅}

R⇑⁰ : {u : Tm} {A : Ty} {Γ : Cx}
    → Γ ⊢ u ∶ A
    → Γ ⊢ ! u ∶ u ∶ A
R⇑⁰ = R⇑ⁿ {𝒕 = ∅}

R⇓⁰ : {u : Tm} {A : Ty} {Γ : Cx}
    → Γ ⊢ u ∶ A
    → Γ ⊢ A
R⇓⁰ = R⇓ⁿ {𝒕 = ∅}


-- Simple level 0 examples

exmI⁰ : {x : Var} {A : Ty}
      → ⊩ A ⊃ A
exmI⁰ = R𝜆⁰ (R𝑣⁰ Z)


exmK⁰ : {x y : Var} {A B : Ty}
      → ⊩ A ⊃ B ⊃ A
exmK⁰ = R𝜆⁰ (R𝜆⁰ (R𝑣⁰ (S Z)))


exmS⁰ : {f g x : Var} {A B C : Ty}
      → ⊩ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
exmS⁰ = R𝜆⁰ (R𝜆⁰ (R𝜆⁰ (R∘⁰ (R∘⁰ (R𝑣⁰ (S (S Z)))
                                (R𝑣⁰ Z))
                           (R∘⁰ (R𝑣⁰ (S Z))
                                (R𝑣⁰ Z)))))


------------------------------------------------------------------------------

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

R𝑣 : {x : Var} {A : Ty} {Γ : Cx}
   → 𝑣 x ∶ A ∈ Γ
   → Γ ⊢ 𝑣 x ∶ A
R𝑣 {x} = R𝑣ⁿ {𝒙 = x ∷ ∅}

R𝜆 : {x : Var} {t : Tm} {A B : Ty} {Γ : Cx}
   → Γ , (𝑣 x ∶ A) ⊢ t ∶ B
   → Γ ⊢ 𝜆 x ． t ∶ (A ⊃ B)
R𝜆 {x} {t} = R𝜆ⁿ {𝒙 = x ∷ ∅} {𝒕 = t ∷ ∅}

R∘ : {t s : Tm} {A B : Ty} {Γ : Cx}
   → Γ ⊢ t ∶ (A ⊃ B)    → Γ ⊢ s ∶ A
   → Γ ⊢ t ∘ s ∶ B
R∘ {t} {s} = R∘ⁿ {𝒕 = t ∷ ∅} {𝒔 = s ∷ ∅}

R𝑝 : {t s : Tm} {A B : Ty} {Γ : Cx}
   → Γ ⊢ t ∶ A    → Γ ⊢ s ∶ B
   → Γ ⊢ 𝑝⟨ t , s ⟩ ∶ (A ∧ B)
R𝑝 {t} {s} = R𝑝ⁿ {𝒕 = t ∷ ∅} {𝒔 = s ∷ ∅}

R𝜋₀ : {t : Tm} {A B : Ty} {Γ : Cx}
    → Γ ⊢ t ∶ (A ∧ B)
    → Γ ⊢ 𝜋₀ t ∶ A
R𝜋₀ {t} = R𝜋₀ⁿ {𝒕 = t ∷ ∅}

R𝜋₁ : {t : Tm} {A B : Ty} {Γ : Cx}
    → Γ ⊢ t ∶ (A ∧ B)
    → Γ ⊢ 𝜋₁ t ∶ B
R𝜋₁ {t} = R𝜋₁ⁿ {𝒕 = t ∷ ∅}

R⇑ : {t u : Tm} {A : Ty} {Γ : Cx}
   → Γ ⊢ t ∶ u ∶ A
   → Γ ⊢ ⇑ t ∶ ! u ∶ u ∶ A
R⇑ {t} = R⇑ⁿ {𝒕 = t ∷ ∅}

R⇓ : {t u : Tm} {A : Ty} {Γ : Cx}
   → Γ ⊢ t ∶ u ∶ A
   → Γ ⊢ ⇓ t ∶ A
R⇓ {t} = R⇓ⁿ {𝒕 = t ∷ ∅}


-- Simple level 1 examples

exmI : {x : Var} {A : Ty}
     → ⊩ 𝜆 x ． 𝑣 x
         ∶ (A ⊃ A)
exmI = R𝜆 (R𝑣 Z)


exmK : {x y : Var} {A B : Ty}
     → ⊩ 𝜆 x ． 𝜆 y ． 𝑣 x
         ∶ (A ⊃ B ⊃ A)
exmK = R𝜆 (R𝜆 (R𝑣 (S Z)))


exmS : {f g x : Var} {A B C : Ty}
     → ⊩ 𝜆 f ． 𝜆 g ． 𝜆 x ． ((𝑣 f) ∘ (𝑣 x)) ∘ ((𝑣 g) ∘ (𝑣 x))
         ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
exmS = R𝜆 (R𝜆 (R𝜆 (R∘ (R∘ (R𝑣 (S (S Z)))
                          (R𝑣 Z))
                      (R∘ (R𝑣 (S Z))
                          (R𝑣 Z)))))


------------------------------------------------------------------------------

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

R𝑣² : {x₂ x₁ : Var} {A : Ty} {Γ : Cx}
    → 𝑣 x₂ ∶ 𝑣 x₁ ∶ A ∈ Γ
    → Γ ⊢ 𝑣 x₂ ∶ 𝑣 x₁ ∶ A
R𝑣² {x₂} {x₁} = R𝑣ⁿ {𝒙 = x₂ ∷ x₁ ∷ ∅}

R𝜆² : {x₂ x₁ : Var} {t₂ t₁ : Tm} {A B : Ty} {Γ : Cx}
    → Γ , (𝑣 x₂ ∶ 𝑣 x₁ ∶ A) ⊢ t₂ ∶ t₁ ∶ B
    → Γ ⊢ 𝜆² x₂ ． t₂ ∶ 𝜆 x₁ ． t₁ ∶ (A ⊃ B)
R𝜆² {x₂} {x₁} {t₂} {t₁} = R𝜆ⁿ {𝒙 = x₂ ∷ x₁ ∷ ∅} {𝒕 = t₂ ∷ t₁ ∷ ∅}

R∘² : {t₂ t₁ s₂ s₁ : Tm} {A B : Ty} {Γ : Cx}
    → Γ ⊢ t₂ ∶ t₁ ∶ (A ⊃ B)    → Γ ⊢ s₂ ∶ s₁ ∶ A
    → Γ ⊢ t₂ ∘² s₂ ∶ t₁ ∘ s₁ ∶ B
R∘² {t₂} {t₁} {s₂} {s₁} = R∘ⁿ {𝒕 = t₂ ∷ t₁ ∷ ∅} {𝒔 = s₂ ∷ s₁ ∷ ∅}

R𝑝² : {t₂ t₁ s₂ s₁ : Tm} {A B : Ty} {Γ : Cx}
    → Γ ⊢ t₂ ∶ t₁ ∶ A    → Γ ⊢ s₂ ∶ s₁ ∶ B
    → Γ ⊢ 𝑝²⟨ t₂ , s₂ ⟩ ∶ 𝑝⟨ t₁ , s₁ ⟩ ∶ (A ∧ B)
R𝑝² {t₂} {t₁} {s₂} {s₁} = R𝑝ⁿ {𝒕 = t₂ ∷ t₁ ∷ ∅} {𝒔 = s₂ ∷ s₁ ∷ ∅}

R𝜋₀² : {t₂ t₁ : Tm} {A B : Ty} {Γ : Cx}
     → Γ ⊢ t₂ ∶ t₁ ∶ (A ∧ B)
     → Γ ⊢ 𝜋₀² t₂ ∶ 𝜋₀ t₁ ∶ A
R𝜋₀² {t₂} {t₁} = R𝜋₀ⁿ {𝒕 = t₂ ∷ t₁ ∷ ∅}

R𝜋₁² : {t₂ t₁ : Tm} {A B : Ty} {Γ : Cx}
     → Γ ⊢ t₂ ∶ t₁ ∶ (A ∧ B)
     → Γ ⊢ 𝜋₁² t₂ ∶ 𝜋₁ t₁ ∶ B
R𝜋₁² {t₂} {t₁} = R𝜋₁ⁿ {𝒕 = t₂ ∷ t₁ ∷ ∅}

R⇑² : {t₂ t₁ u : Tm} {A : Ty} {Γ : Cx}
    → Γ ⊢ t₂ ∶ t₁ ∶ u ∶ A
    → Γ ⊢ ⇑² t₂ ∶ ⇑ t₁ ∶ ! u ∶ u ∶ A
R⇑² {t₂} {t₁} = R⇑ⁿ {𝒕 = t₂ ∷ t₁ ∷ ∅}

R⇓² : {t₂ t₁ u : Tm} {A : Ty} {Γ : Cx}
    → Γ ⊢ t₂ ∶ t₁ ∶ u ∶ A
    → Γ ⊢ ⇓² t₂ ∶ ⇓ t₁ ∶ A
R⇓² {t₂} {t₁} = R⇓ⁿ {𝒕 = t₂ ∷ t₁ ∷ ∅}


-- Simple level 2 examples

exmI² : {u x : Var} {A : Ty}
      → ⊩ 𝜆² u ． 𝑣 u
          ∶ 𝜆 x ． 𝑣 x
            ∶ (A ⊃ A)
exmI² = R𝜆² (R𝑣² Z)


exmK² : {u x v y : Var} {A B : Ty}
      → ⊩ 𝜆² u ． 𝜆² v ． 𝑣 u
          ∶ 𝜆 x ． 𝜆 y ． 𝑣 x
            ∶ (A ⊃ B ⊃ A)
exmK² = R𝜆² (R𝜆² (R𝑣² (S Z)))


exmS² : {f g x : Var} {A B C : Ty}
      → ⊩ 𝜆² f ． 𝜆² g ． 𝜆² x ． ((𝑣 f) ∘² (𝑣 x)) ∘² ((𝑣 g) ∘² (𝑣 x))
          ∶ 𝜆 f ． 𝜆 g ． 𝜆 x ． ((𝑣 f) ∘ (𝑣 x)) ∘ ((𝑣 g) ∘ (𝑣 x))
            ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
exmS² = R𝜆² (R𝜆² (R𝜆² (R∘² (R∘² (R𝑣² (S (S Z)))
                                (R𝑣² Z))
                           (R∘² (R𝑣² (S Z))
                                (R𝑣² Z)))))


------------------------------------------------------------------------------

-- Example 1 (p. 28[1])

exm1a : {x y : Var} {A : Ty}
      → ⊩ 𝜆 y ． ⇓ 𝑣 y
          ∶ (𝑣 x ∶ A ⊃ A)
exm1a = R𝜆 (R⇓ (R𝑣 Z))

exm1b : {x y : Var} {A : Ty}
      → ⊩ 𝜆 y ． ⇑ 𝑣 y
          ∶ (𝑣 x ∶ A ⊃ ! 𝑣 x ∶ 𝑣 x ∶ A)
exm1b = R𝜆 (R⇑ (R𝑣 Z))

exm1c : {u x v y : Var} {A B : Ty}
      → ⊩ 𝜆² u ． 𝜆² v ． 𝑝²⟨ 𝑣 u , 𝑣 v ⟩
          ∶ 𝜆 x ． 𝜆 y ． 𝑝⟨ 𝑣 x , 𝑣 y ⟩
            ∶ (A ⊃ B ⊃ A ∧ B)
exm1c = R𝜆² (R𝜆² (R𝑝² (R𝑣² (S Z))
                      (R𝑣² Z)))

exm1d : {u x v y : Var} {A B : Ty}
      → ⊩ 𝜆 u ． 𝜆 v ． ⇑ 𝑝²⟨ 𝑣 u , 𝑣 v ⟩
          ∶ (𝑣 x ∶ A ⊃ 𝑣 y ∶ B ⊃ ! 𝑝⟨ 𝑣 x , 𝑣 y ⟩ ∶ 𝑝⟨ 𝑣 x , 𝑣 y ⟩ ∶ (A ∧ B))
exm1d = R𝜆 (R𝜆 (R⇑ (R𝑝² (R𝑣 (S Z))
                        (R𝑣 Z))))


-- Example 2 (pp. 31–32[1])

exm2a : {x₃ x₂ x₁ : Var} {A : Ty}
      → ⊩ 𝜆² x₃ ． ⇓² ⇑² 𝑣 x₃
          ∶ 𝜆 x₂ ． ⇓ ⇑ 𝑣 x₂
            ∶ (𝑣 x₁ ∶ A ⊃ 𝑣 x₁ ∶ A)
exm2a = R𝜆² (R⇓² (R⇑² (R𝑣² Z)))

exm2b : {x₃ x₂ x₁ : Var} {A : Ty}
      → ⊩ 𝜆² x₃ ． 𝑣 x₃
          ∶ 𝜆 x₂ ． 𝑣 x₂
            ∶ (𝑣 x₁ ∶ A ⊃ 𝑣 x₁ ∶ A)
exm2b = R𝜆² (R𝑣² Z)


------------------------------------------------------------------------------

-- Generalised weakening principle

data _⊆_ : (Γ Γ′ : Cx) → Set where
  base :                                     ∅ ⊆ ∅
  keep : {Γ Γ′ : Cx} {A : Ty} → Γ ⊆ Γ′ → Γ , A ⊆ Γ′ , A
  drop : {Γ Γ′ : Cx} {A : Ty} → Γ ⊆ Γ′ →     Γ ⊆ Γ′ , A

weak∈ : {Γ Γ′ : Cx} {A : Ty} → Γ ⊆ Γ′ → A ∈ Γ → A ∈ Γ′
weak∈ (keep Γ⊆Γ′) Z     = Z
weak∈ (keep Γ⊆Γ′) (S i) = S (weak∈ Γ⊆Γ′ i)
weak∈ (drop Γ⊆Γ′) i     = S (weak∈ Γ⊆Γ′ i)

weak⊢ : {Γ Γ′ : Cx} {A : Ty} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A
weak⊢ Γ⊆Γ′ (R𝑣ⁿ  {_} {𝒙} i)         = R𝑣ⁿ  {𝒙 = 𝒙} (weak∈ Γ⊆Γ′ i)
weak⊢ Γ⊆Γ′ (R𝜆ⁿ  {_} {𝒙} {𝒕} d)     = R𝜆ⁿ  {𝒙 = 𝒙} {𝒕 = 𝒕} (weak⊢ (keep Γ⊆Γ′) d)
weak⊢ Γ⊆Γ′ (R∘ⁿ  {_} {𝒕} {𝒔} dₜ dₛ) = R∘ⁿ  {𝒕 = 𝒕} {𝒔 = 𝒔} (weak⊢ Γ⊆Γ′ dₜ) (weak⊢ Γ⊆Γ′ dₛ)
weak⊢ Γ⊆Γ′ (R𝑝ⁿ  {_} {𝒕} {𝒔} dₜ dₛ) = R𝑝ⁿ  {𝒕 = 𝒕} {𝒔 = 𝒔} (weak⊢ Γ⊆Γ′ dₜ) (weak⊢ Γ⊆Γ′ dₛ)
weak⊢ Γ⊆Γ′ (R𝜋₀ⁿ {_} {𝒕} d)         = R𝜋₀ⁿ {𝒕 = 𝒕} (weak⊢ Γ⊆Γ′ d)
weak⊢ Γ⊆Γ′ (R𝜋₁ⁿ {_} {𝒕} d)         = R𝜋₁ⁿ {𝒕 = 𝒕} (weak⊢ Γ⊆Γ′ d)
weak⊢ Γ⊆Γ′ (R⇑ⁿ  {_} {𝒕} d)         = R⇑ⁿ  {𝒕 = 𝒕} (weak⊢ Γ⊆Γ′ d)
weak⊢ Γ⊆Γ′ (R⇓ⁿ  {_} {𝒕} d)         = R⇓ⁿ  {𝒕 = 𝒕} (weak⊢ Γ⊆Γ′ d)


------------------------------------------------------------------------------

-- Theorem 1.  Internalisation principle

-- "Note that the set of axioms is thus also defined inductively according
-- to λ∞: as soon as we are able to establish that F is a type we are
-- entitled to use variables of type F as new axioms."

postulate
  lem1 : {x : Var} {m : ℕ} {𝒙 : VVar m} {A B : Ty} {Γ : Cx}    -- XXX: How to prove this?
       → Γ ,     𝑣ⁿ 𝒙 ∶ A ⊢ B
       → Γ , 𝑣ⁿ x ∷ 𝒙 ∶ A ⊢ B

  lem2 : {n m : ℕ} {𝑨 : VTy m} {𝒚 : VVar n} {A B : Ty} {Γ : Cx}    -- XXX: How to prove this?
       → (Γ ,ⁿ 𝑨) , 𝑣ⁿ 𝒚 ∶ A ⊢ B
       → Γ ,ⁿ (𝑣ⁿ 𝒚 ∶ A ∷ 𝑨) ⊢ B

fresh : {m : ℕ} {𝒙 : VVar m} → Var
fresh {m} = suc m    -- XXX: Prove freshness!


-- "Let λ∞ derive
--   A₁, A₂, …, Aₘ ⊢ B.
-- Then one can build a well-defined term t(x₁, x₂, …, xₘ) with fresh
-- variables 𝒙 such that λ∞ also derives
--   x₁ ∶ A₁, x₂ ∶ A₂, …, xₘ ∶ Aₘ ⊢ t(x₁, x₂, …, xₘ) ∶ B."

{-
thm1 : {m : ℕ} {𝑨 : VTy m} {B : Ty} {Γ : Cx}
     → Γ ,ⁿ 𝑨 ⊢ B
     → Σ (VVar m → Tm) (λ t → {𝒙 : VVar m} → (Γ ,,ⁿ 𝒙 ∶ 𝑨) ⊢ t 𝒙 ∶ B)

thm1 {_} {𝑨} (R𝑣ⁿ {_} {𝒚} D) = {!!}    -- XXX: How to prove this?

thm1 {_} {𝑨} (R𝜆ⁿ {n} {𝒚} {𝒕} {A} D) =
  let s , E = thm1 {𝑨 = 𝑣ⁿ 𝒚 ∶ A ∷ 𝑨} (lem2 {𝑨 = 𝑨} {𝒚 = 𝒚} D)    -- XXX: Does this terminate?
  in  (λ 𝒙 → let xₘ₊₁ = fresh {𝒙 = 𝒙}
             in  𝜆^[ suc n ] xₘ₊₁ ． s (xₘ₊₁ ∷ 𝒙))
    , (λ {𝒙} → let xₘ₊₁ = fresh {𝒙 = 𝒙}
               in  R𝜆ⁿ {𝒙 = xₘ₊₁ ∷ 𝒚} {𝒕 = s (xₘ₊₁ ∷ 𝒙) ∷ 𝒕} E)

thm1 {_} {𝑨} (R∘ⁿ {n} {𝒕} {𝒔} Dₜ Dₛ) =
  let sₜ , Eₜ = thm1 {𝑨 = 𝑨} Dₜ
      sₛ , Eₛ = thm1 {𝑨 = 𝑨} Dₛ
  in  (λ 𝒙 → sₜ 𝒙 ∘^[ suc n ] sₛ 𝒙)
    , (λ {𝒙} → R∘ⁿ {𝒕 = sₜ 𝒙 ∷ 𝒕} {𝒔 = sₛ 𝒙 ∷ 𝒔} Eₜ Eₛ)
    
thm1 {_} {𝑨} (R𝑝ⁿ {n} {𝒕} {𝒔} Dₜ Dₛ) =
  let sₜ , Eₜ = thm1 {𝑨 = 𝑨} Dₜ
      sₛ , Eₛ = thm1 {𝑨 = 𝑨} Dₛ
  in  (λ 𝒙 → 𝑝^[ suc n ]⟨ sₜ 𝒙 , sₛ 𝒙 ⟩)
    , (λ {𝒙} → R𝑝ⁿ {𝒕 = sₜ 𝒙 ∷ 𝒕} {𝒔 = sₛ 𝒙 ∷ 𝒔} Eₜ Eₛ)
    
thm1 {_} {𝑨} (R𝜋₀ⁿ {n} {𝒕} D) =
  let s , E = thm1 {𝑨 = 𝑨} D
  in  (λ 𝒙 → 𝜋₀^[ suc n ] s 𝒙)
    , (λ {𝒙} → R𝜋₀ⁿ {𝒕 = s 𝒙 ∷ 𝒕} E)
    
thm1 {_} {𝑨} (R𝜋₁ⁿ {n} {𝒕} D) =
  let s , E = thm1 {𝑨 = 𝑨} D
  in  (λ 𝒙 → 𝜋₁^[ suc n ] s 𝒙)
    , (λ {𝒙} → R𝜋₁ⁿ {𝒕 = s 𝒙 ∷ 𝒕} E)
    
thm1 {_} {𝑨} (R⇑ⁿ {n} {𝒕} D) =
  let s , E = thm1 {𝑨 = 𝑨} D
  in  (λ 𝒙 → ⇑^[ suc n ] s 𝒙)
    , (λ {𝒙} → R⇑ⁿ {𝒕 = s 𝒙 ∷ 𝒕} E)
    
thm1 {_} {𝑨} (R⇓ⁿ {n} {𝒕} D) =
  let s , E = thm1 {𝑨 = 𝑨} D
  in  (λ 𝒙 → ⇓^[ suc n ] s 𝒙)
    , (λ {𝒙} → R⇓ⁿ {𝒕 = s 𝒙 ∷ 𝒕} E)
-}
