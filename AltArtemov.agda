{-

A partial implementation of the Alt-Artëmov system λ∞[1].

Miëtek Bak <mietek@bak.io>

Thanks to Darryl McAdams and Paolo Giarrusso for comments and discussion.

For easy editing with Emacs agda-mode, add to your .emacs file:
 '(agda-input-user-translations
   (quote
    (("imp" "⊃") ("iff" "⊃⊂") ("not" "¬") ("ent" "⊢") ("thm" "⊩") ("N" "ℕ")
     ("s" "𝒔") ("t" "𝒕") ("x" "𝒙") ("y" "𝒚")
     ("v" "𝑣") ("ts" "𝑡𝑠") ("vs" "𝑣𝑠")
     ("l" "𝜆") ("l1" "𝜆") ("l2" "𝜆²") ("ln" "𝜆ⁿ") ("." "．")
     ("o" "∘") ("o1" "∘") ("o2" "∘²") ("on" "∘ⁿ")
     ("p" "𝗽") ("p1" "𝗽") ("p2" "𝗽²") ("pn" "𝗽ⁿ")
     ("pi0" "𝛑₀") ("pi01" "𝛑₀") ("pi02" "𝛑₀²") ("pi0n" "𝛑₀ⁿ")
     ("pi1" "𝛑₁") ("pi11" "𝛑₁") ("pi12" "𝛑₁²") ("pi1n" "𝛑₁ⁿ")
     ("u" "⇑") ("u1" "⇑") ("u2" "⇑²") ("un" "⇑ⁿ")
     ("d" "⇓") ("d1" "⇓") ("d2" "⇓²") ("dn" "⇓ⁿ"))))

[1]: Alt, J., Artëmov, S. (2001) Reflective λ-calculus, Proceedings of the
     2001 International Seminar on Proof Theory in Computer Science (PTCS’01),
     Lecture Notes in Computer Science, vol. 2183, pp. 22–37.
     http://dx.doi.org/10.1007/3-540-45504-3_2

-}


module AltArtemov where

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_)

infixl 8 _∘_ _∘²_ _∘ⁿ_#_
infixr 7 ⇓_ ⇓²_ ⇓ⁿ_#_ ⇑_ ⇑²_ ⇑ⁿ_#_ !_ 𝑣_
infixr 6 𝜆_．_ 𝜆²_．_ 𝜆ⁿ_．_#_
infixr 5 ¬_ _∶_
infixl 4 _∧_
infixr 3 _⊃_ _⊃⊂_
infixl 2 _,_
infixr 1 _∈_
infixr 0 _⊢_ ⊩_


mutual

  -- Variables
  
  Var : Set
  Var = ℕ × Ty


  -- Term formation

  data Tm : Set where
    𝑣_        : (x : Var)                  → Tm    -- Variable referencing
    𝜆ⁿ_．_#_   : (x : Var) (t : Tm) (n : ℕ) → Tm    -- Implication introduction
    _∘ⁿ_#_    : (t s : Tm)         (n : ℕ) → Tm    -- Implication elimination
    𝗽ⁿ⟨_,_⟩#_ : (t s : Tm)         (n : ℕ) → Tm    -- Conjunction introduction
    𝛑₀ⁿ_#_    : (t : Tm)           (n : ℕ) → Tm    -- Left conjunction elimination
    𝛑₁ⁿ_#_    : (t : Tm)           (n : ℕ) → Tm    -- Right conjunction elimination
    !_        : (t : Tm)                   → Tm    -- Proof checking
    ⇑ⁿ_#_     : (t : Tm)           (n : ℕ) → Tm    -- Proof reification
    ⇓ⁿ_#_     : (t : Tm)           (n : ℕ) → Tm    -- Proof reflection


  -- Type formation

  data Ty : Set where
    ⊥   :                     Ty    -- Falsehood
    _⊃_ : (A B : Ty)        → Ty    -- Implication
    _∧_ : (A B : Ty)        → Ty    -- Conjunction
    _∶_ : (x : Tm) (A : Ty) → Ty    -- Explicit provability
 

-- Contexts

data Cx : Set where
  ∅   :           Cx
  _,_ : Cx → Ty → Cx


-- Context membership evidence

data _∈_ (A : Ty) : Cx → Set where
  Z : {Γ : Cx}                  → A ∈ Γ , A
  S : {Γ : Cx} {B : Ty} → A ∈ Γ → A ∈ Γ , B


-- Notation for types

⊤ : Ty                    -- Truth
⊤ = ⊥ ⊃ ⊥

¬_ : (A : Ty) → Ty        -- Negation
¬ A = A ⊃ ⊥

_⊃⊂_ : (A B : Ty) → Ty    -- Equivalence
A ⊃⊂ B = A ⊃ B ∧ B ⊃ A


-- Notation for level 1 terms

𝜆_．_ : (x : Var) (t : Tm) → Tm
𝜆 x ． t = 𝜆ⁿ x ． t # 0

_∘_ : (t s : Tm) → Tm
t ∘ s = t ∘ⁿ s # 0

𝗽⟨_,_⟩ : (t s : Tm) → Tm
𝗽⟨ t , s ⟩ = 𝗽ⁿ⟨ t , s ⟩# 0

𝛑₀_ : (t : Tm) → Tm
𝛑₀ t = 𝛑₀ⁿ t # 0

𝛑₁_ : (t : Tm) → Tm
𝛑₁ t = 𝛑₁ⁿ t # 0

⇑_ : (t : Tm) → Tm
⇑ t = ⇑ⁿ t # 0

⇓_ : (t : Tm) → Tm
⇓ t = ⇓ⁿ t # 0


-- Notation for level 2 terms

𝜆²_．_ : (x : Var) (t : Tm) → Tm
𝜆² x ． t = 𝜆ⁿ x ． t # 1

_∘²_ : (t s : Tm) → Tm
t ∘² s = t ∘ⁿ s # 1

𝗽²⟨_,_⟩ : (t s : Tm) → Tm
𝗽²⟨ t , s ⟩ = 𝗽ⁿ⟨ t , s ⟩# 1

𝛑₀²_ : (t : Tm) → Tm
𝛑₀² t = 𝛑₀ⁿ t # 1

𝛑₁²_ : (t : Tm) → Tm
𝛑₁² t = 𝛑₁ⁿ t # 1

⇑²_ : (t : Tm) → Tm
⇑² t = ⇑ⁿ t # 1

⇓²_ : (t : Tm) → Tm
⇓² t = ⇓ⁿ t # 1


-- Term vectors

data Tms : ℕ → Set where
  tms₁ : {n : ℕ} (t : Tm)             → Tms zero
  tmsₙ : {n : ℕ} (t : Tm) (𝒕 : Tms n) → Tms (suc n)

Vt_∶_ : {n : ℕ} (𝒕 : Tms n) (A : Ty) → Ty
Vt_∶_ (tms₁ t₁)   A = t₁ ∶ A
Vt_∶_ (tmsₙ tₙ 𝒕) A = tₙ ∶ Vt 𝒕 ∶ A


-- Variable vectors

data Vars : ℕ → Set where
  vars₁ : {n : ℕ} (x : Var)              → Vars zero
  varsₙ : {n : ℕ} (x : Var) (𝒙 : Vars n) → Vars (suc n)

Vx_∶_ : {n : ℕ} (𝒙 : Vars n) (A : Ty) → Ty
Vx_∶_ (vars₁ x₁)   A = 𝑣 x₁ ∶ A
Vx_∶_ (varsₙ xₙ 𝒙) A = 𝑣 xₙ ∶ Vx 𝒙 ∶ A


-- Implication vectors

Vλ_．_∶_ : {n : ℕ} (𝒙 : Vars n) (𝒕 : Tms n) (A : Ty) → Ty
Vλ_．_∶_ {zero}  (vars₁ x₁)   (tms₁ t₁)   A = 𝜆 x₁ ． t₁ ∶ A
Vλ_．_∶_ {suc n} (varsₙ xₙ 𝒙) (tmsₙ tₙ 𝒕) A = 𝜆ⁿ xₙ ． tₙ # n ∶ Vλ 𝒙 ． 𝒕 ∶ A


data _⊢_ (Γ : Cx) : Ty → Set where

  RR𝑣  : {n : ℕ} {𝒙 : Vars n} {A : Ty}
       → Vx 𝒙 ∶ A ∈ Γ
       → Γ ⊢ Vx 𝒙 ∶ A

  RR𝜆  : {n : ℕ} {𝒙 : Vars n} {𝒕 : Tms n} {A B : Ty}
       → Γ , Vx 𝒙 ∶ A ⊢ Vt 𝒕 ∶ B
       → Γ ⊢ Vλ 𝒙 ． 𝒕 ∶ (A ⊃ B) 


  -- Typing rules for level 1 terms

  R𝑣  : {x : Var} {A : Ty}
      → 𝑣 x ∶ A ∈ Γ
      → Γ ⊢ 𝑣 x ∶ A

  R𝜆  : {x : Var} {t : Tm} {A B : Ty}
      → Γ , 𝑣 x ∶ A ⊢ t ∶ B
      → Γ ⊢ 𝜆 x ． t ∶ (A ⊃ B)

  R∘  : {t s : Tm} {A B : Ty}
      → Γ ⊢ t ∶ (A ⊃ B)    → Γ ⊢ s ∶ A
      → Γ ⊢ (t ∘ s) ∶ B

  R𝗽  : {t s : Tm} {A B : Ty}
      → Γ ⊢ t ∶ A    → Γ ⊢ s ∶ B
      → Γ ⊢ 𝗽⟨ t , s ⟩ ∶ (A ∧ B)

  R𝛑₀ : {t : Tm} {A B : Ty}
      → Γ ⊢ t ∶ (A ∧ B)
      → Γ ⊢ 𝛑₀ t ∶ A

  R𝛑₁ : {t : Tm} {A B : Ty}
      → Γ ⊢ t ∶ (A ∧ B)
      → Γ ⊢ 𝛑₁ t ∶ B

  R⇑  : {t u : Tm} {A : Ty}
      → Γ ⊢ t ∶ u ∶ A
      → Γ ⊢ ⇑ t ∶ ! u ∶ u ∶ A

  R⇓  : {t u : Tm} {A : Ty}
      → Γ ⊢ t ∶ u ∶ A
      → Γ ⊢ ⇓ t ∶ A


  -- Typing rules for level 2 terms

  R𝑣²  : {x₂ x₁ : Var} {A : Ty}
       → 𝑣 x₂ ∶ 𝑣 x₁ ∶ A ∈ Γ
       → Γ ⊢ 𝑣 x₂ ∶ 𝑣 x₁ ∶ A

  R𝜆²  : {x₂ x₁ : Var} {t₂ t₁ : Tm} {A B : Ty}
       → Γ , 𝑣 x₂ ∶ 𝑣 x₁ ∶ A ⊢ t₂ ∶ t₁ ∶ B
       → Γ ⊢ 𝜆² x₂ ． t₂ ∶ 𝜆 x₁ ． t₁ ∶ (A ⊃ B)

  R∘²  : {t₂ t₁ s₂ s₁ : Tm} {A B : Ty}
       → Γ ⊢ t₂ ∶ t₁ ∶ (A ⊃ B)    → Γ ⊢ s₂ ∶ s₁ ∶ A
       → Γ ⊢ (t₂ ∘² s₂) ∶ (t₁ ∘ s₁) ∶ B

  R𝗽²  : {t₂ t₁ s₂ s₁ : Tm} {A B : Ty}
       → Γ ⊢ t₂ ∶ t₁ ∶ A    → Γ ⊢ s₂ ∶ s₁ ∶ B
       → Γ ⊢ 𝗽²⟨ t₂ , s₂ ⟩ ∶ 𝗽⟨ t₁ , s₁ ⟩ ∶ (A ∧ B)

  R𝛑₀² : {t₂ t₁ : Tm} {A B : Ty}
       → Γ ⊢ t₂ ∶ t₁ ∶ (A ∧ B)
       → Γ ⊢ 𝛑₀² t₂ ∶ 𝛑₀ t₁ ∶ A

  R𝛑₁² : {t₂ t₁ : Tm} {A B : Ty}
       → Γ ⊢ t₂ ∶ t₁ ∶ (A ∧ B)
       → Γ ⊢ 𝛑₁² t₂ ∶ 𝛑₁ t₁ ∶ B

  R⇑²  : {t₂ t₁ u : Tm} {A : Ty}
       → Γ ⊢ t₂ ∶ t₁ ∶ u ∶ A
       → Γ ⊢ ⇑² t₂ ∶ ⇑ t₁ ∶ ! u ∶ u ∶ A

  R⇓²  : {t₂ t₁ u : Tm} {A : Ty}
       → Γ ⊢ t₂ ∶ t₁ ∶ u ∶ A
       → Γ ⊢ ⇓² t₂ ∶ ⇓ t₁ ∶ A


-- Theorems

⊩_  : (A : Ty) → Set
⊩ A = {Γ : Cx} → Γ ⊢ A


-- Example 1 (p. 28[1])

e1₁ : {x y : Var} {A : Ty}
    → ⊩ 𝜆 y ． ⇓ 𝑣 y ∶ (𝑣 x ∶ A ⊃ A)
e1₁ = R𝜆 (R⇓ (R𝑣 Z))

e1₂ : {x y : Var} {A : Ty}
    → ⊩ 𝜆 y ． ⇑ 𝑣 y ∶ (𝑣 x ∶ A ⊃ ! 𝑣 x ∶ 𝑣 x ∶ A)
e1₂ = R𝜆 (R⇑ (R𝑣 Z))

e1₃ : {u x v y : Var} {A B : Ty}
    → ⊩ 𝜆² u ． 𝜆² v ． 𝗽²⟨ 𝑣 u , 𝑣 v ⟩ ∶ 𝜆 x ． 𝜆 y ． 𝗽⟨ 𝑣 x , 𝑣 y ⟩ ∶ (A ⊃ B ⊃ A ∧ B)
e1₃ = R𝜆² (R𝜆² (R𝗽² (R𝑣² (S Z))
                    (R𝑣² Z)))

e1₄ : {u x v y : Var} {A B : Ty}
    → ⊩ 𝜆 u ． 𝜆 v ． ⇑ 𝗽²⟨ 𝑣 u , 𝑣 v ⟩ ∶ (𝑣 x ∶ A ⊃ 𝑣 y ∶ B ⊃ ! 𝗽⟨ 𝑣 x , 𝑣 y ⟩ ∶ 𝗽⟨ 𝑣 x , 𝑣 y ⟩ ∶ (A ∧ B))
e1₄ = R𝜆 (R𝜆 (R⇑ (R𝗽² (R𝑣 (S Z))
                      (R𝑣 Z))))


-- Example 2 (pp. 31–32[1])

e2  : {x₃ x₂ x₁ : Var} {A : Ty}
    → ⊩ 𝜆² x₃ ． ⇓² ⇑² 𝑣 x₃ ∶ 𝜆 x₂ ． ⇓ ⇑ 𝑣 x₂ ∶ (𝑣 x₁ ∶ A ⊃ 𝑣 x₁ ∶ A)
e2 = R𝜆² (R⇓² (R⇑² (R𝑣² Z)))

e2' : {x₃ x₂ x₁ : Var} {A : Ty}
    → ⊩ 𝜆² x₃ ． 𝑣 x₃ ∶ 𝜆 x₂ ． 𝑣 x₂ ∶ (𝑣 x₁ ∶ A ⊃ 𝑣 x₁ ∶ A)
e2' = R𝜆² (R𝑣² Z)
