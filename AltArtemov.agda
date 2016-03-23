{-

An implementation of the Alt-Artëmov system λ∞
==============================================

Miëtek Bak  <mietek@bak.io>


Work in progress.  Checked with Agda 2.4.2.5.

For easy editing with Emacs agda-mode, add to your .emacs file:

'(agda-input-user-translations
   (quote
    (("i" "⊃") ("ii" "⫗") ("e" "⊢") ("ee" "⊩") ("n" "¬") ("N" "ℕ")
     ("v" "𝑣") ("l" "𝜆") ("l2" "𝜆²") ("l3" "𝜆³") ("ln" "𝜆ⁿ")
     ("o" "∘") ("o2" "∘²") ("o3" "∘³") ("on" "∘ⁿ")
     ("p" "𝑝") ("p2" "𝑝²") ("p3" "𝑝³") ("pn" "𝑝ⁿ")
     ("pi0" "𝜋₀") ("pi02" "𝜋₀²") ("pi03" "𝜋₀³") ("pi0n" "𝜋₀ⁿ")
     ("pi1" "𝜋₁") ("pi12" "𝜋₁²") ("pi13" "𝜋₁³") ("pi1n" "𝜋₁ⁿ")
     ("u" "⇑") ("u2" "⇑²") ("u3" "⇑³") ("un" "⇑ⁿ")
     ("d" "⇓") ("d2" "⇓²") ("d3" "⇓³") ("dn" "⇓ⁿ")
     ("mv" "𝒗") ("ml" "𝝀") ("ml2" "𝝀²") ("ml3" "𝝀³") ("ml4" "𝝀⁴") ("mln" "𝝀ⁿ")
     ("mo" "∙") ("mo2" "∙²") ("mo3" "∙³") ("mo4" "∙⁴") ("mon" "∙ⁿ")
     ("mp" "𝒑") ("mp2" "𝒑²") ("mp3" "𝒑³") ("mp4" "𝒑⁴") ("mpn" "𝒑ⁿ")
     ("mpi0" "𝝅₀") ("mpi02" "𝝅₀²") ("mpi03" "𝝅₀³") ("mpi04" "𝝅₀⁴") ("mpi0n" "𝝅₀ⁿ")
     ("mpi1" "𝝅₁") ("mpi12" "𝝅₁²") ("mpi13" "𝝅₁³") ("mpi14" "𝝅₁⁴") ("mpi1n" "𝝅₁ⁿ")
     ("mu" "⬆") ("mu2" "⬆²") ("mu3" "⬆³") ("mu4" "⬆⁴") ("mun" "⬆ⁿ")
     ("md" "⬇") ("md2" "⬇²") ("md3" "⬇³") ("md4" "⬇⁴") ("mdn" "⬇ⁿ")
     ("mS" "𝐒") ("mZ" "𝐙")
     ("m0" "𝟎") ("m1" "𝟏") ("m2" "𝟐") ("m3" "𝟑") ("m4" "𝟒")
     ("m5" "𝟓") ("m6" "𝟔") ("m7" "𝟕") ("m8" "𝟖") ("m9" "𝟗")
     ("s" "𝐬") ("t" "𝐭") ("x" "𝐱") ("y" "𝐲"))))


[1]: Alt, J., Artëmov, S. (2001) Reflective λ-calculus,
     Proceedings of the 2001 International Seminar on Proof Theory in
     Computer Science (PTCS’01), Lecture Notes in Computer Science,
     vol. 2183, pp. 22–37.
     http://dx.doi.org/10.1007/3-540-45504-3_2

[2]: Artëmov, S. (2001) Explicit provability and constructive semantics
     Bulletin of Symbolic Logic, vol. 7, no. 1, pp. 1–36.
     http://dx.doi.org/10.2307/2687821

-}


module AltArtemov where

open import Data.Nat
  using (ℕ ; zero ; suc)

open import Data.Product
  using (Σ ; _×_)
  renaming (_,_ to ⟨_,_⟩ ; proj₁ to proj₀ ; proj₂ to proj₁)

open import Data.Vec
  using (Vec ; [] ; _∷_ ; replicate)

infixl 9 !_
infixl 9 𝑣_ 𝒗_
infixl 8 𝜋₀_ 𝜋₀²_ 𝜋₀³_ 𝝅₀_ 𝝅₀²_ 𝝅₀³_ 𝝅₀⁴_ 𝝅₀ⁿ_
infixl 8 𝜋₁_ 𝜋₁²_ 𝜋₁³_ 𝝅₁_ 𝝅₁²_ 𝝅₁³_ 𝝅₁⁴_ 𝝅₁ⁿ_
infixl 7 _∘_ _∘²_ _∘³_ _∙_ _∙²_ _∙³_ _∙⁴_ _∙ⁿ_
infixr 6 ⇑_ ⇑²_ ⇑³_ ⬆_ ⬆²_ ⬆³_ ⬆⁴_ ⬆ⁿ_
infixr 6 ⇓_ ⇓²_ ⇓³_ ⬇_ ⬇²_ ⬇³_ ⬇⁴_ ⬇ⁿ_
infixr 5 𝜆_ 𝜆²_ 𝜆³_ 𝝀_ 𝝀²_ 𝝀³_ 𝝀⁴_ 𝝀ⁿ_
infixr 4 _∶_
infixr 3 ¬_
infixl 2 _∧_
infixl 2 _,_
infixr 1 _⊃_ _⫗_
infixr 0 _⊢_ ⊩_


-- --------------------------------------------------------------------------
--
-- Untyped syntax


-- Variables
Var : Set
Var = ℕ


-- Term constructors
data Tm : Set where
  -- Variable reference
  𝑣_ : Var → Tm

  -- Abstraction (⊃I) at level n
  𝜆[_]_ : ℕ → Tm → Tm

  -- Application (⊃E) at level n
  _∘[_]_ : Tm → ℕ → Tm → Tm

  -- Pairing (∧I) at level n
  𝑝[_]⟨_,_⟩ : ℕ → Tm → Tm → Tm

  -- 0th projection (∧E₀) at level n
  𝜋₀[_]_ : ℕ → Tm → Tm

  -- 1st projection (∧E₁) at level n
  𝜋₁[_]_ : ℕ → Tm → Tm

  -- Artëmov’s “proof checker”
  !_ : Tm → Tm

  -- Reification at level n
  ⇑[_]_ : ℕ → Tm → Tm

  -- Reflection at level n
  ⇓[_]_ : ℕ → Tm → Tm


-- Type constructors
data Ty : Set where
  -- Falsehood
  ⊥ : Ty

  -- Implication
  _⊃_ : Ty → Ty → Ty

  -- Conjunction
  _∧_ : Ty → Ty → Ty

  -- Explicit provability
  _∶_ : Tm → Ty → Ty


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
A ⫗ B = (A ⊃ B) ∧ (B ⊃ A)


-- --------------------------------------------------------------------------
--
-- Notation for term constructors at level 1


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


-- --------------------------------------------------------------------------
--
-- Notation for term constructors at level 2


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
-- Notation for term constructors at level 3


𝜆³_ : Tm → Tm
𝜆³ t₃ = 𝜆[ 3 ] t₃

_∘³_ : Tm → Tm → Tm
t₃ ∘³ s₃ = t₃ ∘[ 3 ] s₃

𝑝³⟨_,_⟩ : Tm → Tm → Tm
𝑝³⟨ t₃ , s₃ ⟩ = 𝑝[ 3 ]⟨ t₃ , s₃ ⟩

𝜋₀³_ : Tm → Tm
𝜋₀³ t₃ = 𝜋₀[ 3 ] t₃

𝜋₁³_ : Tm → Tm
𝜋₁³ t₃ = 𝜋₁[ 3 ] t₃

⇑³_ : Tm → Tm
⇑³ t₃ = ⇑[ 3 ] t₃

⇓³_ : Tm → Tm
⇓³ t₃ = ⇓[ 3 ] t₃


-- --------------------------------------------------------------------------
--
-- Vector notation for type assertions at level n (p. 27 [1])


map# : ∀{n} {X Y : Set}
    → (ℕ → X → Y) → Vec X n → Vec Y n
map# {zero}  f []      = []
map# {suc n} f (x ∷ 𝐱) = f (suc n) x ∷ map# f 𝐱

zipWith# : ∀{n} {X Y Z : Set}
    → (ℕ → X → Y → Z) → Vec X n → Vec Y n → Vec Z n
zipWith# {zero}  f []      []       = []
zipWith# {suc n} f (x ∷ 𝐱) (y ∷ 𝐲) = f (suc n) x y ∷ zipWith# f 𝐱 𝐲


-- Term vectors
Tms : ℕ → Set
Tms = Vec Tm


-- tₙ ∶ tₙ₋₁ ∶ … ∶ t₁ ∶ A
*_∷_ : ∀{n} → Tms n → Ty → Ty
* []      ∷ A = A
* (x ∷ 𝐭) ∷ A = x ∶ * 𝐭 ∷ A

-- 𝑣 x ∶ 𝑣 x ∶ … ∶ 𝑣 x ∶ A
𝑣[_]_∷_ : ℕ → Var → Ty → Ty
𝑣[ n ] x ∷ A = * replicate {n = n} (𝑣 x) ∷ A

-- 𝜆ⁿ tₙ ∶ 𝜆ⁿ⁻¹ tₙ₋₁ ∶ … ∶ 𝜆 t₁ ∶ A
𝜆ⁿ_∷_ : ∀{n} → Tms n → Ty → Ty
𝜆ⁿ 𝐭 ∷ A = * map# 𝜆[_]_ 𝐭 ∷ A

-- tₙ ∘ⁿ sₙ ∶ tₙ₋₁ ∘ⁿ⁻¹ ∶ sₙ₋₁ ∶ … ∶ t₁ ∘ s₁ ∶ A
_∘ⁿ_∷_ : ∀{n} → Tms n → Tms n → Ty → Ty
𝐭 ∘ⁿ 𝐬 ∷ A = * zipWith# (λ n t s → t ∘[ n ] s) 𝐭 𝐬 ∷ A

-- 𝑝ⁿ⟨ tₙ , sₙ ⟩ ∶ 𝑝ⁿ⁻¹⟨ tₙ₋₁ , sₙ₋₁ ⟩ ∶ … ∶ p⟨ t₁ , s₁ ⟩ ∶ A
𝑝ⁿ⟨_,_⟩∷_ : ∀{n} → Tms n → Tms n → Ty → Ty
𝑝ⁿ⟨ 𝐭 , 𝐬 ⟩∷ A = * zipWith# 𝑝[_]⟨_,_⟩ 𝐭 𝐬 ∷ A

-- 𝜋₀ⁿ tₙ ∶ 𝜋₀ⁿ⁻¹ tₙ₋₁ ∶ … ∶ 𝜋₀ t₁ ∶ A
𝜋₀ⁿ_∷_ : ∀{n} → Tms n → Ty → Ty
𝜋₀ⁿ 𝐭 ∷ A = * map# 𝜋₀[_]_ 𝐭 ∷ A

-- 𝜋₁ⁿ tₙ ∶ 𝜋₁ⁿ⁻¹ tₙ₋₁ ∶ … ∶ 𝜋₁ t₁ ∶ A
𝜋₁ⁿ_∷_ : ∀{n} → Tms n → Ty → Ty
𝜋₁ⁿ 𝐭 ∷ A = * map# 𝜋₁[_]_ 𝐭 ∷ A

-- ⇑ⁿ tₙ ∶ ⇑ⁿ⁻¹ tₙ₋₁ ∶ … ∶ ⇑ t₁ ∶ A
⇑ⁿ_∷_ : ∀{n} → Tms n → Ty → Ty
⇑ⁿ 𝐭 ∷ A = * map# ⇑[_]_ 𝐭 ∷ A

-- ⇓ⁿ tₙ ∶ ⇑ⁿ⁻¹ tₙ₋₁ ∶ … ∶ ⇑ t₁ ∶ A
⇓ⁿ_∷_ : ∀{n} → Tms n → Ty → Ty
⇓ⁿ 𝐭 ∷ A = * map# ⇓[_]_ 𝐭 ∷ A


-- --------------------------------------------------------------------------
--
-- Typed syntax


-- Hypotheses
Hyp : Set
Hyp = ℕ × Ty


-- Contexts
data Cx : Set where
  ∅   : Cx
  _,_ : Cx → Hyp → Cx


-- Context membership evidence
data _∈[_]_ : Hyp → ℕ → Cx → Set where
  𝐙 : ∀{A Γ}
      → A ∈[ zero ] (Γ , A)

  𝐒_ : ∀{A B x Γ}
      → A ∈[ x ] Γ
      → A ∈[ suc x ] (Γ , B)


-- Typed terms
data _⊢_ (Γ : Cx) : Ty → Set where
  𝒗_ : ∀{n x A}
      → ⟨ n , A ⟩ ∈[ x ] Γ
      → Γ ⊢ 𝑣[ n ] x ∷ A

  𝝀ⁿ_ : ∀{n} {𝐭 : Tms n} {A B}
      → Γ , ⟨ n , A ⟩ ⊢ * 𝐭 ∷ B
      → Γ ⊢ 𝜆ⁿ 𝐭 ∷ (A ⊃ B)

  _∙ⁿ_ : ∀{n} {𝐭 𝐬 : Tms n} {A B}
      → Γ ⊢ * 𝐭 ∷ (A ⊃ B)    → Γ ⊢ * 𝐬 ∷ A
      → Γ ⊢ 𝐭 ∘ⁿ 𝐬 ∷ B

  𝒑ⁿ⟨_,_⟩ : ∀{n} {𝐭 𝐬 : Tms n} {A B}
      → Γ ⊢ * 𝐭 ∷ A          → Γ ⊢ * 𝐬 ∷ B
      → Γ ⊢ 𝑝ⁿ⟨ 𝐭 , 𝐬 ⟩∷ (A ∧ B)

  𝝅₀ⁿ_ : ∀{n} {𝐭 : Tms n} {A B}
      → Γ ⊢ * 𝐭 ∷ (A ∧ B)
      → Γ ⊢ 𝜋₀ⁿ 𝐭 ∷ A

  𝝅₁ⁿ_ : ∀{n} {𝐭 : Tms n} {A B}
      → Γ ⊢ * 𝐭 ∷ (A ∧ B)
      → Γ ⊢ 𝜋₁ⁿ 𝐭 ∷ B

  ⬆ⁿ_ : ∀{n} {𝐭 : Tms n} {u A}
      → Γ ⊢ * 𝐭 ∷ (u ∶ A)
      → Γ ⊢ ⇑ⁿ 𝐭 ∷ (! u ∶ u ∶ A)

  ⬇ⁿ_ : ∀{n} {𝐭 : Tms n} {u A}
      → Γ ⊢ * 𝐭 ∷ (u ∶ A)
      → Γ ⊢ ⇓ⁿ 𝐭 ∷ A


⊩_  : Ty → Set
⊩ A = ∅ ⊢ A


-- --------------------------------------------------------------------------
--
-- Notation for context membership evidence


𝟎 : ∀{A Γ}
    → A ∈[ 0 ] (Γ , A)
𝟎 = 𝐙

𝟏 : ∀{A B Γ}
    → A ∈[ 1 ] (Γ , A , B)
𝟏 = 𝐒 𝟎

𝟐 : ∀{A B C Γ}
    → A ∈[ 2 ] (Γ , A , B , C)
𝟐 = 𝐒 𝟏

𝟑 : ∀{A B C D Γ}
    → A ∈[ 3 ] (Γ , A , B , C , D)
𝟑 = 𝐒 𝟐

𝟒 : ∀{A B C D E Γ}
    → A ∈[ 4 ] (Γ , A , B , C , D , E)
𝟒 = 𝐒 𝟑

𝟓 : ∀{A B C D E F Γ}
    → A ∈[ 5 ] (Γ , A , B , C , D , E , F)
𝟓 = 𝐒 𝟒

𝟔 : ∀{A B C D E F G Γ}
    → A ∈[ 6 ] (Γ , A , B , C , D , E , F , G)
𝟔 = 𝐒 𝟓

𝟕 : ∀{A B C D E F G H Γ}
    → A ∈[ 7 ] (Γ , A , B , C , D , E , F , G , H)
𝟕 = 𝐒 𝟔

𝟖 : ∀{A B C D E F G H I Γ}
    → A ∈[ 8 ] (Γ , A , B , C , D , E , F , G , H , I)
𝟖 = 𝐒 𝟕

𝟗 : ∀{A B C D E F G H I J Γ}
    → A ∈[ 9 ] (Γ , A , B , C , D , E , F , G , H , I , J)
𝟗 = 𝐒 𝟖


-- --------------------------------------------------------------------------
--
-- Notation for typed terms at level 1


𝝀_ : ∀{A B Γ}
    → Γ , ⟨ 0 , A ⟩ ⊢ B
    → Γ ⊢ A ⊃ B
𝝀_ = 𝝀ⁿ_ {𝐭 = []}

_∙_ : ∀{A B Γ}
    → Γ ⊢ A ⊃ B    → Γ ⊢ A
    → Γ ⊢ B
_∙_ = _∙ⁿ_ {𝐭 = []} {𝐬 = []}

𝒑⟨_,_⟩ : ∀{A B Γ}
    → Γ ⊢ A        → Γ ⊢ B
    → Γ ⊢ A ∧ B
𝒑⟨_,_⟩ = 𝒑ⁿ⟨_,_⟩ {𝐭 = []} {𝐬 = []}

𝝅₀_ : ∀{A B Γ}
    → Γ ⊢ A ∧ B
    → Γ ⊢ A
𝝅₀_ = 𝝅₀ⁿ_ {𝐭 = []}

𝝅₁_ : ∀{A B Γ}
    → Γ ⊢ A ∧ B
    → Γ ⊢ B
𝝅₁_ = 𝝅₁ⁿ_ {𝐭 = []}

⬆_ : ∀{u A Γ}
    → Γ ⊢ u ∶ A
    → Γ ⊢ ! u ∶ u ∶ A
⬆_ = ⬆ⁿ_ {𝐭 = []}

⬇_ : ∀{u A Γ}
    → Γ ⊢ u ∶ A
    → Γ ⊢ A
⬇_ = ⬇ⁿ_ {𝐭 = []}


-- --------------------------------------------------------------------------
--
-- Notation for typed terms at level 2


𝝀²_ : ∀{t A B Γ}
    → Γ , ⟨ 1 , A ⟩ ⊢ t ∶ B
    → Γ ⊢ 𝜆 t ∶ (A ⊃ B)
𝝀²_ {t} =
    𝝀ⁿ_ {𝐭 = t ∷ []}

_∙²_ : ∀{t s A B Γ}
    → Γ ⊢ t ∶ (A ⊃ B)    → Γ ⊢ s ∶ A
    → Γ ⊢ t ∘ s ∶ B
_∙²_ {t} {s} =
    _∙ⁿ_ {𝐭 = t ∷ []} {𝐬 = s ∷ []}

𝒑²⟨_,_⟩ : ∀{t s A B Γ}
    → Γ ⊢ t ∶ A          → Γ ⊢ s ∶ B
    → Γ ⊢ 𝑝⟨ t , s ⟩ ∶ (A ∧ B)
𝒑²⟨_,_⟩ {t} {s} =
    𝒑ⁿ⟨_,_⟩ {𝐭 = t ∷ []} {𝐬 = s ∷ []}

𝝅₀²_ : ∀{t A B Γ}
    → Γ ⊢ t ∶ (A ∧ B)
    → Γ ⊢ 𝜋₀ t ∶ A
𝝅₀²_ {t} =
    𝝅₀ⁿ_ {𝐭 = t ∷ []}

𝝅₁²_ : ∀{t A B Γ}
    → Γ ⊢ t ∶ (A ∧ B)
    → Γ ⊢ 𝜋₁ t ∶ B
𝝅₁²_ {t} =
    𝝅₁ⁿ_ {𝐭 = t ∷ []}

⬆²_ : ∀{t u A Γ}
    → Γ ⊢ t ∶ u ∶ A
    → Γ ⊢ ⇑ t ∶ ! u ∶ u ∶ A
⬆²_ {t} =
    ⬆ⁿ_ {𝐭 = t ∷ []}

⬇²_ : ∀{t u A Γ}
    → Γ ⊢ t ∶ u ∶ A
    → Γ ⊢ ⇓ t ∶ A
⬇²_ {t} =
    ⬇ⁿ_ {𝐭 = t ∷ []}


-- --------------------------------------------------------------------------
--
-- Notation for typed terms at level 3


𝝀³_ : ∀{t₂ t₁ A B Γ}
    → Γ , ⟨ 2 , A ⟩ ⊢ t₂ ∶ t₁ ∶ B
    → Γ ⊢ 𝜆² t₂ ∶ 𝜆 t₁ ∶ (A ⊃ B)
𝝀³_ {t₂} {t₁} =
    𝝀ⁿ_ {𝐭 = t₂ ∷ t₁ ∷ []}

_∙³_ : ∀{t₂ t₁ s₂ s₁ A B Γ}
    → Γ ⊢ t₂ ∶ t₁ ∶ (A ⊃ B)    → Γ ⊢ s₂ ∶ s₁ ∶ A
    → Γ ⊢ t₂ ∘² s₂ ∶ t₁ ∘ s₁ ∶ B
_∙³_ {t₂} {t₁} {s₂} {s₁} =
    _∙ⁿ_ {𝐭 = t₂ ∷ t₁ ∷ []} {𝐬 = s₂ ∷ s₁ ∷ []}

𝒑³⟨_,_⟩ : ∀{t₂ t₁ s₂ s₁ A B Γ}
    → Γ ⊢ t₂ ∶ t₁ ∶ A          → Γ ⊢ s₂ ∶ s₁ ∶ B
    → Γ ⊢ 𝑝²⟨ t₂ , s₂ ⟩ ∶ 𝑝⟨ t₁ , s₁ ⟩ ∶ (A ∧ B)
𝒑³⟨_,_⟩ {t₂} {t₁} {s₂} {s₁} =
    𝒑ⁿ⟨_,_⟩ {𝐭 = t₂ ∷ t₁ ∷ []} {𝐬 = s₂ ∷ s₁ ∷ []}

𝝅₀³_ : ∀{t₂ t₁ A B Γ}
    → Γ ⊢ t₂ ∶ t₁ ∶ (A ∧ B)
    → Γ ⊢ 𝜋₀² t₂ ∶ 𝜋₀ t₁ ∶ A
𝝅₀³_ {t₂} {t₁} =
    𝝅₀ⁿ_ {𝐭 = t₂ ∷ t₁ ∷ []}

𝝅₁³_ : ∀{t₂ t₁ A B Γ}
    → Γ ⊢ t₂ ∶ t₁ ∶ (A ∧ B)
    → Γ ⊢ 𝜋₁² t₂ ∶ 𝜋₁ t₁ ∶ B
𝝅₁³_ {t₂} {t₁} =
    𝝅₁ⁿ_ {𝐭 = t₂ ∷ t₁ ∷ []}

⬆³_ : ∀{t₂ t₁ u A Γ}
    → Γ ⊢ t₂ ∶ t₁ ∶ u ∶ A
    → Γ ⊢ ⇑² t₂ ∶ ⇑ t₁ ∶ ! u ∶ u ∶ A
⬆³_ {t₂} {t₁} =
    ⬆ⁿ_ {𝐭 = t₂ ∷ t₁ ∷ []}

⬇³_ : ∀{t₂ t₁ u A Γ}
    → Γ ⊢ t₂ ∶ t₁ ∶ u ∶ A
    → Γ ⊢ ⇓² t₂ ∶ ⇓ t₁ ∶ A
⬇³_ {t₂} {t₁} =
    ⬇ⁿ_ {𝐭 = t₂ ∷ t₁ ∷ []}


-- --------------------------------------------------------------------------
--
-- Notation for typed terms at level 4


𝝀⁴_ : ∀{t₃ t₂ t₁ A B Γ}
    → Γ , ⟨ 3 , A ⟩ ⊢ t₃ ∶ t₂ ∶ t₁ ∶ B
    → Γ ⊢ 𝜆³ t₃ ∶ 𝜆² t₂ ∶ 𝜆 t₁ ∶ (A ⊃ B)
𝝀⁴_ {t₃} {t₂} {t₁} =
    𝝀ⁿ_ {𝐭 = t₃ ∷ t₂ ∷ t₁ ∷ []}

_∙⁴_ : ∀{t₃ t₂ t₁ s₃ s₂ s₁ A B Γ}
    → Γ ⊢ t₃ ∶ t₂ ∶ t₁ ∶ (A ⊃ B)    → Γ ⊢ s₃ ∶ s₂ ∶ s₁ ∶ A
    → Γ ⊢ t₃ ∘³ s₃ ∶ t₂ ∘² s₂ ∶ t₁ ∘ s₁ ∶ B
_∙⁴_ {t₃} {t₂} {t₁} {s₃} {s₂} {s₁} =
    _∙ⁿ_ {𝐭 = t₃ ∷ t₂ ∷ t₁ ∷ []} {𝐬 = s₃ ∷ s₂ ∷ s₁ ∷ []}

𝒑⁴⟨_,_⟩ : ∀{t₃ t₂ t₁ s₃ s₂ s₁ A B Γ}
    → Γ ⊢ t₃ ∶ t₂ ∶ t₁ ∶ A          → Γ ⊢ s₃ ∶ s₂ ∶ s₁ ∶ B
    → Γ ⊢ 𝑝³⟨ t₃ , s₃ ⟩ ∶ 𝑝²⟨ t₂ , s₂ ⟩ ∶ 𝑝⟨ t₁ , s₁ ⟩ ∶ (A ∧ B)
𝒑⁴⟨_,_⟩ {t₃} {t₂} {t₁} {s₃} {s₂} {s₁} =
    𝒑ⁿ⟨_,_⟩ {𝐭 = t₃ ∷ t₂ ∷ t₁ ∷ []} {𝐬 = s₃ ∷ s₂ ∷ s₁ ∷ []}

𝝅₀⁴_ : ∀{t₃ t₂ t₁ A B Γ}
    → Γ ⊢ t₃ ∶ t₂ ∶ t₁ ∶ (A ∧ B)
    → Γ ⊢ 𝜋₀³ t₃ ∶ 𝜋₀² t₂ ∶ 𝜋₀ t₁ ∶ A
𝝅₀⁴_ {t₃} {t₂} {t₁} =
    𝝅₀ⁿ_ {𝐭 = t₃ ∷ t₂ ∷ t₁ ∷ []}

𝝅₁⁴_ : ∀{t₃ t₂ t₁ A B Γ}
    → Γ ⊢ t₃ ∶ t₂ ∶ t₁ ∶ (A ∧ B)
    → Γ ⊢ 𝜋₁³ t₃ ∶ 𝜋₁² t₂ ∶ 𝜋₁ t₁ ∶ B
𝝅₁⁴_ {t₃} {t₂} {t₁} =
    𝝅₁ⁿ_ {𝐭 = t₃ ∷ t₂ ∷ t₁ ∷ []}

⬆⁴_ : ∀{t₃ t₂ t₁ u A Γ}
    → Γ ⊢ t₃ ∶ t₂ ∶ t₁ ∶ u ∶ A
    → Γ ⊢ ⇑³ t₃ ∶ ⇑² t₂ ∶ ⇑ t₁ ∶ ! u ∶ u ∶ A
⬆⁴_ {t₃} {t₂} {t₁} =
    ⬆ⁿ_ {𝐭 = t₃ ∷ t₂ ∷ t₁ ∷ []}

⬇⁴_ : ∀{t₃ t₂ t₁ u A Γ}
    → Γ ⊢ t₃ ∶ t₂ ∶ t₁ ∶ u ∶ A
    → Γ ⊢ ⇓³ t₃ ∶ ⇓² t₂ ∶ ⇓ t₁ ∶ A
⬇⁴_ {t₃} {t₂} {t₁} =
    ⬇ⁿ_ {𝐭 = t₃ ∷ t₂ ∷ t₁ ∷ []}


-- --------------------------------------------------------------------------
--
-- Example terms corresponding to S4 theorems at levels 1, 2, and 3


-- S4: A ⊃ A
tI : ∀{A}
    → ⊩  A ⊃ A
tI = 𝝀 𝒗 𝟎

-- S4: □(A ⊃ A)
tI² : ∀{A}
    → ⊩  𝜆 𝑣 0  ∶  (A ⊃ A)
tI² = 𝝀² 𝒗 𝟎

-- S4: □□(A ⊃ A)
tI³ : ∀{A}
    → ⊩  𝜆² 𝑣 0  ∶  𝜆 𝑣 0  ∶  (A ⊃ A)
tI³ = 𝝀³ 𝒗 𝟎


-- S4: A ⊃ B ⊃ A
tK : ∀{A B}
    → ⊩  A ⊃ B ⊃ A
tK = 𝝀 𝝀 𝒗 𝟏

-- S4: □(A ⊃ B ⊃ A)
tK² : ∀{A B}
    → ⊩  𝜆 𝜆 𝑣 1  ∶  (A ⊃ B ⊃ A)
tK² = 𝝀² 𝝀² 𝒗 𝟏

-- S4: □□(A ⊃ B ⊃ A)
tK³ : ∀{A B}
    → ⊩  𝜆² 𝜆² 𝑣 1  ∶  𝜆 𝜆 𝑣 1  ∶  (A ⊃ B ⊃ A)
tK³ = 𝝀³ 𝝀³ 𝒗 𝟏


-- S4: (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
tS : ∀{A B C}
    → ⊩  (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
tS = 𝝀 𝝀 𝝀 (𝒗 𝟐 ∙ 𝒗 𝟎) ∙ (𝒗 𝟏 ∙ 𝒗 𝟎)

-- S4: □((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
tS² : ∀{A B C}
    → ⊩  𝜆 𝜆 𝜆 (𝑣 2 ∘ 𝑣 0) ∘ (𝑣 1 ∘ 𝑣 0)  ∶  ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
tS² = 𝝀² 𝝀² 𝝀² (𝒗 𝟐 ∙² 𝒗 𝟎) ∙² (𝒗 𝟏 ∙² 𝒗 𝟎)

-- S4: □□((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
tS³ : ∀{A B C}
    → ⊩  𝜆² 𝜆² 𝜆² (𝑣 2 ∘² 𝑣 0) ∘² (𝑣 1 ∘² 𝑣 0)  ∶  𝜆 𝜆 𝜆 (𝑣 2 ∘ 𝑣 0) ∘ (𝑣 1 ∘ 𝑣 0)  ∶  ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
tS³ = 𝝀³ 𝝀³ 𝝀³ (𝒗 𝟐 ∙³ 𝒗 𝟎) ∙³ (𝒗 𝟏 ∙³ 𝒗 𝟎)


-- --------------------------------------------------------------------------
--
-- Example terms corresponding to S4 axioms at levels 1 and 2


-- S4: □(A ⊃ B) ⊃ □A ⊃ □B
tAK : ∀{f x A B}
    → ⊩  (f ∶ (A ⊃ B)) ⊃ x ∶ A ⊃ (f ∘ x) ∶ B
tAK = 𝝀 𝝀 (𝒗 𝟏 ∙² 𝒗 𝟎)

-- S4: □(□(A ⊃ B) ⊃ □A ⊃ □B)
tAK² : ∀{f x A B}
    → ⊩  𝜆 𝜆 𝑣 1 ∘² 𝑣 0  ∶  (f ∶ (A ⊃ B) ⊃ x ∶ A ⊃ (f ∘ x) ∶ B)
tAK² = 𝝀² 𝝀² (𝒗 𝟏 ∙³ 𝒗 𝟎)

-- S4: □A ⊃ A
tAT : ∀{x A}
    → ⊩  x ∶ A ⊃ A
tAT = 𝝀 ⬇ 𝒗 𝟎

-- S4: □(□A ⊃ A)
tAT² : ∀{x A}
    → ⊩  𝜆 ⇓ 𝑣 0  ∶  (x ∶ A ⊃ A)
tAT² = 𝝀² ⬇² 𝒗 𝟎

-- S4: □A ⊃ □□A
tA4 : ∀{x A}
    → ⊩  x ∶ A ⊃ ! x ∶ x ∶ A
tA4 = 𝝀 ⬆ 𝒗 𝟎

-- S4: □(□A ⊃ □□A)
tA4² : ∀{x A}
    → ⊩  𝜆 ⇑ 𝑣 0  ∶  (x ∶ A ⊃ ! x ∶ x ∶ A)
tA4² = 𝝀² ⬆² 𝒗 𝟎


-- --------------------------------------------------------------------------
--
-- Terms of example 1 (p. 28 [1])


-- S4: □(□A ⊃ A)
tE11 : ∀{x A}
    → ⊩  𝜆 ⇓ 𝑣 0  ∶  (x ∶ A ⊃ A)
tE11 = tAT²

-- S4: □(□A ⊃ □□A)
tE12 : ∀{x A}
    → ⊩  𝜆 ⇑ 𝑣 0  ∶  (x ∶ A ⊃ ! x ∶ x ∶ A)
tE12 = tA4²

-- S4: □□(A ⊃ B ⊃ A ∧ B)
tE13 : ∀{A B}
    → ⊩  𝜆² 𝜆² 𝑝²⟨ 𝑣 1 , 𝑣 0 ⟩  ∶  𝜆 𝜆 𝑝⟨ 𝑣 1 , 𝑣 0 ⟩  ∶  (A ⊃ B ⊃ A ∧ B)
tE13 = 𝝀³ 𝝀³ 𝒑³⟨ 𝒗 𝟏 , 𝒗 𝟎 ⟩

-- S4: □(□A ⊃ □B ⊃ □□(A ∧ B))
tE14 : ∀{x y A B}
    → ⊩  𝜆 𝜆 ⇑ 𝑝²⟨ 𝑣 1 , 𝑣 0 ⟩  ∶  (x ∶ A ⊃ y ∶ B ⊃ ! 𝑝⟨ x , y ⟩ ∶ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
tE14 = 𝝀² 𝝀² ⬆² 𝒑³⟨ 𝒗 𝟏 , 𝒗 𝟎 ⟩


-- --------------------------------------------------------------------------
--
-- Additional example terms corresponding to S4 theorems


-- S4: □(□A ⊃ □B ⊃ □(A ∧ B))
tE14a : ∀{x y A B}
    → ⊩  𝜆 𝜆 𝑝²⟨ 𝑣 1 , 𝑣 0 ⟩  ∶  (x ∶ A ⊃ y ∶ B ⊃ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
tE14a = 𝝀² 𝝀² 𝒑³⟨ 𝒗 𝟏 , 𝒗 𝟎 ⟩

-- S4: □(□A ∧ □B ⊃ □□(A ∧ B))
tE14b : ∀{x y A B}
    → ⊩  𝜆 ⇑ 𝑝²⟨ 𝜋₀ 𝑣 0 , 𝜋₁ 𝑣 0 ⟩  ∶  (x ∶ A ∧ y ∶ B ⊃ ! 𝑝⟨ x , y ⟩ ∶ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
tE14b = 𝝀² ⬆² 𝒑³⟨ 𝝅₀² 𝒗 𝟎 , 𝝅₁² 𝒗 𝟎 ⟩

-- S4: □(□A ∧ □B ⊃ □(A ∧ B))
tE14c : ∀{x y A B}
    → ⊩  𝜆 𝑝²⟨ 𝜋₀ 𝑣 0 , 𝜋₁ 𝑣 0 ⟩  ∶  (x ∶ A ∧ y ∶ B ⊃ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
tE14c = 𝝀² 𝒑³⟨ 𝝅₀² 𝒗 𝟎 , 𝝅₁² 𝒗 𝟎 ⟩


-- --------------------------------------------------------------------------
--
-- Terms of example 2 (pp. 31–32 [1])


tE2 : ∀{x A}
    → ⊩  𝜆² ⇓² ⇑² 𝑣 0  ∶  𝜆 ⇓ ⇑ 𝑣 0  ∶  (x ∶ A ⊃ x ∶ A)
tE2 = 𝝀³ ⬇³ ⬆³ 𝒗 𝟎

tE2′ : ∀{x A}
    → ⊩ 𝜆² 𝑣 0  ∶  𝜆 𝑣 0  ∶  (x ∶ A ⊃ x ∶ A)
tE2′ = 𝝀³  𝒗 𝟎


-- --------------------------------------------------------------------------
--
-- Internalisation (theorem 1, p. 29 [1]; lemma 5.4, pp. 9–10 [2])


-- A₁, A₂, …, Aₘ  →  x₁ ∶ A₁, x₂ ∶ A₂, …, xₘ ∶ Aₘ
prefix : Cx → Cx
prefix ∅               = ∅
prefix (Γ , ⟨ n , A ⟩) = prefix Γ , ⟨ suc n , A ⟩


-- yₙ ∶ yₙ₋₁ ∶ … ∶ y₁ ∶ Aᵢ ∈ A₁, A₂, …, Aₘ  →  xᵢ ∶ yₙ ∶ yₙ₋₁ ∶ … ∶ y₁ ∶ Aᵢ ∈ x₁ ∶ A₁, x₂ ∶ A₂, …, xₘ ∶ Aₘ
int∈ : ∀{n x A Γ}
    → ⟨ n , A ⟩ ∈[ x ] Γ
    → ⟨ suc n , A ⟩ ∈[ x ] prefix Γ
int∈ 𝐙     = 𝐙
int∈ (𝐒 i) = 𝐒 (int∈ i)


-- A₁, A₂, …, Aₘ ⊢ B  →  x₁ ∶ A₁, x₂ ∶ A₂, … xₘ ∶ Aₘ ⊢ t(x₁, x₂, …, xₘ) ∶ B
int⊢ : ∀{B Γ}
    → Γ ⊢ B
    → Σ Tm λ t → prefix Γ ⊢ t ∶ B
int⊢ (𝒗_ {n} {k} i) =
    let j = int∈ i in
      ⟨ 𝑣 k
      , 𝒗 j
      ⟩
int⊢ (𝝀ⁿ_ {n} {𝐭} D) =
    let ⟨ s , C ⟩ = int⊢ D in
      ⟨ 𝜆[ suc n ] s
      , 𝝀ⁿ_ {𝐭 = s ∷ 𝐭} C
      ⟩
int⊢ (_∙ⁿ_ {n} {𝐭} {𝐬} D₀ D₁) =
    let ⟨ s₀ , C₀ ⟩ = int⊢ D₀
        ⟨ s₁ , C₁ ⟩ = int⊢ D₁ in
      ⟨ s₀ ∘[ suc n ] s₁
      , _∙ⁿ_ {𝐭 = s₀ ∷ 𝐭} {𝐬 = s₁ ∷ 𝐬} C₀ C₁
      ⟩
int⊢ (𝒑ⁿ⟨_,_⟩ {n} {𝐭} {𝐬} D₀ D₁) =
    let ⟨ s₀ , C₀ ⟩ = int⊢ D₀
        ⟨ s₁ , C₁ ⟩ = int⊢ D₁ in
      ⟨ 𝑝[ suc n ]⟨ s₀ , s₁ ⟩
      , 𝒑ⁿ⟨_,_⟩ {𝐭 = s₀ ∷ 𝐭} {𝐬 = s₁ ∷ 𝐬} C₀ C₁
      ⟩
int⊢ (𝝅₀ⁿ_ {n} {𝐭} D) =
    let ⟨ s , C ⟩ = int⊢ D in
      ⟨ 𝜋₀[ suc n ] s
      , 𝝅₀ⁿ_ {𝐭 = s ∷ 𝐭} C
      ⟩
int⊢ (𝝅₁ⁿ_ {n} {𝐭} D) =
    let ⟨ s , C ⟩ = int⊢ D in
      ⟨ 𝜋₁[ suc n ] s
      , 𝝅₁ⁿ_ {𝐭 = s ∷ 𝐭} C
      ⟩
int⊢ (⬆ⁿ_ {n} {𝐭} D) =
    let ⟨ s , C ⟩ = int⊢ D in
      ⟨ ⇑[ suc n ] s
      , ⬆ⁿ_ {𝐭 = s ∷ 𝐭} C
      ⟩
int⊢ (⬇ⁿ_ {n} {𝐭} D) =
    let ⟨ s , C ⟩ = int⊢ D in
      ⟨ ⇓[ suc n ] s
      , ⬇ⁿ_ {𝐭 = s ∷ 𝐭} C
      ⟩


-- --------------------------------------------------------------------------
--
-- Constructive necessitation (corollary 5.5, p. 10 [2])


-- ⊩ B  →  ⊩ t ∶ B
nec : ∀{B}
    → ⊩ B
    → Σ Tm λ t → ⊩ t ∶ B
nec = int⊢


-- --------------------------------------------------------------------------
--
-- Example necessitated terms at levels 2, 3, and 4


-- A ⊃ A
tI′ : ∀{A}
    → ⊩  A ⊃ A
tI′ = tI

-- 𝜆 𝑣 0  ∶  (A ⊃ A)
tI²′ : ∀{A} → Σ Tm λ t
    → ⊩  t  ∶  (A ⊃ A)
tI²′ = nec tI

-- 𝜆² 𝑣 0  ∶  𝜆 𝑣 0  ∶  (A ⊃ A)
tI³′ : ∀{A} → Σ Tm λ t
    → ⊩  t  ∶  𝜆 𝑣 0  ∶  (A ⊃ A)
tI³′ = nec (proj₁ tI²′)

-- 𝜆³ 𝑣 0  ∶  𝜆² v 0  ∶  𝜆 𝑣 0  ∶  (A ⊃ A)
tI⁴′ : ∀{A} → Σ Tm λ t
    → ⊩  t  ∶  𝜆² 𝑣 0  ∶  𝜆 𝑣 0  ∶  (A ⊃ A)
tI⁴′ = nec (proj₁ tI³′)


-- A ⊃ B ⊃ A
tK′ : ∀{A B}
    → ⊩  A ⊃ B ⊃ A
tK′ = tK

-- 𝜆 𝜆 𝑣 1  ∶  (A ⊃ B ⊃ A)
tK²′ : ∀{A B} → Σ Tm λ t
    → ⊩  t  ∶  (A ⊃ B ⊃ A)
tK²′ = nec tK

-- 𝜆² 𝜆² 𝑣 1  ∶  𝜆 𝜆 𝑣 1  ∶  (A ⊃ B ⊃ A)
tK³′ : ∀{A B} → Σ Tm λ t
    → ⊩  t  ∶  𝜆 𝜆 𝑣 1  ∶  (A ⊃ B ⊃ A)
tK³′ = nec (proj₁ tK²′)

-- 𝜆³ 𝜆³ 𝑣 1  ∶  𝜆² 𝜆² 𝑣 1  ∶  𝜆 𝜆 𝑣 1  ∶  (A ⊃ B ⊃ A)
tK⁴′ : ∀{A B} → Σ Tm λ t
    → ⊩  t  ∶  𝜆² 𝜆² 𝑣 1  ∶  𝜆 𝜆 𝑣 1  ∶  (A ⊃ B ⊃ A)
tK⁴′ = nec (proj₁ tK³′)


-- (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
tS′ : ∀{A B C}
    → ⊩  (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
tS′ = tS

-- 𝜆 𝜆 𝜆 (𝑣 2 ∘ 𝑣 0) ∘ (𝑣 1 ∘ 𝑣 0)  ∶  ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
tS²′ : ∀{A B C} → Σ Tm λ t
    → ⊩  t  ∶  ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
tS²′ = nec tS

-- 𝜆² 𝜆² 𝜆² (𝑣 2 ∘² 𝑣 0) ∘² (𝑣 1 ∘² 𝑣 0)  ∶  𝜆 𝜆 𝜆 (𝑣 2 ∘ 𝑣 0) ∘ (𝑣 1 ∘ 𝑣 0)  ∶  ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
tS³′ : ∀{A B C} → Σ Tm λ t
    → ⊩  t  ∶  𝜆 𝜆 𝜆 (𝑣 2 ∘ 𝑣 0) ∘ (𝑣 1 ∘ 𝑣 0)  ∶  ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
tS³′ = nec (proj₁ tS²′)

-- 𝜆³ 𝜆³ 𝜆³ (𝑣 2 ∘³ 𝑣 0) ∘³ (𝑣 1 ∘³ 𝑣 0)  ∶  𝜆² 𝜆² 𝜆² (𝑣 2 ∘² 𝑣 0) ∘² (𝑣 1 ∘² 𝑣 0)  ∶  𝜆 𝜆 𝜆 (𝑣 2 ∘ 𝑣 0) ∘ (𝑣 1 ∘ 𝑣 0)  ∶  ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
tS⁴′ : ∀{A B C} → Σ Tm λ t
    → ⊩  t  ∶  𝜆² 𝜆² 𝜆² (𝑣 2 ∘² 𝑣 0) ∘² (𝑣 1 ∘² 𝑣 0)  ∶  𝜆 𝜆 𝜆 (𝑣 2 ∘ 𝑣 0) ∘ (𝑣 1 ∘ 𝑣 0)  ∶  ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
tS⁴′ = nec (proj₁ tS³′)
