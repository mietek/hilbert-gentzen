module Scratch-variables where

{-

{-

An extension of reflective λ-calculus
=====================================

A work-in-progress implementation of the Alt-Artëmov system λ∞,
extended with disjunction and falsehood.

For easy editing with Emacs agda-mode, add to your .emacs file:

'(agda-input-user-translations
   (quote
    (("i" "⊃") ("ii" "⫗") ("e" "⊢") ("ee" "⊩") ("n" "¬") (":." "∵")
     ("v" "𝑣") ("v2" "𝑣²") ("v3" "𝑣³") ("v4" "𝑣⁴") ("vn" "𝑣ⁿ")
     ("l" "𝜆") ("l2" "𝜆²") ("l3" "𝜆³") ("l4" "𝜆⁴") ("ln" "𝜆ⁿ")
     ("o" "∘") ("o2" "∘²") ("o3" "∘³") ("o4" "∘⁴") ("on" "∘ⁿ")
     ("p" "𝑝") ("p2" "𝑝²") ("p3" "𝑝³") ("p4" "𝑝⁴") ("pn" "𝑝ⁿ")
     ("pi" "𝜋")
     ("pi0" "𝜋₀") ("pi02" "𝜋₀²") ("pi03" "𝜋₀³") ("pi04" "𝜋₀⁴") ("pi0n" "𝜋₀ⁿ")
     ("pi1" "𝜋₁") ("pi12" "𝜋₁²") ("pi13" "𝜋₁³") ("pi14" "𝜋₁⁴") ("pi1n" "𝜋₁ⁿ")
     ("io" "𝜄")
     ("io0" "𝜄₀") ("io02" "𝜄₀²") ("io03" "𝜄₀³") ("io04" "𝜄₀⁴") ("io0n" "𝜄₀ⁿ")
     ("io1" "𝜄₁") ("io12" "𝜄₁²") ("io13" "𝜄₁³") ("io14" "𝜄₁⁴") ("io1n" "𝜄₁ⁿ")
     ("c" "𝑐") ("c2" "𝑐²") ("c3" "𝑐³") ("c4" "𝑐⁴") ("cn" "𝑐ⁿ")
     ("u" "⇑") ("u2" "⇑²") ("u3" "⇑³") ("u4" "⇑⁴") ("un" "⇑ⁿ")
     ("d" "⇓") ("d2" "⇓²") ("d3" "⇓³") ("d4" "⇓⁴") ("dn" "⇓ⁿ")
     ("x" "☆") ("x2" "☆²") ("x3" "☆³") ("x4" "☆⁴") ("xn" "☆ⁿ")
     ("b" "□")
     ("mv" "𝒗") ("mv2" "𝒗²") ("mv3" "𝒗³") ("mv4" "𝒗⁴") ("mvn" "𝒗ⁿ")
     ("ml" "𝝀") ("ml2" "𝝀²") ("ml3" "𝝀³") ("ml4" "𝝀⁴") ("mln" "𝝀ⁿ")
     ("mo" "∙") ("mo2" "∙²") ("mo3" "∙³") ("mo4" "∙⁴") ("mon" "∙ⁿ")
     ("mp" "𝒑") ("mp2" "𝒑²") ("mp3" "𝒑³") ("mp4" "𝒑⁴") ("mpn" "𝒑ⁿ")
     ("mpi" "𝝅")
     ("mpi0" "𝝅₀") ("mpi02" "𝝅₀²") ("mpi03" "𝝅₀³") ("mpi04" "𝝅₀⁴") ("mpi0n" "𝝅₀ⁿ")
     ("mpi1" "𝝅₁") ("mpi12" "𝝅₁²") ("mpi13" "𝝅₁³") ("mpi14" "𝝅₁⁴") ("mpi1n" "𝝅₁ⁿ")
     ("mi" "𝜾")
     ("mi0" "𝜾₀") ("mi02" "𝜾₀²") ("mi03" "𝜾₀³") ("mi04" "𝜾₀⁴") ("mi0n" "𝜾₀ⁿ")
     ("mi1" "𝜾₁") ("mi12" "𝜾₁²") ("mi13" "𝜾₁³") ("mi14" "𝜾₁⁴") ("mi1n" "𝜾₁ⁿ")
     ("mc" "𝒄") ("mc2" "𝒄²") ("mc3" "𝒄³") ("mc4" "𝒄⁴") ("mcn" "𝒄ⁿ")
     ("mu" "⬆") ("mu2" "⬆²") ("mu3" "⬆³") ("mu4" "⬆⁴") ("mun" "⬆ⁿ")
     ("md" "⬇") ("md2" "⬇²") ("md3" "⬇³") ("md4" "⬇⁴") ("mdn" "⬇ⁿ")
     ("mx" "★") ("mx2" "★²") ("mx3" "★³") ("mx4" "★⁴") ("mxn" "★ⁿ")
     ("mb" "■")
     ("mS" "𝐒") ("mZ" "𝐙")
     ("m0" "𝟎") ("m1" "𝟏") ("m2" "𝟐") ("m3" "𝟑") ("m4" "𝟒")
     ("ss" "𝐬") ("ts" "𝐭") ("us" "𝐮") ("xs" "𝐱") ("ys" "𝐲") ("zs" "𝐳")
     ("C" "𝒞") ("D" "𝒟") ("E" "ℰ")
     ("N" "ℕ"))))

-}


module Scratch-variables where

open import Data.Nat using (ℕ ; zero ; suc ; pred ; _⊔_ )
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)

infixl 9 !_
infixl 9 𝑣_ 𝑣²_ 𝑣³_ 𝑣⁴_ 𝑣ⁿ_ 𝒗_ 𝒗²_ 𝒗³_ 𝒗⁴_ 𝒗ⁿ_
infixl 9 ☆_ ☆²_ ☆³_ ☆⁴_ ☆ⁿ_ ★_ ★²_ ★³_ ★⁴_ ★ⁿ_
infixl 8 𝜋₀_ 𝜋₀²_ 𝜋₀³_ 𝜋₀⁴_ 𝜋₀ⁿ_ 𝝅₀_ 𝝅₀²_ 𝝅₀³_ 𝝅₀⁴_ 𝝅₀ⁿ_
infixl 8 𝜋₁_ 𝜋₁²_ 𝜋₁³_ 𝜋₁⁴_ 𝜋₁ⁿ_ 𝝅₁_ 𝝅₁²_ 𝝅₁³_ 𝝅₁⁴_ 𝝅₁ⁿ_
infixl 8 𝜄₀_ 𝜄₀²_ 𝜄₀³_ 𝜄₀⁴_ 𝜄₀ⁿ_ 𝜾₀_ 𝜾₀²_ 𝜾₀³_ 𝜾₀⁴_ 𝜾₀ⁿ_
infixl 8 𝜄₁_ 𝜄₁²_ 𝜄₁³_ 𝜄₁⁴_ 𝜄₁ⁿ_ 𝜾₁_ 𝜾₁²_ 𝜾₁³_ 𝜾₁⁴_ 𝜾₁ⁿ_
infixl 7 _∘_ _∘²_ _∘³_ _∘⁴_ _∘ⁿ_ _∙_ _∙²_ _∙³_ _∙⁴_ _∙ⁿ_
infixr 6 ⇑_ ⇑²_ ⇑³_ ⇑⁴_ ⇑ⁿ_ ⬆_ ⬆²_ ⬆³_ ⬆⁴_ ⬆ⁿ_
infixr 6 ⇓_ ⇓²_ ⇓³_ ⇓⁴_ ⇓ⁿ_ ⬇_ ⬇²_ ⬇³_ ⬇⁴_ ⬇ⁿ_
infixr 5 𝜆_ 𝜆²_ 𝜆³_ 𝜆⁴_ 𝜆ⁿ_ 𝝀_ 𝝀²_ 𝝀³_ 𝝀⁴_ 𝝀ⁿ_
infixr 5 _∶_ _∵_ _∷_
infixr 4 ¬_
infixl 4 _∧_
infixl 3 _∨_ _,_ _„_
infixr 2 _⊃_
infixr 1 _⫗_
infixr 0 _[_]⊢_ ⊩_


-- --------------------------------------------------------------------------
--
-- Untyped syntax


-- Term constructors with variable count
data Tm : ℕ → Set where
  -- Variable reference at level n
  𝑣[_]_ : ℕ → (x : ℕ) → Tm (suc x)

  -- Abstraction (⊃I) at level n
  𝜆[_]_ : ∀{x} → ℕ → Tm x → Tm (pred x)

  -- Application (⊃E) at level n
  _∘[_]_ : ∀{x y} → Tm x → ℕ → Tm y → Tm (x ⊔ y)

  -- Pair (∧I) at level n
  𝑝[_]⟨_,_⟩ : ∀{x y} → ℕ → Tm x → Tm y → Tm (x ⊔ y)

  -- 0th projection (∧E₀) at level n
  𝜋₀[_]_ : ∀{x} → ℕ → Tm x → Tm x

  -- 1st projection (∧E₁) at level n
  𝜋₁[_]_ : ∀{x} → ℕ → Tm x → Tm x

  -- 0th injection (∨I₀) at level n
  𝜄₀[_]_ : ∀{x} → ℕ → Tm x → Tm x

  -- 1st injection (∨I₁) at level n
  𝜄₁[_]_ : ∀{x} → ℕ → Tm x → Tm x

  -- Case split (∨E) at level n
  𝑐[_][_▷_∣_] : ∀{x y z} → ℕ → Tm x → Tm y → Tm z → Tm (x ⊔ pred y ⊔ pred z)

  -- Artëmov’s “proof checker”
  !_ : ∀{x} → Tm x → Tm x

  -- Reification at level n
  ⇑[_]_ : ∀{x} → ℕ → Tm x → Tm x

  -- Reflection at level n
  ⇓[_]_ : ∀{x} → ℕ → Tm x → Tm x

  -- Explosion (⊥E) at level n
  ☆[_]_ : ∀{x} → ℕ → Tm x → Tm x


-- Type constructors
data Ty : Set where
  -- Implication
  _⊃_ : Ty → Ty → Ty

  -- Conjunction
  _∧_ : Ty → Ty → Ty

  -- Disjunction
  _∨_ : Ty → Ty → Ty

  -- Explicit provability
  _∶_ : ∀{x} → Tm x → Ty → Ty

  -- Falsehood
  ⊥ : Ty


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


𝑣_ : (x : ℕ) → Tm (suc x)
𝑣 x = 𝑣[ 1 ] x

𝜆_ : ∀{x} → Tm x → Tm (pred x)
𝜆 t = 𝜆[ 1 ] t

_∘_ : ∀{x y} → Tm x → Tm y → Tm (x ⊔ y)
t ∘ s = t ∘[ 1 ] s

𝑝⟨_,_⟩ : ∀{x y} → Tm x → Tm y → Tm (x ⊔ y)
𝑝⟨ t , s ⟩ = 𝑝[ 1 ]⟨ t , s ⟩

𝜋₀_ : ∀{x} → Tm x → Tm x
𝜋₀ t = 𝜋₀[ 1 ] t

𝜋₁_ : ∀{x} → Tm x → Tm x
𝜋₁ t = 𝜋₁[ 1 ] t

𝜄₀_ : ∀{x} → Tm x → Tm x
𝜄₀ t = 𝜄₀[ 1 ] t

𝜄₁_ : ∀{x} → Tm x → Tm x
𝜄₁ t = 𝜄₁[ 1 ] t

𝑐[_▷_∣_] : ∀{x y z} → Tm x → Tm y → Tm z → Tm (x ⊔ pred y ⊔ pred z)
𝑐[ t ▷ s ∣ r ] = 𝑐[ 1 ][ t ▷ s ∣ r ]

⇑_ : ∀{x} → Tm x → Tm x
⇑ t = ⇑[ 1 ] t

⇓_ : ∀{x} → Tm x → Tm x
⇓ t = ⇓[ 1 ] t

☆_ : ∀{x} → Tm x → Tm x
☆ t = ☆[ 1 ] t


-- --------------------------------------------------------------------------
--
-- Notation for term constructors at level 2


𝑣²_ : (x : ℕ) → Tm (suc x)
𝑣² x = 𝑣[ 2 ] x

𝜆²_ : ∀{x} → Tm x → Tm (pred x)
𝜆² t₂ = 𝜆[ 2 ] t₂

_∘²_ : ∀{x y} → Tm x → Tm y → Tm (x ⊔ y)
t₂ ∘² s₂ = t₂ ∘[ 2 ] s₂

𝑝²⟨_,_⟩ : ∀{x y} → Tm x → Tm y → Tm (x ⊔ y)
𝑝²⟨ t₂ , s₂ ⟩ = 𝑝[ 2 ]⟨ t₂ , s₂ ⟩

𝜋₀²_ : ∀{x} → Tm x → Tm x
𝜋₀² t₂ = 𝜋₀[ 2 ] t₂

𝜋₁²_ : ∀{x} → Tm x → Tm x
𝜋₁² t₂ = 𝜋₁[ 2 ] t₂

𝜄₀²_ : ∀{x} → Tm x → Tm x
𝜄₀² t₂ = 𝜄₀[ 2 ] t₂

𝜄₁²_ : ∀{x} → Tm x → Tm x
𝜄₁² t₂ = 𝜄₁[ 2 ] t₂

𝑐²[_▷_∣_] : ∀{x y z} → Tm x → Tm y → Tm z → Tm (x ⊔ pred y ⊔ pred z)
𝑐²[ t₂ ▷ s₂ ∣ r₂ ] = 𝑐[ 2 ][ t₂ ▷ s₂ ∣ r₂ ]

⇑²_ : ∀{x} → Tm x → Tm x
⇑² t₂ = ⇑[ 2 ] t₂

⇓²_ : ∀{x} → Tm x → Tm x
⇓² t₂ = ⇓[ 2 ] t₂

☆²_ : ∀{x} → Tm x → Tm x
☆² t = ☆[ 2 ] t


-- --------------------------------------------------------------------------
--
-- Notation for term constructors at level 3


𝑣³_ : (x : ℕ) → Tm (suc x)
𝑣³ x = 𝑣[ 3 ] x

𝜆³_ : ∀{x} → Tm x → Tm (pred x)
𝜆³ t₃ = 𝜆[ 3 ] t₃

_∘³_ : ∀{x y} → Tm x → Tm y → Tm (x ⊔ y)
t₃ ∘³ s₃ = t₃ ∘[ 3 ] s₃

𝑝³⟨_,_⟩ : ∀{x y} → Tm x → Tm y → Tm (x ⊔ y)
𝑝³⟨ t₃ , s₃ ⟩ = 𝑝[ 3 ]⟨ t₃ , s₃ ⟩

𝜋₀³_ : ∀{x} → Tm x → Tm x
𝜋₀³ t₃ = 𝜋₀[ 3 ] t₃

𝜋₁³_ : ∀{x} → Tm x → Tm x
𝜋₁³ t₃ = 𝜋₁[ 3 ] t₃

𝜄₀³_ : ∀{x} → Tm x → Tm x
𝜄₀³ t₃ = 𝜄₀[ 3 ] t₃

𝜄₁³_ : ∀{x} → Tm x → Tm x
𝜄₁³ t₃ = 𝜄₁[ 3 ] t₃

𝑐³[_▷_∣_] : ∀{x y z} → Tm x → Tm y → Tm z → Tm (x ⊔ pred y ⊔ pred z)
𝑐³[ t₃ ▷ s₃ ∣ r₃ ] = 𝑐[ 3 ][ t₃ ▷ s₃ ∣ r₃ ]

⇑³_ : ∀{x} → Tm x → Tm x
⇑³ t₃ = ⇑[ 3 ] t₃

⇓³_ : ∀{x} → Tm x → Tm x
⇓³ t₃ = ⇓[ 3 ] t₃

☆³_ : ∀{x} → Tm x → Tm x
☆³ t = ☆[ 3 ] t


-- --------------------------------------------------------------------------
--
-- Notation for term constructors at level 4


𝑣⁴_ : (x : ℕ) → Tm (suc x)
𝑣⁴ x = 𝑣[ 4 ] x

𝜆⁴_ : ∀{x} → Tm x → Tm (pred x)
𝜆⁴ t₄ = 𝜆[ 4 ] t₄

_∘⁴_ : ∀{x y} → Tm x → Tm y → Tm (x ⊔ y)
t₄ ∘⁴ s₄ = t₄ ∘[ 4 ] s₄

𝑝⁴⟨_,_⟩ : ∀{x y} → Tm x → Tm y → Tm (x ⊔ y)
𝑝⁴⟨ t₄ , s₄ ⟩ = 𝑝[ 4 ]⟨ t₄ , s₄ ⟩

𝜋₀⁴_ : ∀{x} → Tm x → Tm x
𝜋₀⁴ t₄ = 𝜋₀[ 4 ] t₄

𝜋₁⁴_ : ∀{x} → Tm x → Tm x
𝜋₁⁴ t₄ = 𝜋₁[ 4 ] t₄

𝜄₀⁴_ : ∀{x} → Tm x → Tm x
𝜄₀⁴ t₄ = 𝜄₀[ 4 ] t₄

𝜄₁⁴_ : ∀{x} → Tm x → Tm x
𝜄₁⁴ t₄ = 𝜄₁[ 4 ] t₄

𝑐⁴[_▷_∣_] : ∀{x y z} → Tm x → Tm y → Tm z → Tm (x ⊔ pred y ⊔ pred z)
𝑐⁴[ t₄ ▷ s₄ ∣ r₄ ] = 𝑐[ 4 ][ t₄ ▷ s₄ ∣ r₄ ]

⇑⁴_ : ∀{x} → Tm x → Tm x
⇑⁴ t₄ = ⇑[ 4 ] t₄

⇓⁴_ : ∀{x} → Tm x → Tm x
⇓⁴ t₄ = ⇓[ 4 ] t₄

☆⁴_ : ∀{x} → Tm x → Tm x
☆⁴ t = ☆[ 4 ] t


-- --------------------------------------------------------------------------
--
-- Example closed and open untyped terms


module Untyped where
  ′I : Tm 0
  ′I = 𝜆 𝜆 𝑣 0

  I : Tm 0
  I = 𝜆 𝑣 0

  I′ : Tm 1
  I′ = 𝑣 0

  ′K : Tm 0
  ′K = 𝜆 𝜆 𝜆 𝑣 1

  K : Tm 0
  K = 𝜆 𝜆 𝑣 1

  K′ : Tm 1
  K′ = 𝜆 𝑣 1

  K″ : Tm 2
  K″ = 𝑣 1


-- --------------------------------------------------------------------------
--
-- Vector notation for type assertions at level n (p. 27 [1])


-- Term vectors with length and variable count
data Tms : ℕ → ℕ → Set where
  []  : ∀{x} → Tms 0 x
  _∷_ : ∀{n x} → Tm x → Tms n x → Tms (suc n) x


-- tₙ ∶ tₙ₋₁ ∶ … ∶ t ∶ A
_∵_ : ∀{n x} → Tms n x → Ty → Ty
[]      ∵ A = A
(t ∷ 𝐭) ∵ A = t ∶ 𝐭 ∵ A

-- 𝑣ⁿ x ∶ 𝑣ⁿ⁻¹ x ∶ … ∶ 𝑣 x
𝑣ⁿ_ : ∀{n} → (x : ℕ) → Tms n (suc x)
𝑣ⁿ_ {zero}  x = []
𝑣ⁿ_ {suc n} x = 𝑣[ suc n ] x ∷ 𝑣ⁿ x

-- 𝜆ⁿ tₙ ∶ 𝜆ⁿ⁻¹ tₙ₋₁ ∶ … ∶ 𝜆 t
𝜆ⁿ_ : ∀{n x} → Tms n x → Tms n (pred x)
𝜆ⁿ_ {zero}  []      = []
𝜆ⁿ_ {suc n} (t ∷ 𝐭) = 𝜆[ suc n ] t ∷ 𝜆ⁿ 𝐭

-- tₙ ∘ⁿ sₙ ∶ tₙ₋₁ ∘ⁿ⁻¹ ∶ sₙ₋₁ ∶ … ∶ t ∘ s
_∘ⁿ_ : ∀{n x y} → Tms n x → Tms n y → Tms n (x ⊔ y)
_∘ⁿ_ {zero}  []      []      = []
_∘ⁿ_ {suc n} (t ∷ 𝐭) (s ∷ 𝐬) = t ∘[ suc n ] s ∷ 𝐭 ∘ⁿ 𝐬

-- 𝑝ⁿ⟨ tₙ , sₙ ⟩ ∶ 𝑝ⁿ⁻¹⟨ tₙ₋₁ , sₙ₋₁ ⟩ ∶ … ∶ p⟨ t , s ⟩
𝑝ⁿ⟨_,_⟩ : ∀{n x y} → Tms n x → Tms n y → Tms n (x ⊔ y)
𝑝ⁿ⟨_,_⟩ {zero}  []      []      = []
𝑝ⁿ⟨_,_⟩ {suc n} (t ∷ 𝐭) (s ∷ 𝐬) = 𝑝[ suc n ]⟨ t , s ⟩ ∷ 𝑝ⁿ⟨ 𝐭 , 𝐬 ⟩

-- 𝜋₀ⁿ tₙ ∶ 𝜋₀ⁿ⁻¹ tₙ₋₁ ∶ … ∶ 𝜋₀ t
𝜋₀ⁿ_ : ∀{n x} → Tms n x → Tms n x
𝜋₀ⁿ_ {zero}  []      = []
𝜋₀ⁿ_ {suc n} (t ∷ 𝐭) = 𝜋₀[ suc n ] t ∷ 𝜋₀ⁿ 𝐭

-- 𝜋₁ⁿ tₙ ∶ 𝜋₁ⁿ⁻¹ tₙ₋₁ ∶ … ∶ 𝜋₁ t
𝜋₁ⁿ_ : ∀{n x} → Tms n x → Tms n x
𝜋₁ⁿ_ {zero}  []      = []
𝜋₁ⁿ_ {suc n} (t ∷ 𝐭) = 𝜋₁[ suc n ] t ∷ 𝜋₁ⁿ 𝐭

-- 𝜄₀ⁿ tₙ ∶ 𝜄₀ⁿ⁻¹ tₙ₋₁ ∶ … ∶ 𝜄₀ t
𝜄₀ⁿ_ : ∀{n x} → Tms n x → Tms n x
𝜄₀ⁿ_ {zero}  []      = []
𝜄₀ⁿ_ {suc n} (t ∷ 𝐭) = 𝜄₀[ suc n ] t ∷ 𝜄₀ⁿ 𝐭

-- 𝜄₁ⁿ tₙ ∶ 𝜄₁ⁿ⁻¹ tₙ₋₁ ∶ … ∶ 𝜄₁ t
𝜄₁ⁿ_ : ∀{n x} → Tms n x → Tms n x
𝜄₁ⁿ_ {zero}  []      = []
𝜄₁ⁿ_ {suc n} (t ∷ 𝐭) = 𝜄₁[ suc n ] t ∷ 𝜄₁ⁿ 𝐭

-- 𝑐ⁿ[ tₙ ▷ sₙ ∣ rₙ ] ∶ 𝑐ⁿ⁻¹[ tₙ₋₁ ▷ sₙ₋₁ ∣ rₙ₋₁ ] ∶ … ∶ 𝑐[ t ▷ s ∣ r ]
𝑐ⁿ[_▷_∣_] : ∀{n x y z} → Tms n x → Tms n y → Tms n z → Tms n (x ⊔ pred y ⊔ pred z)
𝑐ⁿ[_▷_∣_] {zero}  []      []      []      = []
𝑐ⁿ[_▷_∣_] {suc n} (t ∷ 𝐭) (s ∷ 𝐬) (u ∷ 𝐮) = 𝑐[ suc n ][ t ▷ s ∣ u ] ∷ 𝑐ⁿ[ 𝐭 ▷ 𝐬 ∣ 𝐮 ]

-- ⇑ⁿ tₙ ∶ ⇑ⁿ⁻¹ tₙ₋₁ ∶ … ∶ ⇑ t
⇑ⁿ_ : ∀{n x} → Tms n x → Tms n x
⇑ⁿ_ {zero}  []      = []
⇑ⁿ_ {suc n} (t ∷ 𝐭) = ⇑[ suc n ] t ∷ ⇑ⁿ 𝐭

-- ⇓ⁿ tₙ ∶ ⇑ⁿ⁻¹ tₙ₋₁ ∶ … ∶ ⇑ t
⇓ⁿ_ : ∀{n x} → Tms n x → Tms n x
⇓ⁿ_ {zero}  []      = []
⇓ⁿ_ {suc n} (t ∷ 𝐭) = ⇓[ suc n ] t ∷ ⇓ⁿ 𝐭

-- ☆ⁿ tₙ ∶ ☆ⁿ⁻¹ tₙ₋₁ ∶ … ∶ ☆ t
☆ⁿ_ : ∀{n x} → Tms n x → Tms n x
☆ⁿ_ {zero}  []      = []
☆ⁿ_ {suc n} (t ∷ 𝐭) = ☆[ suc n ] t ∷ ☆ⁿ 𝐭


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

_„_ : Cx → Cx → Cx
Γ „ ∅       = Γ
Γ „ (Δ , A) = Γ „ Δ , A


-- Context membership evidence
data _∈[_]_ : Hyp → ℕ → Cx → Set where
  𝐙 : ∀{A Γ}
      → A ∈[ zero ] (Γ , A)

  𝐒_ : ∀{x A B Γ}
      → A ∈[ x ] Γ
      → A ∈[ suc x ] (Γ , B)


-- Typed terms with variable count
data _[_]⊢_ (Γ : Cx) : ℕ → Ty → Set where
  -- Variable reference
  𝒗ⁿ_ : ∀{n x A}
      → ⟨ n , A ⟩ ∈[ x ] Γ
      → Γ [ suc x ]⊢ 𝑣ⁿ_ {n} x ∵ A

  -- Abstraction (⊃I) at level n
  𝝀ⁿ_ : ∀{n x} {𝐭 : Tms n x} {A B}
      → Γ , ⟨ n , A ⟩ [ x ]⊢ 𝐭 ∵ B
      → Γ [ pred x ]⊢ 𝜆ⁿ 𝐭 ∵ (A ⊃ B)

  -- Application (⊃E) at level n
  _∙ⁿ_ : ∀{n x y} {𝐭 : Tms n x} {𝐬 : Tms n y} {A B}
      → Γ [ x ]⊢ 𝐭 ∵ (A ⊃ B)    → Γ [ y ]⊢ 𝐬 ∵ A
      → Γ [ x ⊔ y ]⊢ 𝐭 ∘ⁿ 𝐬 ∵ B

  -- Pair (∧I) at level n
  𝒑ⁿ⟨_,_⟩ : ∀{n x y} {𝐭 : Tms n x} {𝐬 : Tms n y} {A B}
      → Γ [ x ]⊢ 𝐭 ∵ A          → Γ [ y ]⊢ 𝐬 ∵ B
      → Γ [ x ⊔ y ]⊢ 𝑝ⁿ⟨ 𝐭 , 𝐬 ⟩ ∵ (A ∧ B)

  -- 0th projection (∧E₀) at level n
  𝝅₀ⁿ_ : ∀{n x} {𝐭 : Tms n x} {A B}
      → Γ [ x ]⊢ 𝐭 ∵ (A ∧ B)
      → Γ [ x ]⊢ 𝜋₀ⁿ 𝐭 ∵ A

  -- 1st projection (∧E₁) at level n
  𝝅₁ⁿ_ : ∀{n x} {𝐭 : Tms n x} {A B}
      → Γ [ x ]⊢ 𝐭 ∵ (A ∧ B)
      → Γ [ x ]⊢ 𝜋₁ⁿ 𝐭 ∵ B

  -- 0th injection (∨I₀) at level n
  𝜾₀ⁿ_ : ∀{n x} {𝐭 : Tms n x} {A B}
      → Γ [ x ]⊢ 𝐭 ∵ A
      → Γ [ x ]⊢ 𝜄₀ⁿ 𝐭 ∵ (A ∨ B)

  -- 1st injection (∨I₁) at level n
  𝜾₁ⁿ_ : ∀{n x} {𝐭 : Tms n x} {A B}
      → Γ [ x ]⊢ 𝐭 ∵ B
      → Γ [ x ]⊢ 𝜄₁ⁿ 𝐭 ∵ (A ∨ B)

  -- Case split (∨E) at level n
  𝒄ⁿ[_▷_∣_] : ∀{n x y z} {𝐭 : Tms n x} {𝐬 : Tms n y} {𝐮 : Tms n z} {A B C}
      → Γ [ x ]⊢ 𝐭 ∵ (A ∨ B)    → Γ , ⟨ n , A ⟩ [ y ]⊢ 𝐬 ∵ C
                                  → Γ , ⟨ n , B ⟩ [ z ]⊢ 𝐮 ∵ C
      → Γ [ x ⊔ pred y ⊔ pred z ]⊢ 𝑐ⁿ[ 𝐭 ▷ 𝐬 ∣ 𝐮 ] ∵ C

  -- Reification at level n
  ⬆ⁿ_ : ∀{n x} {𝐭 : Tms n x} {u : Tm x} {A}
      → Γ [ x ]⊢ 𝐭 ∵ (u ∶ A)
      → Γ [ x ]⊢ ⇑ⁿ 𝐭 ∵ (! u ∶ u ∶ A)

  -- Reflection at level n
  ⬇ⁿ_ : ∀{n x} {𝐭 : Tms n x} {u : Tm x} {A}
      → Γ [ x ]⊢ 𝐭 ∵ (u ∶ A)
      → Γ [ x ]⊢ ⇓ⁿ 𝐭 ∵ A

  -- Explosion (⊥E)
  ★ⁿ_ : ∀{n x} {𝐭 : Tms n x} {A}
      → Γ [ x ]⊢ 𝐭 ∵ ⊥
      → Γ [ x ]⊢ ☆ⁿ 𝐭 ∵ A


-- Closed typed terms
⊩_  : Ty → Set
⊩ A = ∀{Γ} → Γ [ 0 ]⊢ A


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


-- --------------------------------------------------------------------------
--
-- Notation for typed terms at level 1


𝒗_ : ∀{x A Γ}
    → ⟨ 0 , A ⟩ ∈[ x ] Γ
    → Γ [ suc x ]⊢ A
𝒗_ = 𝒗ⁿ_

𝝀_ : ∀{x A B Γ}
    → Γ , ⟨ 0 , A ⟩ [ x ]⊢ B
    → Γ [ pred x ]⊢ A ⊃ B
𝝀_ {x} =
    𝝀ⁿ_ {x = x} {𝐭 = []}

_∙_ : ∀{x y A B Γ}
    → Γ [ x ]⊢ A ⊃ B    → Γ [ y ]⊢ A
    → Γ [ x ⊔ y ]⊢ B
_∙_ {x} {y} =
    _∙ⁿ_ {x = x} {y = y} {𝐭 = []} {𝐬 = []}

𝒑⟨_,_⟩ : ∀{x y A B Γ}
    → Γ [ x ]⊢ A        → Γ [ y ]⊢ B
    → Γ [ x ⊔ y ]⊢ A ∧ B
𝒑⟨_,_⟩ {x} {y} =
    𝒑ⁿ⟨_,_⟩ {x = x} {y = y} {𝐭 = []} {𝐬 = []}

𝝅₀_ : ∀{x A B Γ}
    → Γ [ x ]⊢ A ∧ B
    → Γ [ x ]⊢ A
𝝅₀_ {x} =
    𝝅₀ⁿ_ {x = x} {𝐭 = []}

𝝅₁_ : ∀{x A B Γ}
    → Γ [ x ]⊢ A ∧ B
    → Γ [ x ]⊢ B
𝝅₁_ {x} =
    𝝅₁ⁿ_ {x = x} {𝐭 = []}

𝜾₀_ : ∀{x A B Γ}
    → Γ [ x ]⊢ A
    → Γ [ x ]⊢ A ∨ B
𝜾₀_ {x} =
    𝜾₀ⁿ_ {x = x} {𝐭 = []}

𝜾₁_ : ∀{x A B Γ}
    → Γ [ x ]⊢ B
    → Γ [ x ]⊢ A ∨ B
𝜾₁_ {x} =
    𝜾₁ⁿ_ {x = x} {𝐭 = []}

𝒄[_▷_∣_] : ∀{x y z A B C Γ}
    → Γ [ x ]⊢ A ∨ B    → Γ , ⟨ 0 , A ⟩ [ y ]⊢ C
                          → Γ , ⟨ 0 , B ⟩ [ z ]⊢ C
    → Γ [ x ⊔ pred y ⊔ pred z ]⊢ C
𝒄[_▷_∣_] {x} {y} {z} =
    𝒄ⁿ[_▷_∣_] {x = x} {y = y}
                              {z = z} {𝐭 = []} {𝐬 = []}
                                               {𝐮 = []}

⬆_ : ∀{x} {u : Tm x} {A Γ}
    → Γ [ x ]⊢ u ∶ A
    → Γ [ x ]⊢ ! u ∶ u ∶ A
⬆_ {x} =
    ⬆ⁿ_ {x = x} {𝐭 = []}

⬇_ : ∀{x} {u : Tm x} {A Γ}
    → Γ [ x ]⊢ u ∶ A
    → Γ [ x ]⊢ A
⬇_ {x} =
    ⬇ⁿ_ {x = x} {𝐭 = []}

★_ : ∀{x A Γ}
    → Γ [ x ]⊢ ⊥
    → Γ [ x ]⊢ A
★_ {x} =
    ★ⁿ_ {x = x} {𝐭 = []}


-- --------------------------------------------------------------------------
--
-- Notation for typed terms at level 2


𝒗²_ : ∀{x A Γ}
    → ⟨ 1 , A ⟩ ∈[ x ] Γ
    → Γ [ suc x ]⊢ 𝑣 x ∶ A
𝒗²_ = 𝒗ⁿ_

𝝀²_ : ∀{x} {t : Tm x} {A B Γ}
    → Γ , ⟨ 1 , A ⟩ [ x ]⊢ t ∶ B
    → Γ [ pred x ]⊢ 𝜆 t ∶ (A ⊃ B)
𝝀²_ {t = t} =
    𝝀ⁿ_ {𝐭 = t ∷ []}

_∙²_ : ∀{x y} {t : Tm x} {s : Tm y} {A B Γ}
    → Γ [ x ]⊢ t ∶ (A ⊃ B)    → Γ [ y ]⊢ s ∶ A
    → Γ [ x ⊔ y ]⊢ t ∘ s ∶ B
_∙²_ {t = t} {s} =
    _∙ⁿ_ {𝐭 = t ∷ []} {𝐬 = s ∷ []}

𝒑²⟨_,_⟩ : ∀{x y} {t : Tm x} {s : Tm y} {A B Γ}
    → Γ [ x ]⊢ t ∶ A          → Γ [ y ]⊢ s ∶ B
    → Γ [ x ⊔ y ]⊢ 𝑝⟨ t , s ⟩ ∶ (A ∧ B)
𝒑²⟨_,_⟩ {t = t} {s} =
    𝒑ⁿ⟨_,_⟩ {𝐭 = t ∷ []} {𝐬 = s ∷ []}

𝝅₀²_ : ∀{x} {t : Tm x} {A B Γ}
    → Γ [ x ]⊢ t ∶ (A ∧ B)
    → Γ [ x ]⊢ 𝜋₀ t ∶ A
𝝅₀²_ {t = t} =
    𝝅₀ⁿ_ {𝐭 = t ∷ []}

𝝅₁²_ : ∀{x} {t : Tm x} {A B Γ}
    → Γ [ x ]⊢ t ∶ (A ∧ B)
    → Γ [ x ]⊢ 𝜋₁ t ∶ B
𝝅₁²_ {t = t} =
    𝝅₁ⁿ_ {𝐭 = t ∷ []}

𝜾₀²_ : ∀{x} {t : Tm x} {A B Γ}
    → Γ [ x ]⊢ t ∶ A
    → Γ [ x ]⊢ 𝜄₀ t ∶ (A ∨ B)
𝜾₀²_ {t = t} =
    𝜾₀ⁿ_ {𝐭 = t ∷ []}

𝜾₁²_ : ∀{x} {t : Tm x} {A B Γ}
    → Γ [ x ]⊢ t ∶ B
    → Γ [ x ]⊢ 𝜄₁ t ∶ (A ∨ B)
𝜾₁²_ {t = t} =
    𝜾₁ⁿ_ {𝐭 = t ∷ []}

𝒄²[_▷_∣_] : ∀{x y z} {t : Tm x} {s : Tm y} {u : Tm z} {A B C Γ}
    → Γ [ x ]⊢ t ∶ (A ∨ B)    → Γ , ⟨ 1 , A ⟩ [ y ]⊢ s ∶ C
                                → Γ , ⟨ 1 , B ⟩ [ z ]⊢ u ∶ C
    → Γ [ x ⊔ pred y ⊔ pred z ]⊢ 𝑐[ t ▷ s ∣ u ] ∶ C
𝒄²[_▷_∣_] {t = t} {s} {u} =
    𝒄ⁿ[_▷_∣_] {𝐭 = t ∷ []} {𝐬 = s ∷ []}
                           {𝐮 = u ∷ []}

⬆²_ : ∀{x} {t : Tm x} {u : Tm x} {A Γ}
    → Γ [ x ]⊢ t ∶ u ∶ A
    → Γ [ x ]⊢ ⇑ t ∶ ! u ∶ u ∶ A
⬆²_ {t = t} {u} =
    ⬆ⁿ_ {𝐭 = t ∷ []}

⬇²_ : ∀{x} {t : Tm x} {u : Tm x} {A Γ}
    → Γ [ x ]⊢ t ∶ u ∶ A
    → Γ [ x ]⊢ ⇓ t ∶ A
⬇²_ {t = t} {u} =
    ⬇ⁿ_ {𝐭 = t ∷ []}

★²_ : ∀{x} {t : Tm x} {A Γ}
    → Γ [ x ]⊢ t ∶ ⊥
    → Γ [ x ]⊢ ☆ t ∶ A
★²_ {t = t} =
    ★ⁿ_ {𝐭 = t ∷ []}


-- --------------------------------------------------------------------------
--
-- Notation for typed terms at level 3


𝒗³_ : ∀{x A Γ}
    → ⟨ 2 , A ⟩ ∈[ x ] Γ
    → Γ [ suc x ]⊢ 𝑣² x ∶ 𝑣 x ∶ A
𝒗³_ = 𝒗ⁿ_

𝝀³_ : ∀{x} {t₂ t : Tm x} {A B Γ}
    → Γ , ⟨ 2 , A ⟩ [ x ]⊢ t₂ ∶ t ∶ B
    → Γ [ pred x ]⊢ 𝜆² t₂ ∶ 𝜆 t ∶ (A ⊃ B)
𝝀³_ {t₂ = t₂} {t} =
    𝝀ⁿ_ {𝐭 = t₂ ∷ t ∷ []}

_∙³_ : ∀{x y} {t₂ t : Tm x} {s₂ s : Tm y} {A B Γ}
    → Γ [ x ]⊢ t₂ ∶ t ∶ (A ⊃ B)    → Γ [ y ]⊢ s₂ ∶ s ∶ A
    → Γ [ x ⊔ y ]⊢ t₂ ∘² s₂ ∶ t ∘ s ∶ B
_∙³_ {t₂ = t₂} {t} {s₂} {s} =
    _∙ⁿ_ {𝐭 = t₂ ∷ t ∷ []} {𝐬 = s₂ ∷ s ∷ []}

𝒑³⟨_,_⟩ : ∀{x y} {t₂ t : Tm x} {s₂ s : Tm y} {A B Γ}
    → Γ [ x ]⊢ t₂ ∶ t ∶ A          → Γ [ y ]⊢ s₂ ∶ s ∶ B
    → Γ [ x ⊔ y ]⊢ 𝑝²⟨ t₂ , s₂ ⟩ ∶ 𝑝⟨ t , s ⟩ ∶ (A ∧ B)
𝒑³⟨_,_⟩ {t₂ = t₂} {t} {s₂} {s} =
    𝒑ⁿ⟨_,_⟩ {𝐭 = t₂ ∷ t ∷ []} {𝐬 = s₂ ∷ s ∷ []}

𝝅₀³_ : ∀{x} {t₂ t : Tm x} {A B Γ}
    → Γ [ x ]⊢ t₂ ∶ t ∶ (A ∧ B)
    → Γ [ x ]⊢ 𝜋₀² t₂ ∶ 𝜋₀ t ∶ A
𝝅₀³_ {t₂ = t₂} {t} =
    𝝅₀ⁿ_ {𝐭 = t₂ ∷ t ∷ []}

𝝅₁³_ : ∀{x} {t₂ t : Tm x} {A B Γ}
    → Γ [ x ]⊢ t₂ ∶ t ∶ (A ∧ B)
    → Γ [ x ]⊢ 𝜋₁² t₂ ∶ 𝜋₁ t ∶ B
𝝅₁³_ {t₂ = t₂} {t} =
    𝝅₁ⁿ_ {𝐭 = t₂ ∷ t ∷ []}

𝜾₀³_ : ∀{x} {t₂ t : Tm x} {A B Γ}
    → Γ [ x ]⊢ t₂ ∶ t ∶ A
    → Γ [ x ]⊢ 𝜄₀² t₂ ∶ 𝜄₀ t ∶ (A ∨ B)
𝜾₀³_ {t₂ = t₂} {t} =
    𝜾₀ⁿ_ {𝐭 = t₂ ∷ t ∷ []}

𝜾₁³_ : ∀{x} {t₂ t : Tm x} {A B Γ}
    → Γ [ x ]⊢ t₂ ∶ t ∶ B
    → Γ [ x ]⊢ 𝜄₁² t₂ ∶ 𝜄₁ t ∶ (A ∨ B)
𝜾₁³_ {t₂ = t₂} {t} =
    𝜾₁ⁿ_ {𝐭 = t₂ ∷ t ∷ []}

𝒄³[_▷_∣_] : ∀{x y z} {t₂ t : Tm x} {s₂ s : Tm y} {u₂ u : Tm z} {A B C Γ}
    → Γ [ x ]⊢ t₂ ∶ t ∶ (A ∨ B)    → Γ , ⟨ 2 , A ⟩ [ y ]⊢ s₂ ∶ s ∶ C
                                     → Γ , ⟨ 2 , B ⟩ [ z ]⊢ u₂ ∶ u ∶ C
    → Γ [ x ⊔ pred y ⊔ pred z ]⊢ 𝑐²[ t₂ ▷ s₂ ∣ u₂ ] ∶ 𝑐[ t ▷ s ∣ u ] ∶ C
𝒄³[_▷_∣_] {t₂ = t₂} {t} {s₂} {s} {u₂} {u} =
    𝒄ⁿ[_▷_∣_] {𝐭 = t₂ ∷ t ∷ []} {𝐬 = s₂ ∷ s ∷ []}
                                {𝐮 = u₂ ∷ u ∷ []}

⬆³_ : ∀{x} {t₂ t : Tm x} {u : Tm x} {A Γ}
    → Γ [ x ]⊢ t₂ ∶ t ∶ u ∶ A
    → Γ [ x ]⊢ ⇑² t₂ ∶ ⇑ t ∶ ! u ∶ u ∶ A
⬆³_ {t₂ = t₂} {t} =
    ⬆ⁿ_ {𝐭 = t₂ ∷ t ∷ []}

⬇³_ : ∀{x} {t₂ t : Tm x} {u : Tm x} {A Γ}
    → Γ [ x ]⊢ t₂ ∶ t ∶ u ∶ A
    → Γ [ x ]⊢ ⇓² t₂ ∶ ⇓ t ∶ A
⬇³_ {t₂ = t₂} {t} =
    ⬇ⁿ_ {𝐭 = t₂ ∷ t ∷ []}

★³_ : ∀{x} {t₂ t : Tm x} {A Γ}
    → Γ [ x ]⊢ t₂ ∶ t ∶ ⊥
    → Γ [ x ]⊢ ☆² t₂ ∶ ☆ t ∶ A
★³_ {t₂ = t₂} {t} =
    ★ⁿ_ {𝐭 = t₂ ∷ t ∷ []}


-- --------------------------------------------------------------------------
--
-- Notation for typed terms at level 4


𝒗⁴_ : ∀{x A Γ}
    → ⟨ 3 , A ⟩ ∈[ x ] Γ
    → Γ [ suc x ]⊢ 𝑣³ x ∶ 𝑣² x ∶ 𝑣 x ∶ A
𝒗⁴_ = 𝒗ⁿ_

𝝀⁴_ : ∀{x} {t₃ t₂ t : Tm x} {A B Γ}
    → Γ , ⟨ 3 , A ⟩ [ x ]⊢ t₃ ∶ t₂ ∶ t ∶ B
    → Γ [ pred x ]⊢ 𝜆³ t₃ ∶ 𝜆² t₂ ∶ 𝜆 t ∶ (A ⊃ B)
𝝀⁴_ {t₃ = t₃} {t₂} {t} =
    𝝀ⁿ_ {𝐭 = t₃ ∷ t₂ ∷ t ∷ []}

_∙⁴_ : ∀{x y} {t₃ t₂ t : Tm x} {s₃ s₂ s : Tm y} {A B Γ}
    → Γ [ x ]⊢ t₃ ∶ t₂ ∶ t ∶ (A ⊃ B)    → Γ [ y ]⊢ s₃ ∶ s₂ ∶ s ∶ A
    → Γ [ x ⊔ y ]⊢ t₃ ∘³ s₃ ∶ t₂ ∘² s₂ ∶ t ∘ s ∶ B
_∙⁴_ {t₃ = t₃} {t₂} {t} {s₃} {s₂} {s} =
    _∙ⁿ_ {𝐭 = t₃ ∷ t₂ ∷ t ∷ []} {𝐬 = s₃ ∷ s₂ ∷ s ∷ []}

𝒑⁴⟨_,_⟩ : ∀{x y} {t₃ t₂ t : Tm x} {s₃ s₂ s : Tm y} {A B Γ}
    → Γ [ x ]⊢ t₃ ∶ t₂ ∶ t ∶ A          → Γ [ y ]⊢ s₃ ∶ s₂ ∶ s ∶ B
    → Γ [ x ⊔ y ]⊢ 𝑝³⟨ t₃ , s₃ ⟩ ∶ 𝑝²⟨ t₂ , s₂ ⟩ ∶ 𝑝⟨ t , s ⟩ ∶ (A ∧ B)
𝒑⁴⟨_,_⟩ {t₃ = t₃} {t₂} {t} {s₃} {s₂} {s} =
    𝒑ⁿ⟨_,_⟩ {𝐭 = t₃ ∷ t₂ ∷ t ∷ []} {𝐬 = s₃ ∷ s₂ ∷ s ∷ []}

𝝅₀⁴_ : ∀{x} {t₃ t₂ t : Tm x} {A B Γ}
    → Γ [ x ]⊢ t₃ ∶ t₂ ∶ t ∶ (A ∧ B)
    → Γ [ x ]⊢ 𝜋₀³ t₃ ∶ 𝜋₀² t₂ ∶ 𝜋₀ t ∶ A
𝝅₀⁴_ {t₃ = t₃} {t₂} {t} =
    𝝅₀ⁿ_ {𝐭 = t₃ ∷ t₂ ∷ t ∷ []}

𝝅₁⁴_ : ∀{x} {t₃ t₂ t : Tm x} {A B Γ}
    → Γ [ x ]⊢ t₃ ∶ t₂ ∶ t ∶ (A ∧ B)
    → Γ [ x ]⊢ 𝜋₁³ t₃ ∶ 𝜋₁² t₂ ∶ 𝜋₁ t ∶ B
𝝅₁⁴_ {t₃ = t₃} {t₂} {t} =
    𝝅₁ⁿ_ {𝐭 = t₃ ∷ t₂ ∷ t ∷ []}

𝜾₀⁴_ : ∀{x} {t₃ t₂ t : Tm x} {A B Γ}
    → Γ [ x ]⊢ t₃ ∶ t₂ ∶ t ∶ A
    → Γ [ x ]⊢ 𝜄₀³ t₃ ∶ 𝜄₀² t₂ ∶ 𝜄₀ t ∶ (A ∨ B)
𝜾₀⁴_ {t₃ = t₃} {t₂} {t} =
    𝜾₀ⁿ_ {𝐭 = t₃ ∷ t₂ ∷ t ∷ []}

𝜾₁⁴_ : ∀{x} {t₃ t₂ t : Tm x} {A B Γ}
    → Γ [ x ]⊢ t₃ ∶ t₂ ∶ t ∶ B
    → Γ [ x ]⊢ 𝜄₁³ t₃ ∶ 𝜄₁² t₂ ∶ 𝜄₁ t ∶ (A ∨ B)
𝜾₁⁴_ {t₃ = t₃} {t₂} {t} =
    𝜾₁ⁿ_ {𝐭 = t₃ ∷ t₂ ∷ t ∷ []}

𝒄⁴[_▷_∣_] : ∀{x y z} {t₃ t₂ t : Tm x} {s₃ s₂ s : Tm y} {u₃ u₂ u : Tm z} {A B C Γ}
    → Γ [ x ]⊢ t₃ ∶ t₂ ∶ t ∶ (A ∨ B)    → Γ , ⟨ 3 , A ⟩ [ y ]⊢ s₃ ∶ s₂ ∶ s ∶ C
                                          → Γ , ⟨ 3 , B ⟩ [ z ]⊢ u₃ ∶ u₂ ∶ u ∶ C
    → Γ [ x ⊔ pred y ⊔ pred z ]⊢ 𝑐³[ t₃ ▷ s₃ ∣ u₃ ] ∶ 𝑐²[ t₂ ▷ s₂ ∣ u₂ ] ∶ 𝑐[ t ▷ s ∣ u ] ∶ C
𝒄⁴[_▷_∣_] {t₃ = t₃} {t₂} {t} {s₃} {s₂} {s} {u₃} {u₂} {u} =
    𝒄ⁿ[_▷_∣_] {𝐭 = t₃ ∷ t₂ ∷ t ∷ []} {𝐬 = s₃ ∷ s₂ ∷ s ∷ []}
                                     {𝐮 = u₃ ∷ u₂ ∷ u ∷ []}

⬆⁴_ : ∀{x} {t₃ t₂ t : Tm x} {u : Tm x} {A Γ}
    → Γ [ x ]⊢ t₃ ∶ t₂ ∶ t ∶ u ∶ A
    → Γ [ x ]⊢ ⇑³ t₃ ∶ ⇑² t₂ ∶ ⇑ t ∶ ! u ∶ u ∶ A
⬆⁴_ {t₃ = t₃} {t₂} {t} =
    ⬆ⁿ_ {𝐭 = t₃ ∷ t₂ ∷ t ∷ []}

⬇⁴_ : ∀{x} {t₃ t₂ t : Tm x} {u : Tm x} {A Γ}
    → Γ [ x ]⊢ t₃ ∶ t₂ ∶ t ∶ u ∶ A
    → Γ [ x ]⊢ ⇓³ t₃ ∶ ⇓² t₂ ∶ ⇓ t ∶ A
⬇⁴_ {t₃ = t₃} {t₂} {t} =
    ⬇ⁿ_ {𝐭 = t₃ ∷ t₂ ∷ t ∷ []}

★⁴_ : ∀{x} {t₃ t₂ t : Tm x} {A Γ}
    → Γ [ x ]⊢ t₃ ∶ t₂ ∶ t ∶ ⊥
    → Γ [ x ]⊢ ☆³ t₃ ∶ ☆² t₂ ∶ ☆ t ∶ A
★⁴_ {t₃ = t₃} {t₂} {t} =
    ★ⁿ_ {𝐭 = t₃ ∷ t₂ ∷ t ∷ []}


-- --------------------------------------------------------------------------
--
-- Quotation


quot : ∀{x B Γ} → Γ [ x ]⊢ B → Tm x
quot (𝒗ⁿ_ {n} {x} i)       = 𝑣[ suc n ] x
quot (𝝀ⁿ_ {n} 𝒟)           = 𝜆[ suc n ] quot 𝒟
quot (_∙ⁿ_ {n} 𝒟 𝒞)        = quot 𝒟 ∘[ suc n ] quot 𝒞
quot (𝒑ⁿ⟨_,_⟩ {n} 𝒟 𝒞)     = 𝑝[ suc n ]⟨ quot 𝒟 , quot 𝒞 ⟩
quot (𝝅₀ⁿ_ {n} 𝒟)          = 𝜋₀[ suc n ] quot 𝒟
quot (𝝅₁ⁿ_ {n} 𝒟)          = 𝜋₁[ suc n ] quot 𝒟
quot (𝜾₀ⁿ_ {n} 𝒟)          = 𝜄₀[ suc n ] quot 𝒟
quot (𝜾₁ⁿ_ {n} 𝒟)          = 𝜄₁[ suc n ] quot 𝒟
quot (𝒄ⁿ[_▷_∣_] {n} 𝒟 𝒞 ℰ) = 𝑐[ suc n ][ quot 𝒟 ▷ quot 𝒞 ∣ quot ℰ ]
quot (⬆ⁿ_ {n} 𝒟)           = ⇑[ suc n ] quot 𝒟
quot (⬇ⁿ_ {n} 𝒟)           = ⇓[ suc n ] quot 𝒟
quot (★ⁿ_ {n} 𝒟)           = ☆[ suc n ] quot 𝒟


-- --------------------------------------------------------------------------
--
-- Internalisation (theorem 1, p. 29 [1]; lemma 5.4, pp. 9–10 [2])


-- A , A₂ , … , Aₘ ⇒
--   x ∶ A , x₂ ∶ A₂ , … , xₘ ∶ Aₘ
prefix : Cx → Cx
prefix ∅               = ∅
prefix (Γ , ⟨ n , A ⟩) = prefix Γ , ⟨ suc n , A ⟩


-- yₙ ∶ yₙ₋₁ ∶ … ∶ y ∶ A⁰ₖ ∈ A , A₂ , … , Aₘ ⇒
--   xₖ ∶ yₙ ∶ yₙ₋₁ ∶ … ∶ y ∶ A⁰ₖ ∈ x ∶ A, x₂ ∶ A₂ , … , xₘ ∶ Aₘ
int∈ : ∀{n x A Γ}
    → ⟨ n , A ⟩ ∈[ x ] Γ
    → ⟨ suc n , A ⟩ ∈[ x ] prefix Γ
int∈ 𝐙     = 𝐙
int∈ (𝐒 i) = 𝐒 (int∈ i)


-- A , A₂ , … , Aₘ ⊢ B ⇒
--   x ∶ A , x₂ ∶ A₂ , … xₘ ∶ Aₘ ⊢ t (x , x₂ , … , xₘ) ∶ B
int⊢ : ∀{x B Γ}
    → (𝒟 : Γ [ x ]⊢ B)
    → prefix Γ [ x ]⊢ quot 𝒟 ∶ B

int⊢ (𝒗ⁿ_ i)         = 𝒗ⁿ int∈ i
int⊢ (𝝀ⁿ_ {𝐭 = 𝐭} 𝒟) = 𝝀ⁿ_ {𝐭 = quot 𝒟 ∷ 𝐭} (int⊢ 𝒟)

int⊢ (_∙ⁿ_ {𝐭 = 𝐭} {𝐬 = 𝐬} 𝒟 𝒞) =
    _∙ⁿ_ {𝐭 = quot 𝒟 ∷ 𝐭} {𝐬 = quot 𝒞 ∷ 𝐬} (int⊢ 𝒟) (int⊢ 𝒞)

int⊢ (𝒑ⁿ⟨_,_⟩ {𝐭 = 𝐭} {𝐬 = 𝐬} 𝒟 𝒞) =
    𝒑ⁿ⟨_,_⟩ {𝐭 = quot 𝒟 ∷ 𝐭} {𝐬 = quot 𝒞 ∷ 𝐬} (int⊢ 𝒟) (int⊢ 𝒞)

int⊢ (𝝅₀ⁿ_ {𝐭 = 𝐭} 𝒟) = 𝝅₀ⁿ_ {𝐭 = quot 𝒟 ∷ 𝐭} (int⊢ 𝒟)
int⊢ (𝝅₁ⁿ_ {𝐭 = 𝐭} 𝒟) = 𝝅₁ⁿ_ {𝐭 = quot 𝒟 ∷ 𝐭} (int⊢ 𝒟)
int⊢ (𝜾₀ⁿ_ {𝐭 = 𝐭} 𝒟) = 𝜾₀ⁿ_ {𝐭 = quot 𝒟 ∷ 𝐭} (int⊢ 𝒟)
int⊢ (𝜾₁ⁿ_ {𝐭 = 𝐭} 𝒟) = 𝜾₁ⁿ_ {𝐭 = quot 𝒟 ∷ 𝐭} (int⊢ 𝒟)

int⊢ (𝒄ⁿ[_▷_∣_] {𝐭 = 𝐭} {𝐬 = 𝐬} {𝐮 = 𝐮} 𝒟 𝒞 ℰ) =
    𝒄ⁿ[_▷_∣_] {𝐭 = quot 𝒟 ∷ 𝐭} {𝐬 = quot 𝒞 ∷ 𝐬}
                               {𝐮 = quot ℰ ∷ 𝐮} (int⊢ 𝒟) (int⊢ 𝒞)
                                                          (int⊢ ℰ)

int⊢ (⬆ⁿ_ {𝐭 = 𝐭} 𝒟) = ⬆ⁿ_ {𝐭 = quot 𝒟 ∷ 𝐭} (int⊢ 𝒟)
int⊢ (⬇ⁿ_ {𝐭 = 𝐭} 𝒟) = ⬇ⁿ_ {𝐭 = quot 𝒟 ∷ 𝐭} (int⊢ 𝒟)
int⊢ (★ⁿ_ {𝐭 = 𝐭} 𝒟) = ★ⁿ_ {𝐭 = quot 𝒟 ∷ 𝐭} (int⊢ 𝒟)


-- --------------------------------------------------------------------------
--
-- Weakening


wk∈ : ∀{x A Δ}
    → (Γ : Cx)    → A ∈[ x ] (∅ „ Γ)
    → A ∈[ x ] (Δ „ Γ)
wk∈ ∅       ()
wk∈ (Γ , A) 𝐙     = 𝐙
wk∈ (Γ , A) (𝐒 i) = 𝐒 (wk∈ Γ i)


wk⊢ : ∀{x A Δ}
    → (Γ : Cx)    → ∅ „ Γ [ x ]⊢ A
    → Δ „ Γ [ x ]⊢ A

wk⊢ Γ (𝒗ⁿ_ i)                 = 𝒗ⁿ wk∈ Γ i
wk⊢ Γ (𝝀ⁿ_ {n} {𝐭 = 𝐭} {A} 𝒟) = 𝝀ⁿ_ {𝐭 = 𝐭} (wk⊢ (Γ , ⟨ n , A ⟩) 𝒟)

wk⊢ Γ (_∙ⁿ_ {𝐭 = 𝐭} {𝐬 = 𝐬} 𝒟 𝒞) =
    _∙ⁿ_ {𝐭 = 𝐭} {𝐬 = 𝐬} (wk⊢ Γ 𝒟) (wk⊢ Γ 𝒞)

wk⊢ Γ (𝒑ⁿ⟨_,_⟩ {𝐭 = 𝐭} {𝐬 = 𝐬} 𝒟 𝒞) =
    𝒑ⁿ⟨_,_⟩ {𝐭 = 𝐭} {𝐬 = 𝐬} (wk⊢ Γ 𝒟) (wk⊢ Γ 𝒞)

wk⊢ Γ (𝝅₀ⁿ_ {𝐭 = 𝐭} 𝒟) = 𝝅₀ⁿ_ {𝐭 = 𝐭} (wk⊢ Γ 𝒟)
wk⊢ Γ (𝝅₁ⁿ_ {𝐭 = 𝐭} 𝒟) = 𝝅₁ⁿ_ {𝐭 = 𝐭} (wk⊢ Γ 𝒟)
wk⊢ Γ (𝜾₀ⁿ_ {𝐭 = 𝐭} 𝒟) = 𝜾₀ⁿ_ {𝐭 = 𝐭} (wk⊢ Γ 𝒟)
wk⊢ Γ (𝜾₁ⁿ_ {𝐭 = 𝐭} 𝒟) = 𝜾₁ⁿ_ {𝐭 = 𝐭} (wk⊢ Γ 𝒟)

wk⊢ Γ (𝒄ⁿ[_▷_∣_] {n} {𝐭 = 𝐭} {𝐬} {𝐮} {A} {B} 𝒟 𝒞 ℰ) =
    𝒄ⁿ[_▷_∣_] {𝐭 = 𝐭} {𝐬 = 𝐬}
                      {𝐮 = 𝐮} (wk⊢ Γ 𝒟) (wk⊢ (Γ , ⟨ n , A ⟩) 𝒞)
                                         (wk⊢ (Γ , ⟨ n , B ⟩) ℰ)

wk⊢ Γ (⬆ⁿ_ {𝐭 = 𝐭} 𝒟) = ⬆ⁿ_ {𝐭 = 𝐭} (wk⊢ Γ 𝒟)
wk⊢ Γ (⬇ⁿ_ {𝐭 = 𝐭} 𝒟) = ⬇ⁿ_ {𝐭 = 𝐭} (wk⊢ Γ 𝒟)
wk⊢ Γ (★ⁿ_ {𝐭 = 𝐭} 𝒟) = ★ⁿ_ {𝐭 = 𝐭} (wk⊢ Γ 𝒟)


-- --------------------------------------------------------------------------
--
-- Constructive necessitation (corollary 5.5, p. 10 [2])


nec : ∀{A}
    → (𝒟 : ∅ [ 0 ]⊢ A)
    → ⊩ quot 𝒟 ∶ A
nec 𝒟 = wk⊢ ∅ (int⊢ 𝒟)


-- --------------------------------------------------------------------------
--
-- Examples


-- Some theorems of propositional logic
module PL where
  I : ∀{A}
      → ⊩ A ⊃ A
  I = 𝝀 𝒗 𝟎

  K : ∀{A B}
      → ⊩ A ⊃ B ⊃ A
  K = 𝝀 𝝀 𝒗 𝟏

  S : ∀{A B C}
      → ⊩ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
  S = 𝝀 𝝀 𝝀 (𝒗 𝟐 ∙ 𝒗 𝟎) ∙ (𝒗 𝟏 ∙ 𝒗 𝟎)

  X1 : ∀{A B}
      → ⊩ A ⊃ B ⊃ A ∧ B
  X1 = 𝝀 𝝀 𝒑⟨ 𝒗 𝟏 , 𝒗 𝟎 ⟩


-- Some derived theorems
module PLExamples where
  -- □ (A ⊃ A)
  I² : ∀{A}
      → ⊩ 𝜆 𝑣 0 ∶ (A ⊃ A)
  I² = nec PL.I

  -- □ □ (A ⊃ A)
  I³ : ∀{A}
      → ⊩ 𝜆² 𝑣² 0 ∶ 𝜆 𝑣 0 ∶ (A ⊃ A)
  I³ = nec I²

  -- □ (A ⊃ B ⊃ A)
  K² : ∀{A B}
      → ⊩ 𝜆 𝜆 𝑣 1 ∶ (A ⊃ B ⊃ A)
  K² = nec PL.K

  -- □ □ (A ⊃ B ⊃ A)
  K³ : ∀{A B}
      → ⊩ 𝜆² 𝜆² 𝑣² 1 ∶ 𝜆 𝜆 𝑣 1 ∶ (A ⊃ B ⊃ A)
  K³ = nec K²

  -- □ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
  S² : ∀{A B C}
      → ⊩ 𝜆 𝜆 𝜆 (𝑣 2 ∘ 𝑣 0) ∘ (𝑣 1 ∘ 𝑣 0)
          ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
  S² = nec PL.S

  -- □ □ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
  S³ : ∀{A B C}
      → ⊩ 𝜆² 𝜆² 𝜆² (𝑣² 2 ∘² 𝑣² 0) ∘² (𝑣² 1 ∘² 𝑣² 0)
          ∶ 𝜆 𝜆 𝜆 (𝑣 2 ∘ 𝑣 0) ∘ (𝑣 1 ∘ 𝑣 0)
              ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
  S³ = nec S²


-- Some theorems of modal logic S4
module S4 where
  -- □ (A ⊃ B) ⊃ □ A ⊃ □ B
  K : ∀{A B}
      → ⊩ (𝑣 1 ∶ (A ⊃ B)) ⊃ 𝑣 0 ∶ A ⊃ (𝑣 1 ∘ 𝑣 0) ∶ B
  K = 𝝀 𝝀 (𝒗 𝟏 ∙² 𝒗 𝟎)

  -- □ A ⊃ A
  T : ∀{A}
      → ⊩ 𝑣 0 ∶ A ⊃ A
  T = 𝝀 ⬇ 𝒗 𝟎

  -- □ A ⊃ □ □ A
  #4 : ∀{A}
      → ⊩ 𝑣 0 ∶ A ⊃ ! 𝑣 0 ∶ 𝑣 0 ∶ A
  #4 = 𝝀 ⬆ 𝒗 𝟎

  -- □ A ⊃ □ B ⊃ □ □ (A ∧ B)
  X1 : ∀{A B}
      → ⊩ 𝑣 1 ∶ A ⊃ 𝑣 0 ∶ B ⊃ ! 𝑝⟨ 𝑣 1 , 𝑣 0 ⟩ ∶ 𝑝⟨ 𝑣 1 , 𝑣 0 ⟩ ∶ (A ∧ B)
  X1 = 𝝀 𝝀 ⬆ 𝒑²⟨ 𝒗 𝟏 , 𝒗 𝟎 ⟩

  -- □ A ⊃ □ B ⊃ □ (A ∧ B)
  X2 : ∀{A B}
      → ⊩ 𝑣 1 ∶ A ⊃ 𝑣 0 ∶ B ⊃ 𝑝⟨ 𝑣 1 , 𝑣 0 ⟩ ∶ (A ∧ B)
  X2 = 𝝀 𝝀 𝒑²⟨ 𝒗 𝟏 , 𝒗 𝟎 ⟩

  -- □ A ∧ □ B ⊃ □ □ (A ∧ B)
{-  X3 : ∀{A B}
      → ⊩ 𝑣 1 ∶ A ∧ 𝑣 0 ∶ B ⊃ ! 𝑝⟨ 𝑣 1 , 𝑣 0 ⟩ ∶ 𝑝⟨ 𝑣 1 , 𝑣 0 ⟩ ∶ (A ∧ B)
  X3 = {!!} -- 𝝀 ⬆ 𝒑²⟨ 𝝅₀ 𝒗 𝟎 , 𝝅₁ 𝒗 𝟎 ⟩-}

  -- □ A ∧ □ B ⊃ □ (A ∧ B)
  X4 : ∀{A B}
      → ⊩ 𝑣 1 ∶ A ∧ 𝑣 0 ∶ B ⊃ 𝑝⟨ 𝑣 1 , 𝑣 0 ⟩ ∶ (A ∧ B)
  X4 = 𝝀 {!𝒑²⟨ ? , ? ⟩!}
  -- 𝝀 𝒑²⟨ 𝝅₀ 𝒗 𝟎 , 𝝅₁ 𝒗 𝟎 ⟩


-- Some more derived theorems
module S4Examples where
  -- □ (□ (A ⊃ B) ⊃ □ A ⊃ □ B)
  K² : ∀{A B}
      → ⊩ 𝜆 𝜆 𝑣 1 ∘² 𝑣 0
          ∶ (𝑣 1 ∶ (A ⊃ B) ⊃ 𝑣 0 ∶ A ⊃ (𝑣 1 ∘ 𝑣 0) ∶ B)
  K² = nec S4.K


-- --------------------------------------------------------------------------
--
-- Original examples


-- Example 1 (p. 28 [1])
module Example1 where
  -- □ (□ A ⊃ A)
  E11 : ∀{A}
      → ⊩ 𝜆 ⇓ 𝑣 0 ∶ (𝑣 0 ∶ A ⊃ A)
  E11 = nec S4.T

  -- □ (□ A ⊃ □ □ A)
  E12 : ∀{A}
      → ⊩ 𝜆 ⇑ 𝑣 0 ∶ (𝑣 0 ∶ A ⊃ ! 𝑣 0 ∶ 𝑣 0 ∶ A)
  E12 = nec S4.#4

  -- □ □ (A ⊃ B ⊃ A ∧ B)
  E13 : ∀{A B}
      → ⊩ 𝜆² 𝜆² 𝑝²⟨ 𝑣² 1 , 𝑣² 0 ⟩ ∶ 𝜆 𝜆 𝑝⟨ 𝑣 1 , 𝑣 0 ⟩ ∶ (A ⊃ B ⊃ A ∧ B)
  E13 = nec (nec PL.X1)

  -- □ (□ A ⊃ □ B ⊃ □ □ (A ∧ B))
  E14 : ∀{A B}
      → ⊩ 𝜆 𝜆 ⇑ 𝑝²⟨ 𝑣 1 , 𝑣 0 ⟩
          ∶ (𝑣 1 ∶ A ⊃ 𝑣 0 ∶ B ⊃ ! 𝑝⟨ 𝑣 1 , 𝑣 0 ⟩ ∶ 𝑝⟨ 𝑣 1 , 𝑣 0 ⟩ ∶ (A ∧ B))
  E14 = nec S4.X1


-- Some more variants of example 1
module Example1a where
  -- □ (□ A ⊃ □ B ⊃ □ (A ∧ B))
  E14a : ∀{A B}
      → ⊩ 𝜆 𝜆 𝑝²⟨ 𝑣 1 , 𝑣 0 ⟩ ∶ (𝑣 1 ∶ A ⊃ 𝑣 0 ∶ B ⊃ 𝑝⟨ 𝑣 1 , 𝑣 0 ⟩ ∶ (A ∧ B))
  E14a = nec S4.X2

  -- □ (□ A ∧ □ B ⊃ □ □ (A ∧ B))
{-  E14b : ∀{A B}
      → ⊩ 𝜆 ⇑ 𝑝²⟨ 𝜋₀ 𝑣 0 , 𝜋₁ 𝑣 0 ⟩
          ∶ (𝑣 1 ∶ A ∧ 𝑣 0 ∶ B ⊃ ! 𝑝⟨ 𝑣 1 , 𝑣 0 ⟩ ∶ 𝑝⟨ 𝑣 1 , 𝑣 0 ⟩ ∶ (A ∧ B))
  E14b = nec S4.X3

  -- □ (□ A ∧ □ B ⊃ □ (A ∧ B))
  E14c : ∀{A B}
      → ⊩ 𝜆 𝑝²⟨ 𝜋₀ 𝑣 0 , 𝜋₁ 𝑣 0 ⟩ ∶ (𝑣 1 ∶ A ∧ 𝑣 0 ∶ B ⊃ 𝑝⟨ 𝑣 1 , 𝑣 0 ⟩ ∶ (A ∧ B))
  E14c = nec S4.X4-}


-- Example 2 (pp. 31–32 [1])
module Example2 where
  E2 : ∀{A}
      → ⊩ 𝜆² ⇓² ⇑² 𝑣² 0 ∶ 𝜆 ⇓ ⇑ 𝑣 0 ∶ (𝑣 0 ∶ A ⊃ 𝑣 0 ∶ A)
  E2 = 𝝀³ ⬇³ ⬆³ 𝒗³ 𝟎

  E2a : ∀{A}
      → ⊩ 𝜆² 𝑣² 0 ∶ 𝜆 𝑣 0 ∶ (𝑣 0 ∶ A ⊃ 𝑣 0 ∶ A)
  E2a = 𝝀³ 𝒗³ 𝟎


-- --------------------------------------------------------------------------
--
-- Additional examples


-- De Morgan’s laws
module DeMorgan where
  -- (A ⊃ ⊥) ∧ (B ⊃ ⊥) ⫗ (A ∨ B) ⊃ ⊥
  L1 : ∀{A B}
      → ⊩ ¬ A ∧ ¬ B ⫗ ¬ (A ∨ B)
  L1 = 𝒑⟨ 𝝀 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝝅₀ 𝒗 𝟐 ∙ 𝒗 𝟎 ∣ 𝝅₁ 𝒗 𝟐 ∙ 𝒗 𝟎 ]
        , 𝝀 𝒑⟨ 𝝀 𝒗 𝟏 ∙ 𝜾₀ 𝒗 𝟎 , 𝝀 𝒗 𝟏 ∙ 𝜾₁ 𝒗 𝟎 ⟩ ⟩

  -- (A ⊃ ⊥) ∨ (B ⊃ ⊥) ⊃ (A ⊃ ⊥) ∧ B
  L2 : ∀{A B}
      → ⊩ ¬ A ∨ ¬ B ⊃ ¬ (A ∧ B)
  L2 = 𝝀 𝝀 𝒄[ 𝒗 𝟏 ▷ 𝒗 𝟎 ∙ 𝝅₀ 𝒗 𝟏 ∣ 𝒗 𝟎 ∙ 𝝅₁ 𝒗 𝟏 ]


-- Explosions and contradictions
module ExploCon where
  X1 : ∀{A}
      → ⊩ ⊥ ⊃ A
  X1 = 𝝀 ★ 𝒗 𝟎

  -- □ (⊥ ⊃ A)
  X1² : ∀{A}
      → ⊩ 𝜆 ☆ 𝑣 0 ∶ (⊥ ⊃ A)
  X1² = nec X1

  -- □ ⊥ ⊃ □ A
  X2 : ∀{A}
      → ⊩ 𝑣 0 ∶ ⊥ ⊃ ☆ 𝑣 0 ∶ A
  X2 = 𝝀 ★² 𝒗 𝟎

  X3 : ∀{A}
      → ⊩ ¬ A ⊃ A ⊃ ⊥
  X3 = 𝝀 𝝀 𝒗 𝟏 ∙ 𝒗 𝟎

  -- □ (¬ A) ⊃ □ A ⊃ □ ⊥
  X4 : ∀{A}
      → ⊩ 𝑣 1 ∶ (¬ A) ⊃ 𝑣 0 ∶ A ⊃ 𝑣 1 ∘ 𝑣 0 ∶ ⊥
  X4 = 𝝀 𝝀 𝒗 𝟏 ∙² 𝒗 𝟎

  -- □ (¬ A) ⊃ □ A ⊃ □ □ ⊥
  X5 : ∀{A}
      → ⊩ 𝑣 1 ∶ (¬ A) ⊃ 𝑣 0 ∶ A ⊃ ! (𝑣 1 ∘ 𝑣 0) ∶ 𝑣 1 ∘ 𝑣 0 ∶ ⊥
  X5 = 𝝀 𝝀 ⬆ 𝒗 𝟏 ∙² 𝒗 𝟎


-- --------------------------------------------------------------------------
--
-- Further examples


module Idempotence where
  ⊃-idem : ∀{A}
      → ⊩ A ⊃ A ⫗ ⊤
  ⊃-idem = 𝒑⟨ 𝝀 𝝀 𝒗 𝟎
            , 𝝀 𝝀 𝒗 𝟎 ⟩

  ∧-idem : ∀{A}
      → ⊩ A ∧ A ⫗ A
  ∧-idem = 𝒑⟨ 𝝀 𝝅₀ 𝒗 𝟎
            , 𝝀 𝒑⟨ 𝒗 𝟎 , 𝒗 𝟎 ⟩ ⟩

  ∨-idem : ∀{A}
      → ⊩ A ∨ A ⫗ A
  ∨-idem = 𝒑⟨ 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝒗 𝟎 ∣ 𝒗 𝟎 ]
            , 𝝀 𝜾₀ 𝒗 𝟎 ⟩


module Commutativity where
  ∧-comm : ∀{A B}
      → ⊩ A ∧ B ⫗ B ∧ A
  ∧-comm = 𝒑⟨ 𝝀 𝒑⟨ 𝝅₁ 𝒗 𝟎 , 𝝅₀ 𝒗 𝟎 ⟩
            , 𝝀 𝒑⟨ 𝝅₁ 𝒗 𝟎 , 𝝅₀ 𝒗 𝟎 ⟩ ⟩

  ∨-comm : ∀{A B}
      → ⊩ A ∨ B ⫗ B ∨ A
  ∨-comm = 𝒑⟨ 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝜾₁ 𝒗 𝟎 ∣ 𝜾₀ 𝒗 𝟎 ]
            , 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝜾₁ 𝒗 𝟎 ∣ 𝜾₀ 𝒗 𝟎 ] ⟩


module Associativity where
  ∧-assoc : ∀{A B C}
      → ⊩ A ∧ (B ∧ C) ⫗ (A ∧ B) ∧ C
  ∧-assoc = 𝒑⟨ 𝝀 𝒑⟨ 𝒑⟨ 𝝅₀ 𝒗 𝟎 , 𝝅₀ 𝝅₁ 𝒗 𝟎 ⟩ , 𝝅₁ 𝝅₁ 𝒗 𝟎 ⟩
             , 𝝀 𝒑⟨ 𝝅₀ 𝝅₀ 𝒗 𝟎 , 𝒑⟨ 𝝅₁ 𝝅₀ 𝒗 𝟎 , 𝝅₁ 𝒗 𝟎 ⟩ ⟩ ⟩

  ∨-assoc : ∀{A B C}
      → ⊩ A ∨ (B ∨ C) ⫗ (A ∨ B) ∨ C
  ∨-assoc = 𝒑⟨ 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝜾₀ 𝜾₀ 𝒗 𝟎 ∣ 𝒄[ 𝒗 𝟎 ▷ 𝜾₀ 𝜾₁ 𝒗 𝟎 ∣ 𝜾₁ 𝒗 𝟎 ] ]
             , 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝒄[ 𝒗 𝟎 ▷ 𝜾₀ 𝒗 𝟎 ∣ 𝜾₁ 𝜾₀ 𝒗 𝟎 ] ∣ 𝜾₁ 𝜾₁ 𝒗 𝟎 ] ⟩


module Distributivity where
  ⊃-dist-∧ : ∀{A B C}
      → ⊩ A ⊃ (B ∧ C) ⫗ (A ⊃ B) ∧ (A ⊃ C)
  ⊃-dist-∧ = 𝒑⟨ 𝝀 𝒑⟨ 𝝀 𝝅₀ (𝒗 𝟏 ∙ 𝒗 𝟎) , 𝝀 𝝅₁ (𝒗 𝟏 ∙ 𝒗 𝟎) ⟩
              , 𝝀 𝝀 𝒑⟨ 𝝅₀ 𝒗 𝟏 ∙ 𝒗 𝟎 , 𝝅₁ 𝒗 𝟏 ∙ 𝒗 𝟎 ⟩ ⟩

  ∧-dist-∨ : ∀{A B C}
      → ⊩ A ∧ (B ∨ C) ⫗ (A ∧ B) ∨ (A ∧ C)
  ∧-dist-∨ = 𝒑⟨ 𝝀 𝒄[ 𝝅₁ 𝒗 𝟎 ▷ 𝜾₀ 𝒑⟨ 𝝅₀ 𝒗 𝟏 , 𝒗 𝟎 ⟩ ∣ 𝜾₁ 𝒑⟨ 𝝅₀ 𝒗 𝟏 , 𝒗 𝟎 ⟩ ]
              , 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝒑⟨ 𝝅₀ 𝒗 𝟎 , 𝜾₀ 𝝅₁ 𝒗 𝟎 ⟩ ∣ 𝒑⟨ 𝝅₀ 𝒗 𝟎 , 𝜾₁ 𝝅₁ 𝒗 𝟎 ⟩ ] ⟩

  ∨-dist-∧ : ∀{A B C}
      → ⊩ A ∨ (B ∧ C) ⫗ (A ∨ B) ∧ (A ∨ C)
  ∨-dist-∧ = 𝒑⟨ 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝒑⟨ 𝜾₀ 𝒗 𝟎 , 𝜾₀ 𝒗 𝟎 ⟩ ∣ 𝒑⟨ 𝜾₁ 𝝅₀ 𝒗 𝟎 , 𝜾₁ 𝝅₁ 𝒗 𝟎 ⟩ ]
              , 𝝀 𝒄[ 𝝅₀ 𝒗 𝟎 ▷ 𝜾₀ 𝒗 𝟎 ∣ 𝒄[ 𝝅₁ 𝒗 𝟏 ▷ 𝜾₀ 𝒗 𝟎 ∣ 𝜾₁ 𝒑⟨ 𝒗 𝟏 , 𝒗 𝟎 ⟩ ] ] ⟩


module Untitled where
  ⊃-law : ∀{A B C}
      → ⊩ (A ⊃ B) ⊃ (B ⊃ C) ⊃ A ⊃ C
  ⊃-law = 𝝀 𝝀 𝝀 𝒗 𝟏 ∙ (𝒗 𝟐 ∙ 𝒗 𝟎)

  ⊃-∧-law : ∀{A B C}
      → ⊩ A ⊃ B ⊃ C ⫗ (A ∧ B) ⊃ C
  ⊃-∧-law = 𝒑⟨ 𝝀 𝝀 𝒗 𝟏 ∙ 𝝅₀ 𝒗 𝟎 ∙ 𝝅₁ 𝒗 𝟎
             , 𝝀 𝝀 𝝀 𝒗 𝟐 ∙ 𝒑⟨ 𝒗 𝟏 , 𝒗 𝟎 ⟩ ⟩

  ∨-⊃-∧-law : ∀{A B C}
      → ⊩ (A ∨ B) ⊃ C ⫗ (A ⊃ C) ∧ (B ⊃ C)
  ∨-⊃-∧-law = 𝒑⟨ 𝝀 𝒑⟨ 𝝀 𝒗 𝟏 ∙ 𝜾₀ 𝒗 𝟎 , 𝝀 𝒗 𝟏 ∙ 𝜾₁ 𝒗 𝟎 ⟩
               , 𝝀 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝝅₀ 𝒗 𝟐 ∙ 𝒗 𝟎 ∣ 𝝅₁ 𝒗 𝟐 ∙ 𝒗 𝟎 ] ⟩


module Trivial where
  ⊃-⊤-law : ∀{A}
      → ⊩ A ⊃ ⊤ ⫗ ⊤
  ⊃-⊤-law = 𝒑⟨ 𝝀 𝝀 𝒗 𝟎
              , 𝝀 𝝀 𝒗 𝟏 ⟩

  ⊤-⊃-law : ∀{A}
      → ⊩ ⊤ ⊃ A ⫗ A
  ⊤-⊃-law = 𝒑⟨ 𝝀 𝒗 𝟎 ∙ (𝝀 𝒗 𝟎)
              , 𝝀 𝝀 𝒗 𝟏 ⟩

  ⊥-⊃-⊤-law : ∀{A}
      → ⊩ ⊥ ⊃ A ⫗ ⊤
  ⊥-⊃-⊤-law = 𝒑⟨ 𝝀 𝝀 𝒗 𝟎
                 , 𝝀 𝝀 ★ 𝒗 𝟎 ⟩

  ∧-⊥-law : ∀{A}
      → ⊩ A ∧ ⊥ ⫗ ⊥
  ∧-⊥-law = 𝒑⟨ 𝝀 𝝅₁ 𝒗 𝟎
              , 𝝀 ★ 𝒗 𝟎 ⟩

  ∨-⊥-law : ∀{A}
      → ⊩ A ∨ ⊥ ⫗ A
  ∨-⊥-law = 𝒑⟨ 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝒗 𝟎 ∣ ★ 𝒗 𝟎 ]
              , 𝝀 𝜾₀ 𝒗 𝟎 ⟩

  ∧-⊤-law : ∀{A}
      → ⊩ A ∧ ⊤ ⫗ A
  ∧-⊤-law = 𝒑⟨ 𝝀 𝝅₀ 𝒗 𝟎
              , 𝝀 𝒑⟨ 𝒗 𝟎 , 𝝀 𝒗 𝟎 ⟩ ⟩

  ∨-⊤-law : ∀{A}
      → ⊩ A ∨ ⊤ ⫗ ⊤
  ∨-⊤-law = 𝒑⟨ 𝝀 𝝀 𝒗 𝟎
              , 𝝀 𝜾₁ 𝒗 𝟎 ⟩

-}
