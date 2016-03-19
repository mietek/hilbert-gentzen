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
     ("mv" "𝒗") ("ml" "𝝀") ("ml2" "𝝀²") ("ml3" "𝝀³") ("mln" "𝝀ⁿ")
     ("mo" "∙") ("mo2" "∙²") ("mo3" "∙³") ("mon" "∙ⁿ")
     ("mp" "𝒑") ("mp2" "𝒑²") ("mp3" "𝒑³") ("mpn" "𝒑ⁿ")
     ("mpi0" "𝝅₀") ("mpi02" "𝝅₀²") ("mpi03" "𝝅₀³") ("mpi0n" "𝝅₀ⁿ")
     ("mpi1" "𝝅₁") ("mpi12" "𝝅₁²") ("mpi13" "𝝅₁³") ("mpi1n" "𝝅₁ⁿ")
     ("mu" "⬆") ("mu2" "⬆²") ("mu3" "⬆³") ("mun" "⬆ⁿ")
     ("md" "⬇") ("md2" "⬇²") ("md3" "⬇³") ("mdn" "⬇ⁿ")
     ("mS" "𝐒") ("mZ" "𝐙") ("m0" "𝟎") ("m1" "𝟏") ("m2" "𝟐") ("m3" "𝟑")
     ("s" "𝐬") ("t" "𝐭") ("x" "𝐱") ("y" "𝐲"))))


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

open import Data.Vec
  using (Vec ; [] ; _∷_ ; replicate)

infixl 9 !_ 𝑣_ 𝒗_
infixl 8 𝜋₀_ 𝜋₀²_ 𝝅₀_ 𝝅₀²_ 𝝅₀³_
infixl 8 𝜋₁_ 𝜋₁²_ 𝝅₁_ 𝝅₁²_ 𝝅₁³_
infixl 7 _∘_ _∘²_ _∙_ _∙²_ _∙³_
infixr 6 ⇑_ ⇑²_ ⬆_ ⬆²_ ⬆³_
infixr 6 ⇓_ ⇓²_ ⬇_ ⬇²_ ⬇³_
infixr 5 𝜆_ 𝜆²_ 𝝀_ 𝝀²_ 𝝀³_
infixr 4 _∶_ -- _∷_
infixr 3 ¬_
infixl 2 _∧_ _,_
infixr 1 _⊃_ _⫗_
infixr 0 _⊢_ ⊩_


-- --------------------------------------------------------------------------
--
-- Untyped syntax


-- Variables
Var : Set
Var = ℕ


-- Type and term constructors
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
-- Simplified notation for term constructors at level 1


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
-- Simplified notation for term constructors at level 2


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
-- Simplified notation for term constructors at level 3


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
-- Generic vector functions


-- Transforming each element dependent on its index
ixMap : ∀{n} {X Y : Set}
    → (ℕ → X → Y) → Vec X n → Vec Y n
ixMap {zero}  f []      = []
ixMap {suc n} f (x ∷ 𝐱) = f (suc n) x ∷ ixMap f 𝐱

-- Transforming each pair of elements dependent on their index
ixZipWith : ∀{n} {X Y Z : Set}
    → (ℕ → X → Y → Z) → Vec X n → Vec Y n → Vec Z n
ixZipWith {zero}  f []      []       = []
ixZipWith {suc n} f (x ∷ 𝐱) (y ∷ 𝐲) = f (suc n) x y ∷ ixZipWith f 𝐱 𝐲


-- --------------------------------------------------------------------------
--
-- Vector notation for type assertions at level n, p. 27 [1]


-- Term vectors
Tms : ℕ → Set
Tms = Vec Tm


-- tₙ ∶ tₙ₋₁ ∶ ⋯ ∶ t₁ ∶ A
*_∷_ : ∀{n} → Tms n → Ty → Ty
* []      ∷ A = A
* (x ∷ 𝐭) ∷ A = x ∶ * 𝐭 ∷ A

-- 𝑣 x ∶ 𝑣 x ∶ ⋯ ∶ 𝑣 x ∶ A
𝑣[_]_∷_ : ℕ → Var → Ty → Ty
𝑣[ n ] x ∷ A = * replicate {n = n} (𝑣 x) ∷ A

-- 𝜆ⁿ tₙ ∶ 𝜆ⁿ⁻¹ tₙ₋₁ ∶ ⋯ ∶ 𝜆 t₁ ∶ A
𝜆ⁿ_∷_ : ∀{n} → Tms n → Ty → Ty
𝜆ⁿ 𝐭 ∷ A = * ixMap 𝜆[_]_ 𝐭 ∷ A

-- tₙ ∘ⁿ sₙ ∶ tₙ₋₁ ∘ⁿ⁻¹ ∶ sₙ₋₁ ∶ ⋯ ∶ t₁ ∘ s₁ ∶ A
_∘ⁿ_∷_ : ∀{n} → Tms n → Tms n → Ty → Ty
𝐭 ∘ⁿ 𝐬 ∷ A = * ixZipWith (λ n t s → t ∘[ n ] s) 𝐭 𝐬 ∷ A

-- 𝑝ⁿ⟨ tₙ , sₙ ⟩ ∶ 𝑝ⁿ⁻¹⟨ tₙ₋₁ , sₙ₋₁ ⟩ ∶ ⋯ ∶ p⟨ t₁ , s₁ ⟩ ∶ A
𝑝ⁿ⟨_,_⟩∷_ : ∀{n} → Tms n → Tms n → Ty → Ty
𝑝ⁿ⟨ 𝐭 , 𝐬 ⟩∷ A = * ixZipWith 𝑝[_]⟨_,_⟩ 𝐭 𝐬 ∷ A

-- 𝜋₀ⁿ tₙ ∶ 𝜋₀ⁿ⁻¹ tₙ₋₁ ∶ ⋯ ∶ 𝜋₀ t₁ ∶ A
𝜋₀ⁿ_∷_ : ∀{n} → Tms n → Ty → Ty
𝜋₀ⁿ 𝐭 ∷ A = * ixMap 𝜋₀[_]_ 𝐭 ∷ A

-- 𝜋₁ⁿ tₙ ∶ 𝜋₁ⁿ⁻¹ tₙ₋₁ ∶ ⋯ ∶ 𝜋₁ t₁ ∶ A
𝜋₁ⁿ_∷_ : ∀{n} → Tms n → Ty → Ty
𝜋₁ⁿ 𝐭 ∷ A = * ixMap 𝜋₁[_]_ 𝐭 ∷ A

-- ⇑ⁿ tₙ ∶ ⇑ⁿ⁻¹ tₙ₋₁ ∶ ⋯ ∶ ⇑ t₁ ∶ A
⇑ⁿ_∷_ : ∀{n} → Tms n → Ty → Ty
⇑ⁿ 𝐭 ∷ A = * ixMap ⇑[_]_ 𝐭 ∷ A

-- ⇓ⁿ tₙ ∶ ⇑ⁿ⁻¹ tₙ₋₁ ∶ ⋯ ∶ ⇑ t₁ ∶ A
⇓ⁿ_∷_ : ∀{n} → Tms n → Ty → Ty
⇓ⁿ 𝐭 ∷ A = * ixMap ⇓[_]_ 𝐭 ∷ A


-- --------------------------------------------------------------------------
--
-- Typed syntax


-- Hypotheses
Hyp : Set
Hyp = ℕ × Ty


-- Contexts
data Cx : ℕ → Set where
  ∅   : Cx zero
  _,_ : ∀{m} → Cx m → Hyp → Cx (suc m)


-- Context membership evidence
data _∈[_]_ : ∀{m} → Hyp → ℕ → Cx m → Set where
  𝐙 : ∀{m A} {Γ : Cx m}
      → A ∈[ zero ] (Γ , A)

  𝐒_ : ∀{m A B x} {Γ : Cx m}
      → A ∈[ x ] Γ
      → A ∈[ suc x ] (Γ , B)


-- Typing rules
data _⊢_ {m : ℕ} (Γ : Cx m) : Ty → Set where
  𝒗_ : ∀{n x} {A}
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


-- Theorems
⊩_  : Ty → Set
⊩ A = ∅ ⊢ A


-- --------------------------------------------------------------------------
--
-- Simplified notation for context membership evidence


𝟎 : ∀{m A} {Γ : Cx m} → A ∈[ 0 ] (Γ , A)
𝟎 = 𝐙

𝟏 : ∀{m A B} {Γ : Cx m} → A ∈[ 1 ] (Γ , A , B)
𝟏 = 𝐒 𝐙

𝟐 : ∀{m A B C} {Γ : Cx m} → A ∈[ 2 ] (Γ , A , B , C)
𝟐 = 𝐒 𝐒 𝐙

𝟑 : ∀{m A B C D} {Γ : Cx m} → A ∈[ 3 ] (Γ , A , B , C , D)
𝟑 = 𝐒 𝐒 𝐒 𝐙


-- --------------------------------------------------------------------------
--
-- Simplified notation for typing rules at level 1


𝝀_ : ∀{A B m} {Γ : Cx m}
    → Γ , ⟨ 0 , A ⟩ ⊢ B
    → Γ ⊢ A ⊃ B
𝝀_ = 𝝀ⁿ_ {𝐭 = []}

_∙_ : ∀{A B m} {Γ : Cx m}
    → Γ ⊢ A ⊃ B    → Γ ⊢ A
    → Γ ⊢ B
_∙_ = _∙ⁿ_ {𝐭 = []} {𝐬 = []}

𝒑⟨_,_⟩ : ∀{A B m} {Γ : Cx m}
    → Γ ⊢ A        → Γ ⊢ B
    → Γ ⊢ A ∧ B
𝒑⟨_,_⟩ = 𝒑ⁿ⟨_,_⟩ {𝐭 = []} {𝐬 = []}

𝝅₀_ : ∀{A B m} {Γ : Cx m}
    → Γ ⊢ A ∧ B
    → Γ ⊢ A
𝝅₀_ = 𝝅₀ⁿ_ {𝐭 = []}

𝝅₁_ : ∀{A B m} {Γ : Cx m}
    → Γ ⊢ A ∧ B
    → Γ ⊢ B
𝝅₁_ = 𝝅₁ⁿ_ {𝐭 = []}

⬆_ : ∀{u A m} {Γ : Cx m}
    → Γ ⊢ u ∶ A
    → Γ ⊢ ! u ∶ u ∶ A
⬆_ = ⬆ⁿ_ {𝐭 = []}

⬇_ : ∀{u A m} {Γ : Cx m}
    → Γ ⊢ u ∶ A
    → Γ ⊢ A
⬇_ = ⬇ⁿ_ {𝐭 = []}


-- --------------------------------------------------------------------------
--
-- Simplified notation for typing rules at level 2


𝝀²_ : ∀{t A B m} {Γ : Cx m}
    → Γ , ⟨ 1 , A ⟩ ⊢ t ∶ B
    → Γ ⊢ 𝜆 t ∶ (A ⊃ B)
𝝀²_ {t} = 𝝀ⁿ_ {𝐭 = t ∷ []}

_∙²_ : ∀{t s A B m} {Γ : Cx m}
    → Γ ⊢ t ∶ (A ⊃ B)    → Γ ⊢ s ∶ A
    → Γ ⊢ t ∘ s ∶ B
_∙²_ {t} {s} = _∙ⁿ_ {𝐭 = t ∷ []} {𝐬 = s ∷ []}

𝒑²⟨_,_⟩ : ∀{t s A B m} {Γ : Cx m}
    → Γ ⊢ t ∶ A          → Γ ⊢ s ∶ B
    → Γ ⊢ 𝑝⟨ t , s ⟩ ∶ (A ∧ B)
𝒑²⟨_,_⟩ {t} {s} = 𝒑ⁿ⟨_,_⟩ {𝐭 = t ∷ []} {𝐬 = s ∷ []}

𝝅₀²_ : ∀{t A B m} {Γ : Cx m}
    → Γ ⊢ t ∶ (A ∧ B)
    → Γ ⊢ 𝜋₀ t ∶ A
𝝅₀²_ {t} = 𝝅₀ⁿ_ {𝐭 = t ∷ []}

𝝅₁²_ : ∀{t A B m} {Γ : Cx m}
    → Γ ⊢ t ∶ (A ∧ B)
    → Γ ⊢ 𝜋₁ t ∶ B
𝝅₁²_ {t} = 𝝅₁ⁿ_ {𝐭 = t ∷ []}

⬆²_ : ∀{t u A m} {Γ : Cx m}
    → Γ ⊢ t ∶ u ∶ A
    → Γ ⊢ ⇑ t ∶ ! u ∶ u ∶ A
⬆²_ {t} = ⬆ⁿ_ {𝐭 = t ∷ []}

⬇²_ : ∀{t u A m} {Γ : Cx m}
    → Γ ⊢ t ∶ u ∶ A
    → Γ ⊢ ⇓ t ∶ A
⬇²_ {t} = ⬇ⁿ_ {𝐭 = t ∷ []}


-- --------------------------------------------------------------------------
--
-- Simplified notation for typing rules at level 3


𝝀³_ : ∀{t₂ t₁ A B m} {Γ : Cx m}
    → Γ , ⟨ 2 , A ⟩ ⊢ t₂ ∶ t₁ ∶ B
    → Γ ⊢ 𝜆² t₂ ∶ 𝜆 t₁ ∶ (A ⊃ B)
𝝀³_ {t₂} {t₁} = 𝝀ⁿ_ {𝐭 = t₂ ∷ t₁ ∷ []}

_∙³_ : ∀{t₂ t₁ s₂ s₁ A B m} {Γ : Cx m}
    → Γ ⊢ t₂ ∶ t₁ ∶ (A ⊃ B)    → Γ ⊢ s₂ ∶ s₁ ∶ A
    → Γ ⊢ t₂ ∘² s₂ ∶ t₁ ∘ s₁ ∶ B
_∙³_ {t₂} {t₁} {s₂} {s₁} = _∙ⁿ_ {𝐭 = t₂ ∷ t₁ ∷ []} {𝐬 = s₂ ∷ s₁ ∷ []}

𝒑³⟨_,_⟩ : ∀{t₂ t₁ s₂ s₁ A B m} {Γ : Cx m}
    → Γ ⊢ t₂ ∶ t₁ ∶ A          → Γ ⊢ s₂ ∶ s₁ ∶ B
    → Γ ⊢ 𝑝²⟨ t₂ , s₂ ⟩ ∶ 𝑝⟨ t₁ , s₁ ⟩ ∶ (A ∧ B)
𝒑³⟨_,_⟩ {t₂} {t₁} {s₂} {s₁} = 𝒑ⁿ⟨_,_⟩ {𝐭 = t₂ ∷ t₁ ∷ []} {𝐬 = s₂ ∷ s₁ ∷ []}

𝝅₀³_ : ∀{t₂ t₁ A B m} {Γ : Cx m}
    → Γ ⊢ t₂ ∶ t₁ ∶ (A ∧ B)
    → Γ ⊢ 𝜋₀² t₂ ∶ 𝜋₀ t₁ ∶ A
𝝅₀³_ {t₂} {t₁} = 𝝅₀ⁿ_ {𝐭 = t₂ ∷ t₁ ∷ []}

𝝅₁³_ : ∀{t₂ t₁ A B m} {Γ : Cx m}
    → Γ ⊢ t₂ ∶ t₁ ∶ (A ∧ B)
    → Γ ⊢ 𝜋₁² t₂ ∶ 𝜋₁ t₁ ∶ B
𝝅₁³_ {t₂} {t₁} = 𝝅₁ⁿ_ {𝐭 = t₂ ∷ t₁ ∷ []}

⬆³_ : ∀{t₂ t₁ u A m} {Γ : Cx m}
    → Γ ⊢ t₂ ∶ t₁ ∶ u ∶ A
    → Γ ⊢ ⇑² t₂ ∶ ⇑ t₁ ∶ ! u ∶ u ∶ A
⬆³_ {t₂} {t₁} = ⬆ⁿ_ {𝐭 = t₂ ∷ t₁ ∷ []}

⬇³_ : ∀{t₂ t₁ u A m} {Γ : Cx m}
    → Γ ⊢ t₂ ∶ t₁ ∶ u ∶ A
    → Γ ⊢ ⇓² t₂ ∶ ⇓ t₁ ∶ A
⬇³_ {t₂} {t₁} = ⬇ⁿ_ {𝐭 = t₂ ∷ t₁ ∷ []}


-- --------------------------------------------------------------------------
--
-- Example terms at levels 1, 2, and 3


-- S4: A ⊃ A
I : ∀{A}
    → ⊩  A ⊃ A
I = 𝝀 𝒗 𝟎

-- S4: □(A ⊃ A)
I² : ∀{A}
    → ⊩  𝜆 𝑣 0  ∶  (A ⊃ A)
I² = 𝝀² 𝒗 𝟎

-- S4: □□(A ⊃ A)
I³ : ∀{A}
    → ⊩  𝜆² 𝑣 0  ∶  𝜆 𝑣 0  ∶  (A ⊃ A)
I³ = 𝝀³ 𝒗 𝟎


-- S4: A ⊃ B ⊃ A
K : ∀{A B}
    → ⊩  A ⊃ B ⊃ A
K = 𝝀 𝝀 𝒗 𝟏

-- S4: □(A ⊃ B ⊃ A)
K² : ∀{A B}
    → ⊩  𝜆 𝜆 𝑣 1  ∶  (A ⊃ B ⊃ A)
K² = 𝝀² 𝝀² 𝒗 𝟏

-- S4: □□(A ⊃ B ⊃ A)
K³ : ∀{A B}
    → ⊩  𝜆² 𝜆² 𝑣 1  ∶  𝜆 𝜆 𝑣 1  ∶  (A ⊃ B ⊃ A)
K³ = 𝝀³ 𝝀³ 𝒗 𝟏


-- S4: (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
S : ∀{A B C}
    → ⊩  (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
S = 𝝀 𝝀 𝝀 (𝒗 𝟐 ∙ 𝒗 𝟎) ∙ (𝒗 𝟏 ∙ 𝒗 𝟎)

-- S4: □((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
S² : ∀{A B C}
    → ⊩  𝜆 𝜆 𝜆 (𝑣 2 ∘ 𝑣 0) ∘ (𝑣 1 ∘ 𝑣 0)  ∶  ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
S² = 𝝀² 𝝀² 𝝀² (𝒗 𝟐 ∙² 𝒗 𝟎) ∙² (𝒗 𝟏 ∙² 𝒗 𝟎)

-- S4: □□((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
S³ : ∀{A B C}
    → ⊩  𝜆² 𝜆² 𝜆² (𝑣 2 ∘² 𝑣 0) ∘² (𝑣 1 ∘² 𝑣 0)  ∶  𝜆 𝜆 𝜆 (𝑣 2 ∘ 𝑣 0) ∘ (𝑣 1 ∘ 𝑣 0)  ∶  ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
S³ = 𝝀³ 𝝀³ 𝝀³ (𝒗 𝟐 ∙³ 𝒗 𝟎) ∙³ (𝒗 𝟏 ∙³ 𝒗 𝟎)


-- --------------------------------------------------------------------------
--
-- Example terms corresponding to S4 axioms at levels 1 and 2


-- S4: □(A ⊃ B) ⊃ □A ⊃ □B
axK : ∀{A B f x}
    → ⊩  (f ∶ (A ⊃ B)) ⊃ x ∶ A ⊃ (f ∘ x) ∶ B
axK = 𝝀 𝝀 (𝒗 𝟏 ∙² 𝒗 𝟎)

-- S4: □(□(A ⊃ B) ⊃ □A ⊃ □B)
axK² : ∀{A B f x}
    → ⊩  𝜆 𝜆 𝑣 1 ∘² 𝑣 0  ∶  (f ∶ (A ⊃ B) ⊃ x ∶ A ⊃ (f ∘ x) ∶ B)
axK² = 𝝀² 𝝀² (𝒗 𝟏 ∙³ 𝒗 𝟎)

-- S4: □A ⊃ A
axT : ∀{A x}
    → ⊩  x ∶ A ⊃ A
axT = 𝝀 ⬇ 𝒗 𝟎

-- S4: □(□A ⊃ A)
axT² : ∀{A x}
    → ⊩  𝜆 ⇓ 𝑣 0  ∶  (x ∶ A ⊃ A)
axT² = 𝝀² ⬇² 𝒗 𝟎

-- S4: □A ⊃ □□A
ax4 : ∀{A x}
    → ⊩  x ∶ A ⊃ ! x ∶ x ∶ A
ax4 = 𝝀 ⬆ 𝒗 𝟎

-- S4: □(□A ⊃ □□A)
ax4² : ∀{A x}
    → ⊩  𝜆 ⇑ 𝑣 0  ∶  (x ∶ A ⊃ ! x ∶ x ∶ A)
ax4² = 𝝀² ⬆² 𝒗 𝟎


-- --------------------------------------------------------------------------
--
-- Terms of example 1, p. 28 [1]


-- S4: □(□A ⊃ A)
ex11 : ∀{A x}
    → ⊩  𝜆 ⇓ 𝑣 0  ∶  (x ∶ A ⊃ A)
ex11 = axT²

-- S4: □(□A ⊃ □□A)
ex12 : ∀{A x}
    → ⊩  𝜆 ⇑ 𝑣 0  ∶  (x ∶ A ⊃ ! x ∶ x ∶ A)
ex12 = ax4²

-- S4: □□(A ⊃ B ⊃ A ∧ B)
ex13 : ∀{A B}
    → ⊩  𝜆² 𝜆² 𝑝²⟨ 𝑣 1 , 𝑣 0 ⟩  ∶  𝜆 𝜆 𝑝⟨ 𝑣 1 , 𝑣 0 ⟩  ∶  (A ⊃ B ⊃ A ∧ B)
ex13 = 𝝀³ 𝝀³ 𝒑³⟨ 𝒗 𝟏 , 𝒗 𝟎 ⟩

-- S4: □(□A ⊃ □B ⊃ □□(A ∧ B))
ex14 : ∀{A B x y}
    → ⊩  𝜆 𝜆 ⇑ 𝑝²⟨ 𝑣 1 , 𝑣 0 ⟩  ∶  (x ∶ A ⊃ y ∶ B ⊃ ! 𝑝⟨ x , y ⟩ ∶ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
ex14 = 𝝀² 𝝀² ⬆² 𝒑³⟨ 𝒗 𝟏 , 𝒗 𝟎 ⟩


-- --------------------------------------------------------------------------
--
-- Additional example terms


-- S4: □(□A ⊃ □B ⊃ □(A ∧ B))
exA : ∀{A B x y}
    → ⊩  𝜆 𝜆 𝑝²⟨ 𝑣 1 , 𝑣 0 ⟩  ∶  (x ∶ A ⊃ y ∶ B ⊃ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
exA = 𝝀² 𝝀² 𝒑³⟨ 𝒗 𝟏 , 𝒗 𝟎 ⟩

-- S4: □(□A ∧ □B ⊃ □□(A ∧ B))
exB : ∀{A B x y}
    → ⊩  𝜆 ⇑ 𝑝²⟨ 𝜋₀ 𝑣 0 , 𝜋₁ 𝑣 0 ⟩  ∶  (x ∶ A ∧ y ∶ B ⊃ ! 𝑝⟨ x , y ⟩ ∶ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
exB = 𝝀² ⬆² 𝒑³⟨ 𝝅₀² 𝒗 𝟎 , 𝝅₁² 𝒗 𝟎 ⟩

-- S4: □(□A ∧ □B ⊃ □(A ∧ B))
exC : ∀{A B x y}
    → ⊩  𝜆 𝑝²⟨ 𝜋₀ 𝑣 0 , 𝜋₁ 𝑣 0 ⟩  ∶  (x ∶ A ∧ y ∶ B ⊃ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
exC = 𝝀² 𝒑³⟨ 𝝅₀² 𝒗 𝟎 , 𝝅₁² 𝒗 𝟎 ⟩


-- --------------------------------------------------------------------------
--
-- Terms of example 2, pp. 31–32 [1]


ex2 : ∀{A x}
    → ⊩  𝜆² ⇓² ⇑² 𝑣 0  ∶  𝜆 ⇓ ⇑ 𝑣 0  ∶  (x ∶ A ⊃ x ∶ A)
ex2 = 𝝀³ ⬇³ ⬆³ 𝒗 𝟎

ex2′ : ∀{A x}
    → ⊩ 𝜆² 𝑣 0  ∶  𝜆 𝑣 0  ∶  (x ∶ A ⊃ x ∶ A)
ex2′ = 𝝀³  𝒗 𝟎


-- --------------------------------------------------------------------------
--
-- Theorem 1 (Internalisation principle), p. 29 [1]


prefix : ∀{m} → Cx m → Cx m
prefix ∅               = ∅
prefix (Γ , ⟨ n , A ⟩) = prefix Γ , ⟨ suc n , A ⟩


in∈ : ∀{n A m k} {Γ : Cx m}
    → ⟨ n , A ⟩ ∈[ k ] Γ
    → ⟨ suc n , A ⟩ ∈[ k ] prefix Γ
in∈ 𝐙     = 𝐙
in∈ (𝐒 i) = 𝐒 (in∈ i)


in⊢ : ∀{A m} {Γ : Cx m}
    → Γ ⊢ A
    → Σ Tm λ t → prefix Γ ⊢ t ∶ A
in⊢ (𝒗_ {n} {k} i)
    = let j = in∈ i in
        ⟨ 𝑣 k
        , 𝒗 j
        ⟩
in⊢ (𝝀ⁿ_ {n} {𝐭} D)
    = let ⟨ s , C ⟩ = in⊢ D in
        ⟨ 𝜆[ suc n ] s
        , 𝝀ⁿ_ {𝐭 = s ∷ 𝐭} C
        ⟩
in⊢ (_∙ⁿ_ {n} {𝐭} {𝐬} Dₜ Dₛ)
    = let ⟨ sₜ , Cₜ ⟩ = in⊢ Dₜ
          ⟨ sₛ , Cₛ ⟩ = in⊢ Dₛ in
        ⟨ sₜ ∘[ suc n ] sₛ
        , _∙ⁿ_ {𝐭 = sₜ ∷ 𝐭} {𝐬 = sₛ ∷ 𝐬} Cₜ Cₛ
        ⟩
in⊢ (𝒑ⁿ⟨_,_⟩ {n} {𝐭} {𝐬} Dₜ Dₛ)
    = let ⟨ sₜ , Cₜ ⟩ = in⊢ Dₜ
          ⟨ sₛ , Cₛ ⟩ = in⊢ Dₛ in
        ⟨ 𝑝[ suc n ]⟨ sₜ , sₛ ⟩
        , 𝒑ⁿ⟨_,_⟩ {𝐭 = sₜ ∷ 𝐭} {𝐬 = sₛ ∷ 𝐬} Cₜ Cₛ
        ⟩
in⊢ (𝝅₀ⁿ_ {n} {𝐭} D)
    = let ⟨ s , C ⟩ = in⊢ D in
        ⟨ 𝜋₀[ suc n ] s
        , 𝝅₀ⁿ_ {𝐭 = s ∷ 𝐭} C
        ⟩
in⊢ (𝝅₁ⁿ_ {n} {𝐭} D)
    = let ⟨ s , C ⟩ = in⊢ D in
        ⟨ 𝜋₁[ suc n ] s
        , 𝝅₁ⁿ_ {𝐭 = s ∷ 𝐭} C
        ⟩
in⊢ (⬆ⁿ_ {n} {𝐭} D)
    = let ⟨ s , C ⟩ = in⊢ D in
        ⟨ ⇑[ suc n ] s
        , ⬆ⁿ_ {𝐭 = s ∷ 𝐭} C
        ⟩
in⊢ (⬇ⁿ_ {n} {𝐭} D)
    = let ⟨ s , C ⟩ = in⊢ D in
        ⟨ ⇓[ suc n ] s
        , ⬇ⁿ_ {𝐭 = s ∷ 𝐭} C
        ⟩


-- --------------------------------------------------------------------------
--
-- Constructive necessitation


nec : ∀{A}
    → ⊩ A
    → Σ Tm λ t → ⊩ t ∶ A
nec = in⊢


I²′ : ∀{A} → Σ Tm λ t
    → ⊩  t  ∶  (A ⊃ A)
I²′ = nec I

I³′ : ∀{A} → Σ Tm λ t
    → ⊩  t  ∶  𝜆 𝑣 0  ∶  (A ⊃ A)
I³′ = nec I²

I⁴′ : ∀{A} → Σ Tm λ t
    → ⊩  t  ∶  𝜆² 𝑣 0  ∶  𝜆 𝑣 0  ∶  (A ⊃ A)
I⁴′ = nec I³


I³″ : ∀{A} → Σ Tm λ t
    → ⊩  t  ∶  𝜆 𝑣 0  ∶  (A ⊃ A)
I³″ = nec (proj₂ (I²′))

I⁴″ : ∀{A} → Σ Tm λ t
    → ⊩  t  ∶ 𝜆² 𝑣 0  ∶  𝜆 𝑣 0  ∶  (A ⊃ A)
I⁴″ = nec (proj₂ (I³′))
