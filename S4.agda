{-

An implementation of the Pfenning-Davies reconstruction of S4
=============================================================

Miëtek Bak  <mietek@bak.io>


Work in progress.  Checked with Agda 2.4.2.5.

For easy editing with Emacs agda-mode, add to your .emacs file:

'(agda-input-user-translations
   (quote
    (("i" "⊃") ("ii" "⫗") ("e" "⊢") ("ee" "⊩") ("n" "¬")
     ("b" "□")
     ("mv" "𝒗") ("ml" "𝝀")
     ("mo" "∙")
     ("mp" "𝒑")
     ("mpi" "𝝅")
     ("mpi0" "𝝅₀")
     ("mpi1" "𝝅₁")
     ("mb" "■") ("m*" "★")
     ("mS" "𝐒") ("mZ" "𝐙")
     ("m0" "𝟎") ("m1" "𝟏") ("m2" "𝟐") ("m3" "𝟑") ("m4" "𝟒")
     ("C" "𝒞") ("D" "𝒟")
     ("N" "ℕ"))))


[1]: Pfenning, F., Davies, R. (2001) A judgmental reconstruction of modal logic.
     Mathematical Structures in Computer Science, vol. 11, no. 4, pp. 511–540.
     http://dx.doi.org/10.1017/S0960129501003322

-}

module S4 where

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)

infixl 9 𝒗_
infixl 8 𝝅₀_ 𝝅₁_
infixl 7 _∙_
infixr 6 ■_ ‼[_]_
infixr 5 𝝀_
infixr 4 □_
infixr 3 ¬_
infixl 3 _∧_
infixl 2 _∨_ _,_
infixr 1 _⊃_ _⫗_
infixr 0 _∣_⊢_ ⊩_


-- --------------------------------------------------------------------------
--
-- Untyped syntax


-- Type constructors
data Ty : Set where
  -- Falsehood
  ⊥ : Ty

  -- Implication
  _⊃_ : Ty → Ty → Ty

  -- Conjunction
  _∧_ : Ty → Ty → Ty

  -- Implicit provability
  □_ : Ty → Ty


-- --------------------------------------------------------------------------
--
-- Example types


-- Truth
⊤ : Ty
⊤ = ⊥ ⊃ ⊥

-- Negation
¬_ : Ty → Ty
¬ A = A ⊃ ⊥

-- Disjunction
_∨_ : Ty → Ty → Ty
A ∨ B = ¬ A ⊃ B

-- Equivalence
_⫗_ : Ty → Ty → Ty
A ⫗ B = (A ⊃ B) ∧ (B ⊃ A)


-- --------------------------------------------------------------------------
--
-- Typed syntax


-- Contexts
data Cx : Set where
  ∅   : Cx
  _,_ : Cx → Ty → Cx


-- Context membership evidence
data _∈_ : Ty → Cx → Set where
  𝐙 : ∀{A Γ}
      → A ∈ (Γ , A)

  𝐒_ : ∀{A B Γ}
      → A ∈ Γ
      → A ∈ (Γ , B)


-- Typed terms
data _∣_⊢_ (Δ Γ : Cx) : Ty → Set where
  -- Variable reference
  𝒗_ : ∀{A}
      → A ∈ Γ
      → Δ ∣ Γ ⊢ A

  -- Abstraction (⊃I)
  𝝀_ : ∀{A B}
      → Δ ∣ Γ , A ⊢ B
      → Δ ∣ Γ ⊢ A ⊃ B

  -- Application (⊃E)
  _∙_ : ∀{A B}
      → Δ ∣ Γ ⊢ A ⊃ B    → Δ ∣ Γ ⊢ A
      → Δ ∣ Γ ⊢ B

  -- Pairing (∧I)
  𝒑⟨_,_⟩ : ∀{A B}
      → Δ ∣ Γ ⊢ A        → Δ ∣ Γ ⊢ B
      → Δ ∣ Γ ⊢ A ∧ B

  -- 0th projection (∧E₀)
  𝝅₀_ : ∀{A B}
      → Δ ∣ Γ ⊢ A ∧ B
      → Δ ∣ Γ ⊢ A

  -- 1st projection (∧E₁)
  𝝅₁_ : ∀{A B}
      → Δ ∣ Γ ⊢ A ∧ B
      → Δ ∣ Γ ⊢ B

  -- Validity variable reference
  𝒗*_ : ∀{A}
      → A ∈ Δ
      → Δ ∣ Γ ⊢ A

  -- Boxing (□I)
  ■_ : ∀{A}
      → Δ ∣ ∅ ⊢ A
      → Δ ∣ Γ ⊢ □ A

  -- Unboxing (□E)
  ‼[_]_ : ∀{A C}
      → Δ ∣ Γ ⊢ □ A      → Δ , A ∣ Γ ⊢ C
      → Δ ∣ Γ ⊢ C


⊩_ : Ty → Set
⊩ A = ∀{Δ Γ} → Δ ∣ Γ ⊢ A


-- --------------------------------------------------------------------------
--
-- Notation for context membership evidence


𝟎 : ∀{A Γ}
    → A ∈ (Γ , A)
𝟎 = 𝐙

𝟏 : ∀{A B Γ}
    → A ∈ (Γ , A , B)
𝟏 = 𝐒 𝟎

𝟐 : ∀{A B C Γ}
    → A ∈ (Γ , A , B , C)
𝟐 = 𝐒 𝟏

𝟑 : ∀{A B C D Γ}
    → A ∈ (Γ , A , B , C , D)
𝟑 = 𝐒 𝟐

𝟒 : ∀{A B C D E Γ}
    → A ∈ (Γ , A , B , C , D , E)
𝟒 = 𝐒 𝟑


-- --------------------------------------------------------------------------
--
-- Some S4 theorems at levels 1, 2, and 3


module SKICombinators where
  I : ∀{A}
      → ⊩ A ⊃ A
  I = 𝝀 𝒗 𝟎

  I² : ∀{A}
      → ⊩ □ (A ⊃ A)
  I² = ■ (𝝀 𝒗 𝟎)

  I³ : ∀{A}
      → ⊩ □ □ (A ⊃ A)
  I³ = ■ ■ (𝝀 𝒗 𝟎)


  K : ∀{A B}
      → ⊩ A ⊃ B ⊃ A
  K = 𝝀 𝝀 𝒗 𝟏

  K² : ∀{A B}
      → ⊩ □ (A ⊃ B ⊃ A)
  K² = ■ (𝝀 𝝀 𝒗 𝟏)

  K³ : ∀{A B}
      → ⊩ □ □ (A ⊃ B ⊃ A)
  K³ = ■ ■ (𝝀 𝝀 𝒗 𝟏)


  S : ∀{A B C}
      → ⊩ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
  S = 𝝀 𝝀 𝝀 (𝒗 𝟐 ∙ 𝒗 𝟎) ∙ (𝒗 𝟏 ∙ 𝒗 𝟎)

  S² : ∀{A B C}
      → ⊩ □ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
  S² = ■ (𝝀 𝝀 𝝀 (𝒗 𝟐 ∙ 𝒗 𝟎) ∙ (𝒗 𝟏 ∙ 𝒗 𝟎))

  S³ : ∀{A B C}
      → ⊩ □ □ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
  S³ = ■ ■ (𝝀 𝝀 𝝀 (𝒗 𝟐 ∙ 𝒗 𝟎) ∙ (𝒗 𝟏 ∙ 𝒗 𝟎))


-- --------------------------------------------------------------------------
--
-- S4 axioms at levels 1 and 2


module S4Axioms where
  K : ∀{A B}
      → ⊩ □ (A ⊃ B) ⊃ □ A ⊃ □ B
  K = 𝝀 𝝀 ‼[ 𝒗 𝟏 ] ‼[ 𝒗 𝟎 ] ■ 𝒗* 𝟏 ∙ 𝒗* 𝟎

  K² : ∀{A B}
      → ⊩ □ (□ (A ⊃ B) ⊃ □ A ⊃ □ B)
  K² = ■ (𝝀 𝝀 ‼[ 𝒗 𝟏 ] ‼[ 𝒗 𝟎 ] ■ 𝒗* 𝟏 ∙ 𝒗* 𝟎)


  T : ∀{A}
      → ⊩ □ A ⊃ A
  T = 𝝀 ‼[ 𝒗 𝟎 ] 𝒗* 𝟎

  T² : ∀{A}
      → ⊩ □ (□ A ⊃ A)
  T² = ■ (𝝀 ‼[ 𝒗 𝟎 ] 𝒗* 𝟎)


  #4 : ∀{A}
      → ⊩ □ A ⊃ □ □ A
  #4 = 𝝀 ‼[ 𝒗 𝟎 ] ■ ■ 𝒗* 𝟎

  #4² : ∀{A}
      → ⊩ □ (□ A ⊃ □ □ A)
  #4² = ■ (𝝀 ‼[ 𝒗 𝟎 ] ■ ■ 𝒗* 𝟎)


-- --------------------------------------------------------------------------
--
-- Some more S4 theorems


module Example1 where
  E11 : ∀{A}
      → ⊩ □ (□ A ⊃ A)
  E11 = S4Axioms.T²

  E12 : ∀{A}
      → ⊩ □ (□ A ⊃ □ □ A)
  E12 = S4Axioms.#4²

  E13 : ∀{A B}
      → ⊩ □ □ (A ⊃ B ⊃ A ∧ B)
  E13 = ■ ■ (𝝀 𝝀 𝒑⟨ 𝒗 𝟏 , 𝒗 𝟎 ⟩)

  E14 : ∀{A B}
      → ⊩ □ (□ A ⊃ □ B ⊃ □ □ (A ∧ B))
  E14 = ■ (𝝀 𝝀 ‼[ 𝒗 𝟏 ] ‼[ 𝒗 𝟎 ] ■ ■ 𝒑⟨ 𝒗* 𝟏 , 𝒗* 𝟎 ⟩)


module Example1a where
  E14a : ∀{A B}
      → ⊩ □ (□ A ⊃ □ B ⊃ □ (A ∧ B))
  E14a = ■ (𝝀 𝝀 ‼[ 𝒗 𝟏 ] ‼[ 𝒗 𝟎 ] ■ 𝒑⟨ 𝒗* 𝟏 , 𝒗* 𝟎 ⟩)

  E14b : ∀{A B}
      → ⊩ □ (□ A ∧ □ B ⊃ □ □ (A ∧ B))
  E14b = ■ (𝝀 ‼[ 𝝅₀ 𝒗 𝟎 ] ‼[ 𝝅₁ 𝒗 𝟎 ] ■ ■ 𝒑⟨ 𝒗* 𝟏 , 𝒗* 𝟎 ⟩)

  E14c : ∀{A B}
      → ⊩ □ (□ A ∧ □ B ⊃ □ (A ∧ B))
  E14c = ■ (𝝀 ‼[ 𝝅₀ 𝒗 𝟎 ] ‼[ 𝝅₁ 𝒗 𝟎 ] ■ 𝒑⟨ 𝒗* 𝟏 , 𝒗* 𝟎 ⟩)


-- --------------------------------------------------------------------------
--
-- Non-constructive necessitation


nec : ∀{A}
    → ⊩ A
    → ⊩ □ A
nec 𝒟 = ■ 𝒟


-- --------------------------------------------------------------------------
--
-- Example necessitated terms at levels 2, 3, and 4


module NecExample where
  I² : ∀{A}
      → ⊩ □ (A ⊃ A)
  I² = nec SKICombinators.I

  I³ : ∀{A}
      → ⊩ □ □ (A ⊃ A)
  I³ = nec I²

  I⁴ : ∀{A}
      → ⊩ □ □ □ (A ⊃ A)
  I⁴ = nec I³


  K² : ∀{A B}
      → ⊩ □ (A ⊃ B ⊃ A)
  K² = nec SKICombinators.K

  K³ : ∀{A B}
      → ⊩ □ □ (A ⊃ B ⊃ A)
  K³ = nec K²

  K⁴ : ∀{A B}
      → ⊩ □ □ □ (A ⊃ B ⊃ A)
  K⁴ = nec K³


  S² : ∀{A B C}
      → ⊩ □ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
  S² = nec SKICombinators.S

  S³ : ∀{A B C}
      → ⊩ □ □ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
  S³ = nec S²

  S⁴ : ∀{A B C}
      → ⊩ □ □ □ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
  S⁴ = nec S³
