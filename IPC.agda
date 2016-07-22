module IPC where

open import Common.Context public


-- Propositions of intuitionistic propositional calculus.

infixl 7 _∧_
infixl 6 _∨_
infixr 5 _▷_
data Ty : Set where
  α_  : Atom → Ty
  _▷_ : Ty → Ty → Ty
  _∧_ : Ty → Ty → Ty
  ⊤  : Ty
  ⊥  : Ty
  _∨_ : Ty → Ty → Ty

¬_ : Ty → Ty
¬ A = A ▷ ⊥

infix 5 _⨝_
_⨝_ : Ty → Ty → Ty
A ⨝ B = (A ▷ B) ∧ (B ▷ A)