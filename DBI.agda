----------------------------------------------------------------------------------------------------

-- de Bruijn indices

module DBI {𝓍} {X : Set 𝓍} where

open import Prelude public


----------------------------------------------------------------------------------------------------

infix 4 _∋_
data _∋_ : List X → X → Set where
  zero : ∀ {Γ A} → A ∷ Γ ∋ A
  suc  : ∀ {B Γ A} (i : Γ ∋ A) → B ∷ Γ ∋ A


----------------------------------------------------------------------------------------------------

-- TODO: delete?

injsuc : ∀ {Γ A B} {i i′ : Γ ∋ A} → suc i ≡ _∋_.suc {B} i′ → i ≡ i′
injsuc refl = refl

infix 4 _≟∋_
_≟∋_ : ∀ {Γ A} (i i′ : Γ ∋ A) → Dec (i ≡ i′)
zero  ≟∋ zero   = yes refl
zero  ≟∋ suc i′ = no λ ()
suc i ≟∋ zero   = no λ ()
suc i ≟∋ suc i′ with i ≟∋ i′
... | yes refl    = yes refl
... | no ¬eq      = no λ { refl → refl ↯ ¬eq }


----------------------------------------------------------------------------------------------------
