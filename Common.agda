module Common where

open import Agda.Builtin.Size public
  using (Size ; Size<_)
  renaming (ω to ∞)

open import Agda.Primitive public
  using ()
  renaming (_⊔_ to _⊔ᴸ_ ; lsuc to sucᴸ)

open import Data.Bool public
  using (true ; false)
  renaming (Bool to 𝔹 ; _∧_ to _∧ᴮ_ ; _∨_ to _∨ᴮ_ ; not to ¬ᴮ_ ; if_then_else_ to ifᴮ)

open import Data.Empty public
  using ()
  renaming (⊥ to 𝟘 ; ⊥-elim to elim𝟘)

open import Data.Fin public
  using (Fin ; zero ; suc)

open import Data.List public
  using (List ; [] ; _∷_)

open import Data.Nat public
  using (ℕ ; zero ; suc)
  renaming (_≟_ to _≟ᴺ_)

open import Data.Sum public
  using (_⊎_)
  renaming (inj₁ to ι₁ ; inj₂ to ι₂)

open import Data.Unit public
  using ()
  renaming (⊤ to 𝟙 ; tt to ∙)

open import Function public
  using (_∘_ ; _$_)
  renaming (id to I ; const to K ; _ˢ_ to S)

open import Induction.WellFounded public
  using (Acc ; acc ; Well-founded)

open import Relation.Binary.PropositionalEquality public
  using (_≡_ ; _≢_ ; refl ; trans ; sym ; cong ; subst)
  renaming (cong₂ to cong²)

open import Relation.Nullary public
  using (Dec ; yes ; no)
  renaming (¬_ to Not)

open import Relation.Nullary.Decidable public
  using ()
  renaming (map′ to mapDec)

open import Relation.Nullary.Negation public
  using ()
  renaming (contradiction to _↯_)



-- Abstract symbols, or atoms.

abstract
  Atom : Set
  Atom = ℕ

  _≟ᵅ_ : (P P′ : Atom) → Dec (P ≡ P′)
  _≟ᵅ_ = _≟ᴺ_


-- Products, with custom fixities.

infixl 5 _,_
record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ᴸ b) where
  constructor _,_
  field
    π₁ : A
    π₂ : B π₁

open Σ public

∃ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ᴸ b)
∃ = Σ _

infix 2 _×_
_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ᴸ b)
A × B = Σ A (λ _ → B)


-- Elimination for disjoint unions.

elim⊎ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
        → A ⊎ B → (A → C) → (B → C) → C
elim⊎ (ι₁ x) f g = f x
elim⊎ (ι₂ y) f g = g y


-- Double-argument K combinator.

K² : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
     → A → B → C → A
K² x _ _ = x


-- Triple-argument congruence.

cong³ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x x′ y y′ z z′}
        → x ≡ x′ → y ≡ y′ → z ≡ z′ → f x y z ≡ f x′ y′ z′
cong³ f refl refl refl = refl


-- Iteration and recursion for naturals.

itᴺ : ∀ {a} {A : Set a} → ℕ → (A → A) → A → A
itᴺ zero    f x = x
itᴺ (suc n) f x = f (itᴺ n f x)

recᴺ : ∀ {a} {A : Set a} → ℕ → (ℕ → A → A) → A → A
recᴺ zero    f x = x
recᴺ (suc n) f x = f n (recᴺ n f x)


-- Iteration and recursion for lists.

itᴸ : ∀ {a b} {A : Set a} {B : Set b} → List A → (A → B → B) → B → B
itᴸ []       f x = x
itᴸ (k ∷ ks) f x = f k (itᴸ ks f x)

recᴸ : ∀ {a b} {A : Set a} {B : Set b} → List A → (A → List A → B → B) → B → B
recᴸ []       f x = x
recᴸ (k ∷ ks) f x = f k ks (recᴸ ks f x)


-- Composition, supremum, and infimum for relations.

module _ {W : Set} where
  _⨾_ : (W → W → Set) → (W → W → Set) → (W → W → Set)
  _R_ ⨾ _Q_ = λ w w′ → ∃ (λ v → w R v × v Q w′)

  _⊔_ : (W → W → Set) → (W → W → Set) → (W → W → Set)
  _R_ ⊔ _Q_ = λ w w′ → ∃ (λ v → w R v × w′ Q v)

  _⊓_ : (W → W → Set) → (W → W → Set) → (W → W → Set)
  _R_ ⊓ _Q_ = λ w w′ → ∃ (λ v → v R w × v Q w′)
