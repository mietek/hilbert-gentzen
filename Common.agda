module Common where

open import Agda.Builtin.Size public
  using (Size ; Size<_)
  renaming (ω to ∞)

open import Agda.Primitive public
  using (lsuc)

open import Data.Bool public
  using ()
  renaming (_∧_ to _∧ᴮ_ ; _∨_ to _∨ᴮ_ ; not to ¬ᴮ_)

open import Data.Empty public
  using ()
  renaming (⊥ to 𝟘 ; ⊥-elim to elim𝟘)

open import Data.Nat public
  using (ℕ ; zero ; suc)
  renaming (_≟_ to _≟ᴺ_)

open import Data.Product public
  using (Σ ; ∃ ; _×_ ; _,_)
  renaming (proj₁ to π₁ ; proj₂ to π₂)

open import Data.Sum public
  using (_⊎_)
  renaming (inj₁ to ι₁ ; inj₂ to ι₂)

open import Data.Unit public
  using ()
  renaming (⊤ to 𝟙 ; tt to ∙)

open import Function public
  using (_∘_ ; _$_ ; id ; const)
  renaming (_ˢ_ to ap)

open import Relation.Binary.PropositionalEquality public
  using (_≡_ ; _≢_ ; refl ; trans ; sym ; cong ; cong₂ ; subst)

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


-- Elimination for disjoint unions.

elim⊎ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
        → A ⊎ B → (A → C) → (B → C) → C
elim⊎ (ι₁ x) f g = f x
elim⊎ (ι₂ y) f g = g y


-- Triple-argument congruence.

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x x′ y y′ z z′}
        → x ≡ x′ → y ≡ y′ → z ≡ z′ → f x y z ≡ f x′ y′ z′
cong₃ f refl refl refl = refl


-- Composition, supremum, and infimum for relations.

module _ {W : Set} where
  _⨾_ : (W → W → Set) → (W → W → Set) → (W → W → Set)
  _R_ ⨾ _Q_ = λ w w′ → ∃ (λ v → w R v × v Q w′)

  _⊔_ : (W → W → Set) → (W → W → Set) → (W → W → Set)
  _R_ ⊔ _Q_ = λ w w′ → ∃ (λ v → w R v × w′ Q v)

  _⊓_ : (W → W → Set) → (W → W → Set) → (W → W → Set)
  _R_ ⊓ _Q_ = λ w w′ → ∃ (λ v → v R w × v Q w′)
