-- More readable alternative to the stdlib

module Prelude-WellFounded where

open import Function using (_on_)
open import Level using (_⊔_)
open import Relation.Binary using (Rel)
open import Relation.Unary using (_⊆_ ; Pred)


-- For showing that _<_ is well-founded
module _ where
  open import Data.Nat using (_≤_ ; _<_ ; s≤s ; suc ; z≤n ; zero)
  open import Relation.Binary.PropositionalEquality using (_≢_ ; refl)
  open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)

  sm≢sn⇒m≢n : ∀ {n m} → suc m ≢ suc n → m ≢ n
  sm≢sn⇒m≢n sn≢sn refl = refl ↯ sn≢sn

  m≤n∧m≢n⇒m<n : ∀ {n m} → m ≤ n → m ≢ n → m < n
  m≤n∧m≢n⇒m<n {zero}  {zero}  z≤n       z≢z   = refl ↯ z≢z
  m≤n∧m≢n⇒m<n {zero}  {suc m} ()        sm≢z
  m≤n∧m≢n⇒m<n {suc n} {zero}  z≤n       z≢sn  = s≤s z≤n
  m≤n∧m≢n⇒m<n {suc n} {suc m} (s≤s m≤n) sm≢sn = s≤s (m≤n∧m≢n⇒m<n m≤n (sm≢sn⇒m≢n sm≢sn))


-- AKA WfRec
Below : ∀ {a p ℓ} {A : Set a} → Rel A ℓ → Pred A p → A → Set (a ⊔ p ⊔ ℓ)
Below _<_ P x = ∀ y → y < x → P y

-- Not in the stdlib
Closed : ∀ {a p ℓ} {A : Set a} → Rel A ℓ → Pred A p → Set (a ⊔ p ⊔ ℓ)
Closed _<_ P = ∀ x → Below _<_ P x → P x

-- Subtly different type
data Accessible {a ℓ} {A : Set a} (_<_ : Rel A ℓ) : A → Set (a ⊔ ℓ) where
  access : Closed _<_ (Accessible _<_)

-- Not in the stdlib
AccessibleBelow : ∀ {a ℓ} {A : Set a} → Rel A ℓ → A → Set (a ⊔ ℓ)
AccessibleBelow _<_ x = Below _<_ (Accessible _<_) x

WellFounded : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
WellFounded _<_ = ∀ x → Accessible _<_ x

-- Not in the stdlib
WellFoundedBelow : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
WellFoundedBelow _<_ = ∀ x → AccessibleBelow _<_ x

InductionPrinciple : ∀ {a p ℓ} {A : Set a} → Rel A ℓ → Pred A p → Set (a ⊔ p ⊔ ℓ)
InductionPrinciple _<_ P = Closed _<_ P → ∀ x → P x

-- Obscured by the stdlib
inductionLoop : ∀ {a p ℓ} {A : Set a} {_<_ : Rel A ℓ} {P : Pred A p} {x : A} →
                Closed _<_ P → Accessible _<_ x → Below _<_ P x
inductionLoop h (access x g) y y<x = h y (inductionLoop h (g y y<x))

-- AKA wfRec
inductionPrinciple : ∀ {a p ℓ} {A : Set a} {_<_ : Rel A ℓ} {P : Pred A p} →
                     WellFounded _<_ → InductionPrinciple _<_ P
inductionPrinciple wf h x = h x (inductionLoop h (wf x))


module _ where
  open import Data.Nat using (_≤_ ; _<_ ; _≟_ ; ℕ ; s≤s ; suc ; zero)
  open import Relation.Binary.PropositionalEquality using (refl)
  open import Relation.Nullary using (no ; yes)

  <-wfb : WellFoundedBelow _<_
  <-wfb zero    m ()
  <-wfb (suc n) m (s≤s m≤n) with m ≟ n
  ... | yes refl = access n (<-wfb n)
  ... | no m≢n   = <-wfb n m (m≤n∧m≢n⇒m<n m≤n m≢n)

  <-wf : WellFounded _<_
  <-wf n = access n (<-wfb n)

  <-ip : ∀ {ℓ} {P : ℕ → Set ℓ} → InductionPrinciple _<_ P
  <-ip = inductionPrinciple <-wf


-- Now we can see why _≤′_ is more suitable to well-founded induction!
module _ where
  open import Data.Nat using (_≤′_ ; _<′_ ; ℕ ; ≤′-refl ; ≤′-step ; suc ; zero)

  <′-wfb : WellFoundedBelow _<′_
  <′-wfb zero     m ()
  <′-wfb (suc n) .n ≤′-refl        = access n (<′-wfb n)
  <′-wfb (suc n)  m (≤′-step m<′n) = <′-wfb n m m<′n

  <′-wf : WellFounded _<′_
  <′-wf n = access n (<′-wfb n)

  <′-ip : ∀ {ℓ} {P : ℕ → Set ℓ} → InductionPrinciple _<′_ P
  <′-ip = inductionPrinciple <′-wf


module Subrelation {a ℓ₁ ℓ₂} {A : Set a} {_<₁_ : Rel A ℓ₁} {_<₂_ : Rel A ℓ₂}
                   (<₁⇒<₂ : ∀ {x y} → x <₁ y → x <₂ y) where
  accessible : Accessible _<₂_ ⊆ Accessible _<₁_
  accessible (access x rs) = access x (λ y y<x → accessible (rs y (<₁⇒<₂ y<x)))

  wellFounded : WellFounded _<₂_ → WellFounded _<₁_
  wellFounded wf = λ x → accessible (wf x)


module InverseImage {a b ℓ} {A : Set a} {B : Set b} {_<_ : Rel B ℓ}
                    (f : A → B) where
  accessible : ∀ {x} → Accessible _<_ (f x) → Accessible (_<_ on f) x
  accessible {x} (access fx rs) = access x (λ y fy<fx → accessible (rs (f y) fy<fx))

  wellFounded : WellFounded _<_ → WellFounded (_<_ on f)
  wellFounded wf = λ x → accessible (wf (f x))