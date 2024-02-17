----------------------------------------------------------------------------------------------------

-- simply typed lambda calculus with negative types

module STLC-Negative where

open import Kit1 public


----------------------------------------------------------------------------------------------------

infixr 18 _⌜⊃⌝_
infixl 19 _⌜∧⌝_
data Ty : Set where
  _⌜⊃⌝_ : ∀ (A B : Ty) → Ty
  _⌜∧⌝_ : ∀ (A B : Ty) → Ty
  ⌜𝟙⌝   : Ty

infixr 18 _`⫗_
_`⫗_ : ∀ (A B : Ty) → Ty
A `⫗ B = (A ⌜⊃⌝ B) ⌜∧⌝ (B ⌜⊃⌝ A)

open TyKit Ty public

infix 3 _⊢_
infixl 18 _⌜$⌝_
data _⊢_ (Γ : Ctx) : Ty → Set where
  var    : ∀ {A} (i : Γ ∋ A) → Γ ⊢ A
  ⌜λ⌝    : ∀ {A B} (t : Γ , A ⊢ B) → Γ ⊢ A ⌜⊃⌝ B
  _⌜$⌝_  : ∀ {A B} (t₁ : Γ ⊢ A ⌜⊃⌝ B) (t₂ : Γ ⊢ A) → Γ ⊢ B
  _⌜,⌝_  : ∀ {A B} (t₁ : Γ ⊢ A) (t₂ : Γ ⊢ B) → Γ ⊢ A ⌜∧⌝ B
  ⌜fst⌝  : ∀ {A B} (t : Γ ⊢ A ⌜∧⌝ B) → Γ ⊢ A
  ⌜snd⌝  : ∀ {A B} (t : Γ ⊢ A ⌜∧⌝ B) → Γ ⊢ B
  ⌜unit⌝ : Γ ⊢ ⌜𝟙⌝

open TmKit (kit _⊢_) public


----------------------------------------------------------------------------------------------------

ren : ∀ {Γ Γ′ A} → Γ ⊑ Γ′ → Γ ⊢ A → Γ′ ⊢ A
ren ρ (var i)     = var (ren∋ ρ i)
ren ρ (⌜λ⌝ t)     = ⌜λ⌝ (ren (lift⊑ ρ) t)
ren ρ (t₁ ⌜$⌝ t₂) = ren ρ t₁ ⌜$⌝ ren ρ t₂
ren ρ (t₁ ⌜,⌝ t₂) = ren ρ t₁ ⌜,⌝ ren ρ t₂
ren ρ (⌜fst⌝ t)   = ⌜fst⌝ (ren ρ t)
ren ρ (⌜snd⌝ t)   = ⌜snd⌝ (ren ρ t)
ren ρ ⌜unit⌝      = ⌜unit⌝

open RenKit (kit var ren) public

sub : ∀ {Γ Ξ A} → Ξ ⊢§ Γ → Γ ⊢ A → Ξ ⊢ A
sub σ (var i)     = sub∋ σ i
sub σ (⌜λ⌝ t)     = ⌜λ⌝ (sub (lift§ σ) t)
sub σ (t₁ ⌜$⌝ t₂) = sub σ t₁ ⌜$⌝ sub σ t₂
sub σ (t₁ ⌜,⌝ t₂) = sub σ t₁ ⌜,⌝ sub σ t₂
sub σ (⌜fst⌝ t)   = ⌜fst⌝ (sub σ t)
sub σ (⌜snd⌝ t)   = ⌜snd⌝ (sub σ t)
sub σ ⌜unit⌝      = ⌜unit⌝

open SubKit (kit renkit sub) public


----------------------------------------------------------------------------------------------------

module BetaShortDefEq where
  infix 4 _≝_
  data _≝_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
    refl≝   : ∀ {A} {t : Γ ⊢ A} → t ≝ t
    sym≝    : ∀ {A} {t t′ : Γ ⊢ A} (eq : t ≝ t′) → t′ ≝ t
    trans≝  : ∀ {A} {t t′ t″ : Γ ⊢ A} (eq : t ≝ t′) (eq′ : t′ ≝ t″) → t ≝ t″
    congλ   : ∀ {A B} {t t′ : Γ , A ⊢ B} (eq : t ≝ t′) → ⌜λ⌝ t ≝ ⌜λ⌝ t′
    cong$   : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (eq₁ : t₁ ≝ t₁′) (eq₂ : t₂ ≝ t₂′) →
              t₁ ⌜$⌝ t₂ ≝ t₁′ ⌜$⌝ t₂′
    cong,   : ∀ {A B} {t₁ t₁′ : Γ ⊢ A} {t₂ t₂′ : Γ ⊢ B} (eq₁ : t₁ ≝ t₁′) (eq₂ : t₂ ≝ t₂′) →
              t₁ ⌜,⌝ t₂ ≝ t₁′ ⌜,⌝ t₂′
    congfst : ∀ {A B} {t t′ : Γ ⊢ A ⌜∧⌝ B} (eq : t ≝ t′) → ⌜fst⌝ t ≝ ⌜fst⌝ t′
    congsnd : ∀ {A B} {t t′ : Γ ⊢ A ⌜∧⌝ B} (eq : t ≝ t′) → ⌜snd⌝ t ≝ ⌜snd⌝ t′
    βred⊃   : ∀ {A B} {t₁ : Γ , A ⊢ B} {t₂ : Γ ⊢ A} {t′} (eq : t′ ≡ t₁ [ t₂ ]) →
              ⌜λ⌝ t₁ ⌜$⌝ t₂ ≝ t′
    βred∧₁  : ∀ {A B} {t₁ : Γ ⊢ A} {t₂ : Γ ⊢ B} → ⌜fst⌝ (t₁ ⌜,⌝ t₂) ≝ t₁
    βred∧₂  : ∀ {A B} {t₁ : Γ ⊢ A} {t₂ : Γ ⊢ B} → ⌜snd⌝ (t₁ ⌜,⌝ t₂) ≝ t₂

  open DefEqKit (kit tmkit (λ {Γ} {A} {t} → refl≝ {t = t}) sym≝ trans≝) public

module BetaShortEtaLongDefEq where
  infix 4 _≝_
  data _≝_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
    refl≝   : ∀ {A} {t : Γ ⊢ A} → t ≝ t
    sym≝    : ∀ {A} {t t′ : Γ ⊢ A} (eq : t ≝ t′) → t′ ≝ t
    trans≝  : ∀ {A} {t t′ t″ : Γ ⊢ A} (eq : t ≝ t′) (eq′ : t′ ≝ t″) → t ≝ t″
    congλ   : ∀ {A B} {t t′ : Γ , A ⊢ B} (eq : t ≝ t′) → ⌜λ⌝ t ≝ ⌜λ⌝ t′
    cong$   : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (eq₁ : t₁ ≝ t₁′) (eq₂ : t₂ ≝ t₂′) →
              t₁ ⌜$⌝ t₂ ≝ t₁′ ⌜$⌝ t₂′
    cong,   : ∀ {A B} {t₁ t₁′ : Γ ⊢ A} {t₂ t₂′ : Γ ⊢ B} (eq₁ : t₁ ≝ t₁′) (eq₂ : t₂ ≝ t₂′) →
              t₁ ⌜,⌝ t₂ ≝ t₁′ ⌜,⌝ t₂′
    congfst : ∀ {A B} {t t′ : Γ ⊢ A ⌜∧⌝ B} (eq : t ≝ t′) → ⌜fst⌝ t ≝ ⌜fst⌝ t′
    congsnd : ∀ {A B} {t t′ : Γ ⊢ A ⌜∧⌝ B} (eq : t ≝ t′) → ⌜snd⌝ t ≝ ⌜snd⌝ t′
    βred⊃   : ∀ {A B} {t₁ : Γ , A ⊢ B} {t₂ : Γ ⊢ A} {t′} (eq : t′ ≡ t₁ [ t₂ ]) →
              ⌜λ⌝ t₁ ⌜$⌝ t₂ ≝ t′
    βred∧₁  : ∀ {A B} {t₁ : Γ ⊢ A} {t₂ : Γ ⊢ B} → ⌜fst⌝ (t₁ ⌜,⌝ t₂) ≝ t₁
    βred∧₂  : ∀ {A B} {t₁ : Γ ⊢ A} {t₂ : Γ ⊢ B} → ⌜snd⌝ (t₁ ⌜,⌝ t₂) ≝ t₂
    ηexp⊃   : ∀ {A B} {t : Γ ⊢ A ⌜⊃⌝ B} {t′} (eq : t′ ≡ wk t) → t ≝ ⌜λ⌝ (t′ ⌜$⌝ var zero)
    ηexp,   : ∀ {A B} {t : Γ ⊢ A ⌜∧⌝ B} → t ≝ (⌜fst⌝ t) ⌜,⌝ (⌜snd⌝ t)
    ηexp𝟙   : ∀ {t : Γ ⊢ ⌜𝟙⌝} → t ≝ ⌜unit⌝

  open DefEqKit (kit tmkit (λ {Γ} {A} {t} → refl≝ {t = t}) sym≝ trans≝) public


----------------------------------------------------------------------------------------------------

infix 4 _≟Ty_
_≟Ty_ : ∀ (A A′ : Ty) → Dec (A ≡ A′)
A ⌜⊃⌝ B ≟Ty A′ ⌜⊃⌝ B′     with A ≟Ty A′ | B ≟Ty B′
... | no ¬eq₁  | _          = no λ { refl → refl ↯ ¬eq₁ }
... | yes refl | no ¬eq₂    = no λ { refl → refl ↯ ¬eq₂ }
... | yes refl | yes refl   = yes refl
A ⌜⊃⌝ B ≟Ty A′ ⌜∧⌝ B′     = no λ ()
A ⌜⊃⌝ B ≟Ty ⌜𝟙⌝           = no λ ()
A ⌜∧⌝ B ≟Ty A′ ⌜⊃⌝ B′     = no λ ()
A ⌜∧⌝ B ≟Ty A′ ⌜∧⌝ B′     with A ≟Ty A′ | B ≟Ty B′
... | no ¬eq₁  | _          = no λ { refl → refl ↯ ¬eq₁ }
... | yes refl | no ¬eq₂    = no λ { refl → refl ↯ ¬eq₂ }
... | yes refl | yes refl   = yes refl
A ⌜∧⌝ B ≟Ty ⌜𝟙⌝           = no λ ()
⌜𝟙⌝     ≟Ty A′ ⌜⊃⌝ B′     = no λ ()
⌜𝟙⌝     ≟Ty A′ ⌜∧⌝ B′     = no λ ()
⌜𝟙⌝     ≟Ty ⌜𝟙⌝           = yes refl

infix 4 _≟_
_≟_ : ∀ {Γ A} (t t′ : Γ ⊢ A) → Dec (t ≡ t′)
var i     ≟ var i′          with i ≟∋ i′
... | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
... | yes refl                = yes refl
var i     ≟ ⌜λ⌝ t′            = no λ ()
var i     ≟ t₁′ ⌜$⌝ t₂′       = no λ ()
var i     ≟ t₁′ ⌜,⌝ t₂′       = no λ ()
var i     ≟ ⌜fst⌝ t′          = no λ ()
var i     ≟ ⌜snd⌝ t′          = no λ ()
var i     ≟ ⌜unit⌝            = no λ ()
⌜λ⌝ t     ≟ var i′            = no λ ()
⌜λ⌝ t     ≟ ⌜λ⌝ t′          with t ≟ t′
... | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
... | yes refl                = yes refl
⌜λ⌝ t     ≟ t₁′ ⌜$⌝ t₂′       = no λ ()
⌜λ⌝ t     ≟ ⌜fst⌝ t′          = no λ ()
⌜λ⌝ t     ≟ ⌜snd⌝ t′          = no λ ()
t₁ ⌜$⌝ t₂ ≟ var i′            = no λ ()
t₁ ⌜$⌝ t₂ ≟ ⌜λ⌝ t′            = no λ ()
t₁ ⌜$⌝ t₂ ≟ t₁′ ⌜$⌝ t₂′     with ty t₁ ≟Ty ty t₁′
... | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
... | yes refl                with t₁ ≟ t₁′ | t₂ ≟ t₂′
...   | no ¬eq₁  | _            = no λ { refl → refl ↯ ¬eq₁ }
...   | yes refl | no ¬eq₂      = no λ { refl → refl ↯ ¬eq₂ }
...   | yes refl | yes refl     = yes refl
t₁ ⌜$⌝ t₂ ≟ t₁′ ⌜,⌝ t₂′       = no λ ()
t₁ ⌜$⌝ t₂ ≟ ⌜fst⌝ t′          = no λ ()
t₁ ⌜$⌝ t₂ ≟ ⌜snd⌝ t′          = no λ ()
t₁ ⌜$⌝ t₂ ≟ ⌜unit⌝            = no λ ()
t₁ ⌜,⌝ t₂ ≟ var i′            = no λ ()
t₁ ⌜,⌝ t₂ ≟ t₁′ ⌜$⌝ t₂′       = no λ ()
t₁ ⌜,⌝ t₂ ≟ t₁′ ⌜,⌝ t₂′     with t₁ ≟ t₁′ | t₂ ≟ t₂′
... | no ¬eq₁  | _            = no λ { refl → refl ↯ ¬eq₁ }
... | yes refl | no ¬eq₂      = no λ { refl → refl ↯ ¬eq₂ }
... | yes refl | yes refl     = yes refl
t₁ ⌜,⌝ t₂ ≟ ⌜fst⌝ t′          = no λ ()
t₁ ⌜,⌝ t₂ ≟ ⌜snd⌝ t′          = no λ ()
⌜fst⌝ t   ≟ var i′            = no λ ()
⌜fst⌝ t   ≟ ⌜λ⌝ t′            = no λ ()
⌜fst⌝ t   ≟ t₁′ ⌜$⌝ t₂′       = no λ ()
⌜fst⌝ t   ≟ t₁′ ⌜,⌝ t₂′       = no λ ()
⌜fst⌝ t   ≟ ⌜fst⌝ t′        with ty t ≟Ty ty t′
... | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
... | yes refl                with t ≟ t′
...   | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
...   | yes refl                = yes refl
⌜fst⌝ t   ≟ ⌜snd⌝ t′          = no λ ()
⌜fst⌝ t   ≟ ⌜unit⌝            = no λ ()
⌜snd⌝ t   ≟ var i′            = no λ ()
⌜snd⌝ t   ≟ ⌜λ⌝ t′            = no λ ()
⌜snd⌝ t   ≟ t₁′ ⌜$⌝ t₂′       = no λ ()
⌜snd⌝ t   ≟ t₁′ ⌜,⌝ t₂′       = no λ ()
⌜snd⌝ t   ≟ ⌜fst⌝ t′          = no λ ()
⌜snd⌝ t   ≟ ⌜snd⌝ t′        with ty t ≟Ty ty t′
... | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
... | yes refl                with t ≟ t′
...   | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
...   | yes refl                = yes refl
⌜snd⌝ t   ≟ ⌜unit⌝            = no λ ()
⌜unit⌝    ≟ var i′            = no λ ()
⌜unit⌝    ≟ t₁′ ⌜$⌝ t₂′       = no λ ()
⌜unit⌝    ≟ ⌜fst⌝ t′          = no λ ()
⌜unit⌝    ≟ ⌜snd⌝ t′          = no λ ()
⌜unit⌝    ≟ ⌜unit⌝            = yes refl


----------------------------------------------------------------------------------------------------
