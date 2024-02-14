----------------------------------------------------------------------------------------------------

-- first-order renamings

module FOR {𝓍} {X : Set 𝓍} where

open import DBI public


----------------------------------------------------------------------------------------------------

infix 4 _⊆_
data _⊆_ : List X → List X → Set 𝓍 where
  []  : ∀ {Γ} → [] ⊆ Γ
  _∷_ : ∀ {Γ Γ′ A} (i : Γ′ ∋ A) (is : Γ ⊆ Γ′) → A ∷ Γ ⊆ Γ′

stop⊆ : [] ⊆ []
stop⊆ = []

wk⊆ : ∀ {B Γ Γ′} → Γ ⊆ Γ′ → Γ ⊆ B ∷ Γ′
wk⊆ []       = []
wk⊆ (i ∷ is) = suc i ∷ wk⊆ is

lift⊆ : ∀ {B Γ Γ′} → Γ ⊆ Γ′ → B ∷ Γ ⊆ B ∷ Γ′
lift⊆ is = zero ∷ wk⊆ is

id⊆ refl⊆ : ∀ {Γ} → Γ ⊆ Γ
id⊆ {[]}    = []
id⊆ {A ∷ Γ} = lift⊆ id⊆
refl⊆ = id⊆


----------------------------------------------------------------------------------------------------

ren∋ : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ∋ A → Γ′ ∋ A
ren∋ (j ∷ js) zero    = j
ren∋ (j ∷ js) (suc i) = ren∋ js i

wk∋ : ∀ {B Γ A} → Γ ∋ B → A ∷ Γ ∋ B
wk∋ i = ren∋ (wk⊆ id⊆) i

eqwkren∋ : ∀ {B Γ Γ′ A} (js : Γ ⊆ Γ′) (i : Γ ∋ A) →
           ren∋ (wk⊆ js) i ≡ (_∋_.suc {B = B} ∘ ren∋ js) i
eqwkren∋ (j ∷ js) zero    = refl
eqwkren∋ (j ∷ js) (suc i) = eqwkren∋ js i

idren∋ : ∀ {Γ A} (i : Γ ∋ A) → ren∋ id⊆ i ≡ i
idren∋ zero    = refl
idren∋ (suc i) = eqwkren∋ id⊆ i ⋮ suc & idren∋ i

_∘⊆_ : ∀ {Γ Γ′ Γ″} → Γ′ ⊆ Γ″ → Γ ⊆ Γ′ → Γ ⊆ Γ″
is′ ∘⊆ []       = []
is′ ∘⊆ (i ∷ is) = ren∋ is′ i ∷ (is′ ∘⊆ is)

trans⊆ _○_ : ∀ {Γ Γ′ Γ″} → Γ ⊆ Γ′ → Γ′ ⊆ Γ″ → Γ ⊆ Γ″
trans⊆ = flip _∘⊆_
_○_ = trans⊆

compren∋ : ∀ {Γ Γ′ Γ″ A} (js′ : Γ′ ⊆ Γ″) (js : Γ ⊆ Γ′) (i : Γ ∋ A) →
           ren∋ (js′ ∘⊆ js) i ≡ (ren∋ js′ ∘ ren∋ js) i
compren∋ (j′ ∷ js′) (j ∷ js) zero    = refl
compren∋ (j′ ∷ js′) (j ∷ js) (suc i) = compren∋ (j′ ∷ js′) js i


----------------------------------------------------------------------------------------------------

lid⊆ : ∀ {Γ Γ′} (is : Γ ⊆ Γ′) → id⊆ ∘⊆ is ≡ is
lid⊆ []       = refl
lid⊆ (i ∷ is) = _∷_ & idren∋ i ⊗ lid⊆ is

eq⊆ : ∀ {B Γ Γ′ Γ″} (i′ : Γ″ ∋ B) (is′ : Γ′ ⊆ Γ″) (is : Γ ⊆ Γ′) →
      (i′ ∷ is′) ∘⊆ (wk⊆ is) ≡ is′ ∘⊆ is
eq⊆ i′ is′ []       = refl
eq⊆ i′ is′ (i ∷ is) = (ren∋ is′ i ∷_) & eq⊆ i′ is′ is

eqwk⊆ : ∀ {B Γ Γ′ Γ″} (is′ : Γ′ ⊆ Γ″) (is : Γ ⊆ Γ′) →
        (lift⊆ is′) ∘⊆ (wk⊆ is) ≡ wk⊆ {B} (is′ ∘⊆ is)
eqwk⊆ is′ []       = refl
eqwk⊆ is′ (i ∷ is) = _∷_ & eqwkren∋ is′ i ⊗ eqwk⊆ is′ is

eqlift⊆ : ∀ {B Γ Γ′ Γ″} (is′ : Γ′ ⊆ Γ″) (is : Γ ⊆ Γ′) →
          (lift⊆ is′) ∘⊆ (lift⊆ is) ≡ lift⊆ {B} (is′ ∘⊆ is)
eqlift⊆ is′ []       = refl
eqlift⊆ is′ (i ∷ is) = (zero ∷_) & eqwk⊆ is′ (i ∷ is)

rid⊆ : ∀ {Γ Γ′} (is : Γ ⊆ Γ′) → is ∘⊆ id⊆ ≡ is
rid⊆ []       = refl
rid⊆ (i ∷ is) = (i ∷_) & (eq⊆ i is id⊆ ⋮ rid⊆ is)

ass⊆ : ∀ {Γ Γ′ Γ″ Γ‴} (is″ : Γ″ ⊆ Γ‴) (is′ : Γ′ ⊆ Γ″) (is : Γ ⊆ Γ′) →
       is″ ∘⊆ (is′ ∘⊆ is) ≡ (is″ ∘⊆ is′) ∘⊆ is
ass⊆ is″ is′ []       = refl
ass⊆ is″ is′ (i ∷ is) = _∷_ & compren∋ is″ is′ i ⁻¹ ⊗ ass⊆ is″ is′ is


----------------------------------------------------------------------------------------------------
