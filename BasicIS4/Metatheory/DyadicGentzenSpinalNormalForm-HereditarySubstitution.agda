module BasicIS4.Metatheory.DyadicGentzenSpinalNormalForm-HereditarySubstitution where

open import BasicIS4.Syntax.DyadicGentzenSpinalNormalForm public


-- Hereditary substitution and reduction.

mutual
  [_≔_]ⁿᶠ_ : ∀ {A B Γ Δ} → (i : A ∈ Γ) → Γ ∖ i ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ⁿᶠ B → Γ ∖ i ⁏ Δ ⊢ⁿᶠ B
  [ i ≔ s ]ⁿᶠ neⁿᶠ (spⁿᵉ j  xs y) with i ≟∈ j
  [ i ≔ s ]ⁿᶠ neⁿᶠ (spⁿᵉ .i xs y) | same   = reduce s ([ i ≔ s ]ˢᵖ xs) ([ i ≔ s ]ᵗᵖ y)
  [ i ≔ s ]ⁿᶠ neⁿᶠ (spⁿᵉ ._ xs y) | diff j = neⁿᶠ (spⁿᵉ j ([ i ≔ s ]ˢᵖ xs) ([ i ≔ s ]ᵗᵖ y))
  [ i ≔ s ]ⁿᶠ neⁿᶠ (mspⁿᵉ j xs y) = neⁿᶠ (mspⁿᵉ j ([ i ≔ s ]ˢᵖ xs) ([ i ≔ s ]ᵗᵖ y))
  [ i ≔ s ]ⁿᶠ lamⁿᶠ t             = lamⁿᶠ ([ pop i ≔ mono⊢ⁿᶠ weak⊆ s ]ⁿᶠ t)
  [ i ≔ s ]ⁿᶠ boxⁿᶠ t             = boxⁿᶠ t
  [ i ≔ s ]ⁿᶠ pairⁿᶠ t u          = pairⁿᶠ ([ i ≔ s ]ⁿᶠ t) ([ i ≔ s ]ⁿᶠ u)
  [ i ≔ s ]ⁿᶠ unitⁿᶠ              = unitⁿᶠ

  [_≔_]ˢᵖ_ : ∀ {A B C Γ Δ} → (i : A ∈ Γ) → Γ ∖ i ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ˢᵖ B ⦙ C → Γ ∖ i ⁏ Δ ⊢ˢᵖ B ⦙ C
  [ i ≔ s ]ˢᵖ nilˢᵖ      = nilˢᵖ
  [ i ≔ s ]ˢᵖ appˢᵖ xs u = appˢᵖ ([ i ≔ s ]ˢᵖ xs) ([ i ≔ s ]ⁿᶠ u)
  [ i ≔ s ]ˢᵖ fstˢᵖ xs   = fstˢᵖ ([ i ≔ s ]ˢᵖ xs)
  [ i ≔ s ]ˢᵖ sndˢᵖ xs   = sndˢᵖ ([ i ≔ s ]ˢᵖ xs)

  [_≔_]ᵗᵖ_ : ∀ {A B C Γ Δ} → (i : A ∈ Γ) → Γ ∖ i ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ᵗᵖ B ⦙ C → Γ ∖ i ⁏ Δ ⊢ᵗᵖ B ⦙ C
  [ i ≔ s ]ᵗᵖ nilᵗᵖ     = nilᵗᵖ
  [ i ≔ s ]ᵗᵖ unboxᵗᵖ u = unboxᵗᵖ u′
    where u′ = [ i ≔ mmono⊢ⁿᶠ weak⊆ s ]ⁿᶠ u

  m[_≔_]ⁿᶠ_ : ∀ {A B Γ Δ} → (i : A ∈ Δ) → ∅ ⁏ Δ ∖ i ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ⁿᶠ B → Γ ⁏ Δ ∖ i ⊢ⁿᶠ B
  m[ i ≔ s ]ⁿᶠ neⁿᶠ (spⁿᵉ j xs y)   = neⁿᶠ (spⁿᵉ j (m[ i ≔ s ]ˢᵖ xs) (m[ i ≔ s ]ᵗᵖ y))
  m[ i ≔ s ]ⁿᶠ neⁿᶠ (mspⁿᵉ j xs y)  with i ≟∈ j
  m[ i ≔ s ]ⁿᶠ neⁿᶠ (mspⁿᵉ .i xs y) | same   = reduce (mono⊢ⁿᶠ bot⊆ s) (m[ i ≔ s ]ˢᵖ xs) (m[ i ≔ s ]ᵗᵖ y)
  m[ i ≔ s ]ⁿᶠ neⁿᶠ (mspⁿᵉ ._ xs y) | diff j = neⁿᶠ (mspⁿᵉ j (m[ i ≔ s ]ˢᵖ xs) (m[ i ≔ s ]ᵗᵖ y))
  m[ i ≔ s ]ⁿᶠ lamⁿᶠ t              = lamⁿᶠ (m[ i ≔ s ]ⁿᶠ t)
  m[ i ≔ s ]ⁿᶠ boxⁿᶠ t              = boxⁿᶠ (m[ i ≔ nf→tm s ] t)
  m[ i ≔ s ]ⁿᶠ pairⁿᶠ t u           = pairⁿᶠ (m[ i ≔ s ]ⁿᶠ t) (m[ i ≔ s ]ⁿᶠ u)
  m[ i ≔ s ]ⁿᶠ unitⁿᶠ               = unitⁿᶠ

  m[_≔_]ˢᵖ_ : ∀ {A B C Γ Δ} → (i : A ∈ Δ) → ∅ ⁏ Δ ∖ i ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ˢᵖ B ⦙ C → Γ ⁏ Δ ∖ i ⊢ˢᵖ B ⦙ C
  m[ i ≔ s ]ˢᵖ nilˢᵖ      = nilˢᵖ
  m[ i ≔ s ]ˢᵖ appˢᵖ xs u = appˢᵖ (m[ i ≔ s ]ˢᵖ xs) (m[ i ≔ s ]ⁿᶠ u)
  m[ i ≔ s ]ˢᵖ fstˢᵖ xs   = fstˢᵖ (m[ i ≔ s ]ˢᵖ xs)
  m[ i ≔ s ]ˢᵖ sndˢᵖ xs   = sndˢᵖ (m[ i ≔ s ]ˢᵖ xs)

  m[_≔_]ᵗᵖ_ : ∀ {A B C Γ Δ} → (i : A ∈ Δ) → ∅ ⁏ Δ ∖ i ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ᵗᵖ B ⦙ C → Γ ⁏ Δ ∖ i ⊢ᵗᵖ B ⦙ C
  m[ i ≔ s ]ᵗᵖ nilᵗᵖ     = nilᵗᵖ
  m[ i ≔ s ]ᵗᵖ unboxᵗᵖ u = unboxᵗᵖ u′
    where u′ = m[ pop i ≔ mmono⊢ⁿᶠ weak⊆ s ]ⁿᶠ u

  reduce : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ˢᵖ A ⦙ B → Γ ⁏ Δ ⊢ᵗᵖ B ⦙ C → {{_ : Tyⁿᵉ C}} → Γ ⁏ Δ ⊢ⁿᶠ C
  reduce t                               nilˢᵖ        nilᵗᵖ       = t
  reduce (neⁿᶠ (spⁿᵉ i xs nilᵗᵖ))        nilˢᵖ        y           = neⁿᶠ (spⁿᵉ i xs y)
  reduce (neⁿᶠ (spⁿᵉ i xs (unboxᵗᵖ u)))  nilˢᵖ        y           = neⁿᶠ (spⁿᵉ i xs (unboxᵗᵖ u′))
    where u′ = reduce u nilˢᵖ (mmono⊢ᵗᵖ weak⊆ y)
  reduce (neⁿᶠ (mspⁿᵉ i xs nilᵗᵖ))       nilˢᵖ        y           = neⁿᶠ (mspⁿᵉ i xs y)
  reduce (neⁿᶠ (mspⁿᵉ i xs (unboxᵗᵖ u))) nilˢᵖ        y           = neⁿᶠ (mspⁿᵉ i xs (unboxᵗᵖ u′))
    where u′ = reduce u nilˢᵖ (mmono⊢ᵗᵖ weak⊆ y)
  reduce (neⁿᶠ t {{()}})                 (appˢᵖ xs u) y
  reduce (neⁿᶠ t {{()}})                 (fstˢᵖ xs)   y
  reduce (neⁿᶠ t {{()}})                 (sndˢᵖ xs)   y
  reduce (lamⁿᶠ t)                       (appˢᵖ xs u) y           = reduce ([ top ≔ u ]ⁿᶠ t) xs y
  reduce (boxⁿᶠ t)                       nilˢᵖ        (unboxᵗᵖ u) = m[ top ≔ {!t!} ]ⁿᶠ u
  reduce (pairⁿᶠ t u)                    (fstˢᵖ xs)   y           = reduce t xs y
  reduce (pairⁿᶠ t u)                    (sndˢᵖ xs)   y           = reduce u xs y


-- Reduction-based normal forms.

appⁿᶠ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ⁿᶠ A ▻ B → Γ ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ⁿᶠ B
appⁿᶠ (neⁿᶠ t {{()}})
appⁿᶠ (lamⁿᶠ t) u = [ top ≔ u ]ⁿᶠ t

fstⁿᶠ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ⁿᶠ A ∧ B → Γ ⁏ Δ ⊢ⁿᶠ A
fstⁿᶠ (neⁿᶠ t {{()}})
fstⁿᶠ (pairⁿᶠ t u) = t

sndⁿᶠ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ⁿᶠ A ∧ B → Γ ⁏ Δ ⊢ⁿᶠ B
sndⁿᶠ (neⁿᶠ t {{()}})
sndⁿᶠ (pairⁿᶠ t u) = u


-- Useful equipment for deriving neutrals.

≪appˢᵖ : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊢ˢᵖ C ⦙ A ▻ B → Γ ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ˢᵖ C ⦙ B
≪appˢᵖ nilˢᵖ        t = appˢᵖ nilˢᵖ t
≪appˢᵖ (appˢᵖ xs u) t = appˢᵖ (≪appˢᵖ xs t) u
≪appˢᵖ (fstˢᵖ xs)   t = fstˢᵖ (≪appˢᵖ xs t)
≪appˢᵖ (sndˢᵖ xs)   t = sndˢᵖ (≪appˢᵖ xs t)

≪fstˢᵖ : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊢ˢᵖ C ⦙ A ∧ B → Γ ⁏ Δ ⊢ˢᵖ C ⦙ A
≪fstˢᵖ nilˢᵖ        = fstˢᵖ nilˢᵖ
≪fstˢᵖ (appˢᵖ xs u) = appˢᵖ (≪fstˢᵖ xs) u
≪fstˢᵖ (fstˢᵖ xs)   = fstˢᵖ (≪fstˢᵖ xs)
≪fstˢᵖ (sndˢᵖ xs)   = sndˢᵖ (≪fstˢᵖ xs)

≪sndˢᵖ : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊢ˢᵖ C ⦙ A ∧ B → Γ ⁏ Δ ⊢ˢᵖ C ⦙ B
≪sndˢᵖ nilˢᵖ        = sndˢᵖ nilˢᵖ
≪sndˢᵖ (appˢᵖ xs u) = appˢᵖ (≪sndˢᵖ xs) u
≪sndˢᵖ (fstˢᵖ xs)   = fstˢᵖ (≪sndˢᵖ xs)
≪sndˢᵖ (sndˢᵖ xs)   = sndˢᵖ (≪sndˢᵖ xs)


-- Derived neutrals.

varⁿᵉ : ∀ {A Γ Δ} → A ∈ Γ → Γ ⁏ Δ ⊢ⁿᵉ A
varⁿᵉ i = spⁿᵉ i nilˢᵖ nilᵗᵖ

appⁿᵉ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ⁿᵉ A ▻ B → Γ ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ⁿᵉ B
appⁿᵉ (spⁿᵉ i xs nilᵗᵖ)        t = spⁿᵉ i (≪appˢᵖ xs t) nilᵗᵖ
appⁿᵉ (spⁿᵉ i xs (unboxᵗᵖ u))  t = spⁿᵉ i xs (unboxᵗᵖ u′)
  where u′ = appⁿᶠ u (mmono⊢ⁿᶠ weak⊆ t)
appⁿᵉ (mspⁿᵉ i xs nilᵗᵖ)       t = mspⁿᵉ i (≪appˢᵖ xs t) nilᵗᵖ
appⁿᵉ (mspⁿᵉ i xs (unboxᵗᵖ u)) t = mspⁿᵉ i xs (unboxᵗᵖ u′)
  where u′ = appⁿᶠ u (mmono⊢ⁿᶠ weak⊆ t)

mvarⁿᵉ : ∀ {A Γ Δ} → A ∈ Δ → Γ ⁏ Δ ⊢ⁿᵉ A
mvarⁿᵉ i = mspⁿᵉ i nilˢᵖ nilᵗᵖ

fstⁿᵉ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ⁿᵉ A ∧ B → Γ ⁏ Δ ⊢ⁿᵉ A
fstⁿᵉ (spⁿᵉ i xs nilᵗᵖ)        = spⁿᵉ i (≪fstˢᵖ xs) nilᵗᵖ
fstⁿᵉ (spⁿᵉ i xs (unboxᵗᵖ u))  = spⁿᵉ i xs (unboxᵗᵖ (fstⁿᶠ u))
fstⁿᵉ (mspⁿᵉ i xs nilᵗᵖ)       = mspⁿᵉ i (≪fstˢᵖ xs) nilᵗᵖ
fstⁿᵉ (mspⁿᵉ i xs (unboxᵗᵖ u)) = mspⁿᵉ i xs (unboxᵗᵖ (fstⁿᶠ u))

sndⁿᵉ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ⁿᵉ A ∧ B → Γ ⁏ Δ ⊢ⁿᵉ B
sndⁿᵉ (spⁿᵉ i xs nilᵗᵖ)        = spⁿᵉ i (≪sndˢᵖ xs) nilᵗᵖ
sndⁿᵉ (spⁿᵉ i xs (unboxᵗᵖ u))  = spⁿᵉ i xs (unboxᵗᵖ (sndⁿᶠ u))
sndⁿᵉ (mspⁿᵉ i xs nilᵗᵖ)       = mspⁿᵉ i (≪sndˢᵖ xs) nilᵗᵖ
sndⁿᵉ (mspⁿᵉ i xs (unboxᵗᵖ u)) = mspⁿᵉ i xs (unboxᵗᵖ (sndⁿᶠ u))


-- Iterated expansion.

expand : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ⁿᵉ A → Γ ⁏ Δ ⊢ⁿᶠ A
expand {α P}   t = neⁿᶠ t {{α P}}
expand {A ▻ B} t = lamⁿᶠ (expand (appⁿᵉ (mono⊢ⁿᵉ weak⊆ t) (expand (varⁿᵉ top))))
expand {□ A}   t = neⁿᶠ t {{□ A}}
expand {A ∧ B} t = pairⁿᶠ (expand (fstⁿᵉ t)) (expand (sndⁿᵉ t))
expand {⊤}    t = unitⁿᶠ


-- Expansion-based normal forms.

varⁿᶠ : ∀ {A Γ Δ} → A ∈ Γ → Γ ⁏ Δ ⊢ⁿᶠ A
varⁿᶠ i = expand (varⁿᵉ i)

mvarⁿᶠ : ∀ {A Γ Δ} → A ∈ Δ → Γ ⁏ Δ ⊢ⁿᶠ A
mvarⁿᶠ i = expand (mvarⁿᵉ i)

mutual
  unboxⁿᶠ : ∀ {A C Γ Δ} → Γ ⁏ Δ ⊢ⁿᶠ □ A → Γ ⁏ Δ , A ⊢ⁿᶠ C → Γ ⁏ Δ ⊢ⁿᶠ C
  unboxⁿᶠ (neⁿᶠ t)  u = expand (unboxⁿᵉ t u)
  unboxⁿᶠ (boxⁿᶠ t) u = m[ top ≔ {!t!} ]ⁿᶠ u

  unboxⁿᵉ : ∀ {A C Γ Δ} → Γ ⁏ Δ ⊢ⁿᵉ □ A → Γ ⁏ Δ , A ⊢ⁿᶠ C → Γ ⁏ Δ ⊢ⁿᵉ C
  unboxⁿᵉ (spⁿᵉ i xs nilᵗᵖ)        u = spⁿᵉ i xs (unboxᵗᵖ u)
  unboxⁿᵉ (spⁿᵉ i xs (unboxᵗᵖ t))  u = spⁿᵉ i xs (unboxᵗᵖ u′)
    where u′ = unboxⁿᶠ t (mmono⊢ⁿᶠ (keep (weak⊆)) u)
  unboxⁿᵉ (mspⁿᵉ i xs nilᵗᵖ)       u = mspⁿᵉ i xs (unboxᵗᵖ u)
  unboxⁿᵉ (mspⁿᵉ i xs (unboxᵗᵖ t)) u = mspⁿᵉ i xs (unboxᵗᵖ u′)
    where u′ = unboxⁿᶠ t (mmono⊢ⁿᶠ (keep (weak⊆)) u)


-- Translation from terms to normal forms.

tm→nf : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ⁿᶠ A
tm→nf (var i)     = varⁿᶠ i
tm→nf (lam t)     = lamⁿᶠ (tm→nf t)
tm→nf (app t u)   = appⁿᶠ (tm→nf t) (tm→nf u)
tm→nf (mvar i)    = mvarⁿᶠ i
tm→nf (box t)     = boxⁿᶠ t
tm→nf (unbox t u) = unboxⁿᶠ (tm→nf t) (tm→nf u)
tm→nf (pair t u)  = pairⁿᶠ (tm→nf t) (tm→nf u)
tm→nf (fst t)     = fstⁿᶠ (tm→nf t)
tm→nf (snd t)     = sndⁿᶠ (tm→nf t)
tm→nf unit        = unitⁿᶠ


-- Normalisation by hereditary substitution.

norm : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ A
norm = nf→tm ∘ tm→nf
