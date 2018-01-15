module StdS4 where

open import Prelude
open import List
open List²
open import AllList


--------------------------------------------------------------------------------


infixr 8 _⊃_
data Prop : Set
  where
    BASE : Prop
    _⊃_  : Prop → Prop → Prop
    □_   : Prop → Prop


infix 7 _true
record Truth : Set
  where
    constructor _true
    field
      A : Prop


infix 7 _valid
record Validity : Set
  where
    constructor _valid
    field
      A : Prop


--------------------------------------------------------------------------------


infix 3 _⊢_
data _⊢_ : List² Validity Truth → Truth → Set
  where
    var : ∀ {A Δ Γ} → Γ ∋ A true
                    → Δ ⨾ Γ ⊢ A true

    lam : ∀ {A B Δ Γ} → Δ ⨾ Γ , A true ⊢ B true
                      → Δ ⨾ Γ ⊢ A ⊃ B true

    app : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A ⊃ B true → Δ ⨾ Γ ⊢ A true
                      → Δ ⨾ Γ ⊢ B true

    mvar : ∀ {A Δ Γ} → Δ ∋ A valid
                     → Δ ⨾ Γ ⊢ A true

    box : ∀ {A Δ Γ} → Δ ⨾ ∙ ⊢ A true
                    → Δ ⨾ Γ ⊢ □ A true

    letbox : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ □ A true → Δ , A valid ⨾ Γ ⊢ B true
                         → Δ ⨾ Γ ⊢ B true


--------------------------------------------------------------------------------


ren : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⨾ Γ ⊢ A true
                   → Δ ⨾ Γ′ ⊢ A true
ren η (var 𝒾)      = var (ren∋ η 𝒾)
ren η (lam 𝒟)      = lam (ren (keep η) 𝒟)
ren η (app 𝒟 ℰ)    = app (ren η 𝒟) (ren η ℰ)
ren η (mvar 𝒾)     = mvar 𝒾
ren η (box 𝒟)      = box 𝒟
ren η (letbox 𝒟 ℰ) = letbox (ren η 𝒟) (ren η ℰ)


wk : ∀ {B A Δ Γ} → Δ ⨾ Γ ⊢ A true
                 → Δ ⨾ Γ , B true ⊢ A true
wk 𝒟 = ren (drop id⊇) 𝒟


vz : ∀ {A Δ Γ} → Δ ⨾ Γ , A true ⊢ A true
vz = var zero


--------------------------------------------------------------------------------


mren : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⨾ Γ ⊢ A true
                    → Δ′ ⨾ Γ ⊢ A true
mren η (var 𝒾)      = var 𝒾
mren η (lam 𝒟)      = lam (mren η 𝒟)
mren η (app 𝒟 ℰ)    = app (mren η 𝒟) (mren η ℰ)
mren η (mvar 𝒾)     = mvar (ren∋ η 𝒾)
mren η (box 𝒟)      = box (mren η 𝒟)
mren η (letbox 𝒟 ℰ) = letbox (mren η 𝒟) (mren (keep η) ℰ)


mwk : ∀ {B A Δ Γ} → Δ ⨾ Γ ⊢ A true
                  → Δ , B valid ⨾ Γ ⊢ A true
mwk 𝒟 = mren (drop id⊇) 𝒟


mvz : ∀ {A Δ Γ} → Δ , A valid ⨾ Γ ⊢ A true
mvz = mvar zero


--------------------------------------------------------------------------------


infix 3 _⊢⋆_
_⊢⋆_ : List² Validity Truth → List Truth → Set
Δ ⨾ Γ ⊢⋆ Ξ = All (Δ ⨾ Γ ⊢_) Ξ


--------------------------------------------------------------------------------


rens : ∀ {Δ Γ Γ′ Ξ} → Γ′ ⊇ Γ → Δ ⨾ Γ ⊢⋆ Ξ
                    → Δ ⨾ Γ′ ⊢⋆ Ξ
rens η ξ = maps (ren η) ξ


wks : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢⋆ Ξ
                  → Δ ⨾ Γ , A true ⊢⋆ Ξ
wks ξ = rens (drop id⊇) ξ


lifts : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢⋆ Ξ
                    → Δ ⨾ Γ , A true ⊢⋆ Ξ , A true
lifts ξ = wks ξ , vz


vars : ∀ {Δ Γ Γ′} → Γ′ ⊇ Γ
                  → Δ ⨾ Γ′ ⊢⋆ Γ
vars done     = ∙
vars (drop η) = wks (vars η)
vars (keep η) = lifts (vars η)


ids : ∀ {Δ Γ} → Δ ⨾ Γ ⊢⋆ Γ
ids = vars id⊇


--------------------------------------------------------------------------------


mrens : ∀ {Δ Δ′ Γ Ξ} → Δ′ ⊇ Δ → Δ ⨾ Γ ⊢⋆ Ξ
                     → Δ′ ⨾ Γ ⊢⋆ Ξ
mrens η ξ = maps (mren η) ξ


mwks : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢⋆ Ξ
                   → Δ , A valid ⨾ Γ ⊢⋆ Ξ
mwks ξ = mrens (drop id⊇) ξ


--------------------------------------------------------------------------------


sub : ∀ {Δ Γ Ξ A} → Δ ⨾ Γ ⊢⋆ Ξ → Δ ⨾ Ξ ⊢ A true
                  → Δ ⨾ Γ ⊢ A true
sub ξ (var 𝒾)      = get ξ 𝒾
sub ξ (lam 𝒟)      = lam (sub (lifts ξ) 𝒟)
sub ξ (app 𝒟 ℰ)    = app (sub ξ 𝒟) (sub ξ ℰ)
sub ξ (mvar 𝒾)     = mvar 𝒾
sub ξ (box 𝒟)      = box 𝒟
sub ξ (letbox 𝒟 ℰ) = letbox (sub ξ 𝒟) (sub (mwks ξ) ℰ)


cut : ∀ {Δ Γ A B} → Δ ⨾ Γ ⊢ A true → Δ ⨾ Γ , A true ⊢ B true
                  → Δ ⨾ Γ ⊢ B true
cut 𝒟 ℰ = sub (ids , 𝒟) ℰ


--------------------------------------------------------------------------------


subs : ∀ {Δ Γ Ξ Ψ} → Δ ⨾ Γ ⊢⋆ Ξ → Δ ⨾ Ξ ⊢⋆ Ψ
                   → Δ ⨾ Γ ⊢⋆ Ψ
subs ξ ψ = maps (sub ξ) ψ


--------------------------------------------------------------------------------


infix 3 _⊢₁_
_⊢₁_ : List Validity → Validity → Set
Δ ⊢₁ A valid = Δ ⨾ ∙ ⊢ A true


infix 3 _⊢⋆₁_
_⊢⋆₁_ : List Validity → List Validity → Set
Δ ⊢⋆₁ Ξ = All (Δ ⊢₁_) Ξ


--------------------------------------------------------------------------------


mrens₁ : ∀ {Δ Δ′ Ξ} → Δ′ ⊇ Δ → Δ ⊢⋆₁ Ξ
                    → Δ′ ⊢⋆₁ Ξ
mrens₁ η ξ = maps (mren η) ξ


mwks₁ : ∀ {A Δ Ξ} → Δ ⊢⋆₁ Ξ
                  → Δ , A valid ⊢⋆₁ Ξ
mwks₁ ξ = mrens₁ (drop id⊇) ξ


mlifts₁ : ∀ {A Δ Ξ} → Δ ⊢⋆₁ Ξ
                    → Δ , A valid ⊢⋆₁ Ξ , A valid
mlifts₁ ξ = mwks₁ ξ , mvz


mvars₁ : ∀ {Δ Δ′} → Δ′ ⊇ Δ
                  → Δ′ ⊢⋆₁ Δ
mvars₁ done     = ∙
mvars₁ (drop η) = mwks₁ (mvars₁ η)
mvars₁ (keep η) = mlifts₁ (mvars₁ η)


mids₁ : ∀ {Δ} → Δ ⊢⋆₁ Δ
mids₁ = mvars₁ id⊇


--------------------------------------------------------------------------------


msub : ∀ {Δ Γ Ξ A} → Δ ⊢⋆₁ Ξ → Ξ ⨾ Γ ⊢ A true
                   → Δ ⨾ Γ ⊢ A true
msub ξ (var 𝒾)      = var 𝒾
msub ξ (lam 𝒟)      = lam (msub ξ 𝒟)
msub ξ (app 𝒟 ℰ)    = app (msub ξ 𝒟) (msub ξ ℰ)
msub ξ (mvar 𝒾)     = sub ∙ (get ξ 𝒾)
msub ξ (box 𝒟)      = box (msub ξ 𝒟)
msub ξ (letbox 𝒟 ℰ) = letbox (msub ξ 𝒟) (msub (mlifts₁ ξ) ℰ)


mcut : ∀ {Δ Γ A B} → Δ ⊢₁ A valid → Δ , A valid ⨾ Γ ⊢ B true
                   → Δ ⨾ Γ ⊢ B true
mcut 𝒟 ℰ = msub (mids₁ , 𝒟) ℰ


--------------------------------------------------------------------------------


msubs : ∀ {Δ Γ Ξ Ψ} → Δ ⊢⋆₁ Ξ → Ξ ⨾ Γ ⊢⋆ Ψ
                    → Δ ⨾ Γ ⊢⋆ Ψ
msubs ξ ψ = maps (msub ξ) ψ


msubs₁ : ∀ {Δ Ξ Ψ} → Δ ⊢⋆₁ Ξ → Ξ ⊢⋆₁ Ψ
                   → Δ ⊢⋆₁ Ψ
msubs₁ ξ ψ = maps (msub ξ) ψ


--------------------------------------------------------------------------------


unlam : ∀ {Δ Γ A B} → Δ ⨾ Γ ⊢ A ⊃ B true
                    → Δ ⨾ Γ , A true ⊢ B true
unlam 𝒟 = app (wk 𝒟) vz


ex : ∀ {Δ Γ A B C} → Δ ⨾ Γ , A true , B true ⊢ C true
                   → Δ ⨾ Γ , B true , A true ⊢ C true
ex 𝒟 = app (app (wk (wk (lam (lam 𝒟)))) vz) (wk vz)


--------------------------------------------------------------------------------


up : ∀ {Δ Γ A B} → Δ ⨾ Γ , □ A true ⊢ B true
                 → Δ , A valid ⨾ Γ ⊢ B true
up 𝒟 = app (lam (mwk 𝒟)) (box mvz)


down : ∀ {Δ Γ A B} → Δ , A valid ⨾ Γ ⊢ B true
                   → Δ ⨾ Γ , □ A true ⊢ B true
down 𝒟 = letbox vz (wk 𝒟)


mex : ∀ {Δ Γ A B C} → Δ , A valid , B valid ⨾ Γ ⊢ C true
                    → Δ , B valid , A valid ⨾ Γ ⊢ C true
mex 𝒟 = up (up (ex (down (down 𝒟))))


--------------------------------------------------------------------------------


-- import StdIPL as IPL
-- open IPL using (BASE ; _⊃_ ; _true ; var ; lam ; app)


-- ⌈_⌉ₚ : IPL.Prop → Prop
-- ⌈ BASE ⌉ₚ  = BASE
-- ⌈ A ⊃ B ⌉ₚ = ⌈ A ⌉ₚ ⊃ ⌈ B ⌉ₚ

-- ⌈_⌉ₕ : List IPL.Truth → List Truth
-- ⌈ ∙ ⌉ₕ          = ∙
-- ⌈ Γ , A true ⌉ₕ = ⌈ Γ ⌉ₕ , ⌈ A ⌉ₚ true

-- ⌈_⌉ᵢ : ∀ {Γ A} → Γ ∋ A true
--                → ⌈ Γ ⌉ₕ ∋ ⌈ A ⌉ₚ true
-- ⌈ zero ⌉ᵢ  = zero
-- ⌈ suc 𝒾 ⌉ᵢ = suc ⌈ 𝒾 ⌉ᵢ

-- ⌈_⌉ : ∀ {Δ Γ A} → Γ IPL.⊢ A true
--               → Δ ⨾ ⌈ Γ ⌉ₕ ⊢ ⌈ A ⌉ₚ true
-- ⌈ var 𝒾 ⌉   = var ⌈ 𝒾 ⌉ᵢ
-- ⌈ lam 𝒟 ⌉   = lam ⌈ 𝒟 ⌉
-- ⌈ app 𝒟 ℰ ⌉ = app ⌈ 𝒟 ⌉ ⌈ ℰ ⌉


-- ⌊_⌋ₚ : Prop → IPL.Prop
-- ⌊ BASE ⌋ₚ  = BASE
-- ⌊ A ⊃ B ⌋ₚ = ⌊ A ⌋ₚ ⊃ ⌊ B ⌋ₚ
-- ⌊ □ A ⌋ₚ   = ⌊ A ⌋ₚ

-- ⌊_⌋ₕ : List Truth → List IPL.Truth
-- ⌊ ∙ ⌋ₕ          = ∙
-- ⌊ Γ , A true ⌋ₕ = ⌊ Γ ⌋ₕ , ⌊ A ⌋ₚ true

-- ⌊_⨾_⌋ₕ₂ : List Validity → List Truth → List IPL.Truth
-- ⌊ ∙ ⨾ Γ ⌋ₕ₂ = ⌊ Γ ⌋ₕ
-- ⌊ Δ , A valid ⨾ Γ ⌋ₕ₂ = ⌊ Δ ⨾ Γ ⌋ₕ₂ , ⌊ A ⌋ₚ true

-- ⌊_⌋ᵢ : ∀ {Γ A} → Γ ∋ A true
--                → ⌊ Γ ⌋ₕ ∋ ⌊ A ⌋ₚ true
-- ⌊ zero ⌋ᵢ  = zero
-- ⌊ suc 𝒾 ⌋ᵢ = suc ⌊ 𝒾 ⌋ᵢ


-- ⌊_⌋ : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ A true
--                 → ⌊ Δ ⨾ Γ ⌋ₕ₂ IPL.⊢ ⌊ A ⌋ₚ true
-- ⌊ var 𝒾 ⌋      = {!var ⌊ 𝒾 ⌋ᵢ!}
-- ⌊ lam 𝒟 ⌋      = {!lam ⌊ 𝒟 ⌋!}
-- ⌊ app 𝒟 ℰ ⌋    = app ⌊ 𝒟 ⌋ ⌊ ℰ ⌋
-- ⌊ mvar 𝒾 ⌋     = {!!}
-- ⌊ box 𝒟 ⌋      = {!⌊ 𝒟 ⌋!}
-- ⌊ letbox 𝒟 ℰ ⌋ = {!!}

-- -- {-# TERMINATING #-}
-- -- ⌊_⌋ : ∀ {Γ A} → ∙ ⨾ Γ ⊢ A true
-- --               → ⌊ Γ ⌋ₕ IPL.⊢ ⌊ A ⌋ₚ true
-- -- ⌊ var 𝒾 ⌋      = var ⌊ 𝒾 ⌋ᵢ
-- -- ⌊ lam 𝒟 ⌋      = lam ⌊ 𝒟 ⌋
-- -- ⌊ app 𝒟 ℰ ⌋    = app ⌊ 𝒟 ⌋ ⌊ ℰ ⌋
-- -- ⌊ mvar () ⌋
-- -- ⌊ box 𝒟 ⌋      = IPL.sub ∙ ⌊ 𝒟 ⌋
-- -- ⌊ letbox 𝒟 ℰ ⌋ = IPL.cut ⌊ 𝒟 ⌋ ⌊ down ℰ ⌋ -- ⌊ cut 𝒟 (down ℰ) ⌋ -- woah!
