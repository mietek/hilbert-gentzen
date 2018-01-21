module S4ExperimentalDerivations3x where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import S4Propositions
import S4Derivations as S4


--------------------------------------------------------------------------------


mutual
  infix 3 _⨾_⊢_true
  data _⨾_⊢_true : List Prop → List Prop → Prop → Set
    where
      vz : ∀ {A Δ Γ} → Δ ⨾ Γ , A ⊢ A true

      wk : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A true
                       → Δ ⨾ Γ , B ⊢ A true

      cut : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A true → Δ ⨾ Γ , A ⊢ B true
                        → Δ ⨾ Γ ⊢ B true

      lam : ∀ {A B Δ Γ} → Δ ⨾ Γ , A ⊢ B true
                        → Δ ⨾ Γ ⊢ A ⊃ B true

      unlam : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A ⊃ B true
                          → Δ ⨾ Γ , A ⊢ B true

      vau : ∀ {A B Δ Γ} → Δ , A ⨾ Γ ⊢ B true
                        → Δ ⨾ Γ , □ A ⊢ B true

      unvau : ∀ {A B Δ Γ} → Δ ⨾ Γ , □ A ⊢ B true
                          → Δ , A ⨾ Γ ⊢ B true

      v→t : ∀ {A Δ Γ} → Δ ⊢ A valid
                       → Δ ⨾ Γ ⊢ A true

  infix 3 _⊢_valid
  data _⊢_valid : List Prop → Prop → Set
    where
      mvz : ∀ {A Δ} → Δ , A ⊢ A valid

      mwk : ∀ {A B Δ} → Δ ⊢ A valid
                      → Δ , B ⊢ A valid

      mcut : ∀ {A B Δ} → Δ ⊢ A valid → Δ , A ⊢ B valid
                       → Δ ⊢ B valid

      t→v : ∀ {A Δ} → Δ ⨾ ∙ ⊢ A true
                     → Δ ⊢ A valid


infix 3 _⨾_⊢_true*
_⨾_⊢_true* : List Prop → List Prop → List Prop → Set
Δ ⨾ Γ ⊢ Ξ true* = All (Δ ⨾ Γ ⊢_true) Ξ


infix 3 _⊢_valid*
_⊢_valid* : List Prop → List Prop → Set
Δ ⊢ Ξ valid* = All (Δ ⊢_valid) Ξ


--------------------------------------------------------------------------------


wks : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢ Ξ true*
                  → Δ ⨾ Γ , A ⊢ Ξ true*
wks ξ = maps wk ξ


lifts : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢ Ξ true*
                    → Δ ⨾ Γ , A ⊢ Ξ , A true*
lifts ξ = wks ξ , vz


vars : ∀ {Δ Γ Γ′} → Γ′ ⊇ Γ
                  → Δ ⨾ Γ′ ⊢ Γ true*
vars done     = ∙
vars (drop η) = wks (vars η)
vars (keep η) = lifts (vars η)


ids : ∀ {Δ Γ} → Δ ⨾ Γ ⊢ Γ true*
ids = vars id


--------------------------------------------------------------------------------


mwks : ∀ {A Δ Ξ} → Δ ⊢ Ξ valid*
                 → Δ , A ⊢ Ξ valid*
mwks ξ = maps mwk ξ


mlifts : ∀ {A Δ Ξ} → Δ ⊢ Ξ valid*
                   → Δ , A ⊢ Ξ , A valid*
mlifts ξ = mwks ξ , mvz


mvars : ∀ {Δ Δ′} → Δ′ ⊇ Δ
                 → Δ′ ⊢ Δ valid*
mvars done     = ∙
mvars (drop η) = mwks (mvars η)
mvars (keep η) = mlifts (mvars η)


mids : ∀ {Δ} → Δ ⊢ Δ valid*
mids = mvars id


--------------------------------------------------------------------------------


mwk′ : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A true
                   → Δ , B ⨾ Γ ⊢ A true
mwk′ 𝒟 = unvau (wk 𝒟)


mwks′ : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢ Ξ true*
                    → Δ , A ⨾ Γ ⊢ Ξ true*
mwks′ ξ = maps mwk′ ξ


vaus : ∀ {Δ Γ A Ξ} → Δ , A ⨾ Γ ⊢ Ξ true*
                   → Δ ⨾ Γ , □ A ⊢ Ξ true*
vaus 𝒟 = maps vau 𝒟


-- NOTE: Similar shape to lift or cut

unnamed : ∀ {Δ Γ A Ξ} → Δ , A ⨾ Γ ⊢ Ξ true*
                      → Δ ⨾ Γ , □ A ⊢ Ξ , □ A true*
unnamed 𝒟 = vaus 𝒟 , vz


sub : ∀ {Δ Γ Ξ A} → Δ ⨾ Γ ⊢ Ξ true* → Δ ⨾ Ξ ⊢ A true
                  → Δ ⨾ Γ ⊢ A true
sub (ξ , 𝒞) vz        = 𝒞
sub (ξ , 𝒞) (wk 𝒟)    = sub ξ 𝒟
sub ξ       (cut 𝒟 ℰ) = cut (sub ξ 𝒟) (sub (lifts ξ) ℰ)
sub ξ       (lam 𝒟)   = lam (sub (lifts ξ) 𝒟)
sub (ξ , 𝒞) (unlam 𝒟) = cut 𝒞 (unlam (sub ξ 𝒟))
sub (ξ , 𝒞) (vau 𝒟)   = cut 𝒞 (vau (sub (mwks′ ξ) 𝒟))
sub ξ       (unvau 𝒟) = unvau (sub (unnamed ξ) 𝒟)  -- NOTE: Interesting
sub ξ       (v→t 𝒟)  = v→t 𝒟


--------------------------------------------------------------------------------


box : ∀ {A Δ Γ} → Δ ⨾ ∙ ⊢ A true
                → Δ ⨾ Γ ⊢ □ A true
box 𝒟 = v→t (mcut (t→v 𝒟) (t→v (unvau vz)))


letbox : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ □ A true → Δ , A ⨾ Γ ⊢ B true
                     → Δ ⨾ Γ ⊢ B true
letbox 𝒟 ℰ = cut 𝒟 (vau ℰ)


mcut′ : ∀ {Δ Γ A B} → Δ ⨾ ∙ ⊢ A true → Δ , A ⨾ Γ ⊢ B true
                    → Δ ⨾ Γ ⊢ B true
mcut′ 𝒟 ℰ = cut (box 𝒟) (vau ℰ)


mutual
  msub : ∀ {Δ Γ Ξ A} → Δ ⊢ Ξ valid* → Ξ ⨾ Γ ⊢ A true
                     → Δ ⨾ Γ ⊢ A true
  msub ξ       vz        = vz
  msub ξ       (wk 𝒟)    = wk (msub ξ 𝒟)
  msub ξ       (cut 𝒟 ℰ) = cut (msub ξ 𝒟) (msub ξ ℰ)
  msub ξ       (lam 𝒟)   = lam (msub ξ 𝒟)
  msub ξ       (unlam 𝒟) = unlam (msub ξ 𝒟)
  msub ξ       (vau 𝒟)   = vau (msub (mlifts ξ) 𝒟)
  msub (ξ , 𝒞) (unvau 𝒟) = mcut′ (v→t 𝒞) (unvau (msub ξ 𝒟))  -- NOTE: Interesting
  msub ξ       (v→t 𝒟)  = v→t (msub₁ ξ 𝒟)

  msub₁ : ∀ {Δ Ξ A} → Δ ⊢ Ξ valid* → Ξ ⊢ A valid
                    → Δ ⊢ A valid
  msub₁ ξ       (t→v 𝒟)   = t→v (msub ξ 𝒟)
  msub₁ (ξ , 𝒞) mvz        = 𝒞
  msub₁ (ξ , 𝒞) (mwk 𝒟)    = msub₁ ξ 𝒟
  msub₁ ξ       (mcut 𝒟 ℰ) = mcut (msub₁ ξ 𝒟) (msub₁ (mlifts ξ) ℰ)


--------------------------------------------------------------------------------


var : ∀ {A Δ Γ} → Γ ∋ A
                → Δ ⨾ Γ ⊢ A true
var zero    = vz
var (suc i) = wk (var i)


app : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A ⊃ B true → Δ ⨾ Γ ⊢ A true
                  → Δ ⨾ Γ ⊢ B true
app 𝒟 ℰ = cut ℰ (unlam 𝒟)


--------------------------------------------------------------------------------


mvz′ : ∀ {A Δ Γ} → Δ , A ⨾ Γ ⊢ A true
mvz′ = v→t mvz


mvar : ∀ {A Δ Γ} → Δ ∋ A
                 → Δ ⨾ Γ ⊢ A true
mvar zero    = mvz′
mvar (suc i) = mwk′ (mvar i)


--------------------------------------------------------------------------------


mutual
  ↓ : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ A true
                → Δ S4.⨾ Γ ⊢ A true
  ↓ vz           = S4.vz
  ↓ (wk 𝒟)       = S4.wk (↓ 𝒟)
  ↓ (cut 𝒟 ℰ)    = S4.cut (↓ 𝒟) (↓ ℰ)
  ↓ (lam 𝒟)      = S4.lam (↓ 𝒟)
  ↓ (unlam 𝒟)    = S4.unlam (↓ 𝒟)
  ↓ (vau 𝒟)      = S4.vau (↓ 𝒟)
  ↓ (unvau 𝒟)    = S4.unvau (↓ 𝒟)
  ↓ (v→t 𝒟)     = S4.v→t (↓₁ 𝒟)

  ↓₁ : ∀ {Δ A} → Δ ⊢ A valid
               → Δ S4.⊢ A valid
  ↓₁ (t→v 𝒟)    = S4.t→v (↓ 𝒟)
  ↓₁ mvz        = S4.mvz
  ↓₁ (mwk 𝒟)    = S4.mwk (↓₁ 𝒟)
  ↓₁ (mcut 𝒟 ℰ) = S4.mcut (↓₁ 𝒟) (↓₁ ℰ)


↑ : ∀ {Δ Γ A} → Δ S4.⨾ Γ ⊢ A true
              → Δ ⨾ Γ ⊢ A true
↑ (S4.var i)      = var i
↑ (S4.lam 𝒟)      = lam (↑ 𝒟)
↑ (S4.app 𝒟 ℰ)    = app (↑ 𝒟) (↑ ℰ)
↑ (S4.mvar i)     = mvar i
↑ (S4.box 𝒟)      = box (↑ 𝒟)
↑ (S4.letbox 𝒟 ℰ) = letbox (↑ 𝒟) (↑ ℰ)


--------------------------------------------------------------------------------
