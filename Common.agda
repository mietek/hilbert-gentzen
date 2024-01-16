module Common where

open import Data.Empty public
  using ()
  renaming (⊥ to 𝟘 ; ⊥-elim to abort)

open import Data.List public
  using (List ; [] ; _∷_)

open import Data.Nat public
  using (ℕ ; zero ; suc)

open import Data.Product public
  using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)

open import Data.Sum public
  using (_⊎_ ; inj₁ ; inj₂)

open import Data.Unit public
  using ()
  renaming (⊤ to 𝟙 ; tt to unit)

open import Function public
  using (_∘_ ; _$_ ; flip ; id)

open import Relation.Binary.PropositionalEquality public
  using (_≡_ ; refl ; cong ; subst ; sym ; trans ; module ≡-Reasoning)

open import Relation.Nullary public
  using (¬_ ; Dec ; yes ; no)

open import Relation.Nullary.Decidable public
  using (True ; fromWitness ; toWitness)

open import Relation.Nullary.Negation public
  using ()
  renaming (contradiction to _↯_)


----------------------------------------------------------------------------------------------------

-- uniqueness of proofs for propositional equality
uni≡ : ∀ {𝓍} {X : Set 𝓍} {x x′ : X} (eq eq′ : x ≡ x′) → eq ≡ eq′
uni≡ refl refl = refl

coe : ∀ {𝓍} {X Y : Set 𝓍} → X ≡ Y → X → Y
coe = subst id

infixl 9 _&_
_&_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} (f : X → Y) {x x′ : X} → x ≡ x′ →
      f x ≡ f x′
_&_ = cong

infixl 8 _⊗_
_⊗_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} {f g : X → Y} {x y : X} → f ≡ g → x ≡ y →
      f x ≡ g y
refl ⊗ refl = refl

recℕ : ∀ {𝓍} {X : Set 𝓍} → ℕ → X → (ℕ → X → X) → X
recℕ zero    z s = z
recℕ (suc n) z s = s n (recℕ n z s)


----------------------------------------------------------------------------------------------------

module _ {𝓍} {X : Set 𝓍} where
  -- intrinsically well-typed de Bruijn indices
  infix 4 _∋_
  data _∋_ : List X → X → Set 𝓍 where
    zero : ∀ {Γ A} → A ∷ Γ ∋ A
    suc  : ∀ {Γ A B} (i : Γ ∋ A) → B ∷ Γ ∋ A

  -- order-preserving embeddings
  infix 4 _⊆_
  data _⊆_ : List X → List X → Set 𝓍 where
    stop : [] ⊆ []
    drop : ∀ {Γ Γ′ A} (e : Γ ⊆ Γ′) → Γ ⊆ A ∷ Γ′
    keep : ∀ {Γ Γ′ A} (e : Γ ⊆ Γ′) → A ∷ Γ ⊆ A ∷ Γ′

  refl⊆ : ∀ {Γ} → Γ ⊆ Γ
  refl⊆ {[]}    = stop
  refl⊆ {A ∷ Γ} = keep refl⊆

  trans⊆ : ∀ {Γ Γ′ Γ″} → Γ ⊆ Γ′ → Γ′ ⊆ Γ″ → Γ ⊆ Γ″
  trans⊆ e        stop      = e
  trans⊆ e        (drop e′) = drop (trans⊆ e e′)
  trans⊆ (drop e) (keep e′) = drop (trans⊆ e e′)
  trans⊆ (keep e) (keep e′) = keep (trans⊆ e e′)

  wk⊆ : ∀ {Γ A} → Γ ⊆ A ∷ Γ
  wk⊆ = drop refl⊆

  -- renaming of indices
  ren∋ : ∀ {Γ Γ′} {A : X} → Γ ⊆ Γ′ → Γ ∋ A → Γ′ ∋ A
  ren∋ stop     i       = i
  ren∋ (drop e) i       = suc (ren∋ e i)
  ren∋ (keep e) zero    = zero
  ren∋ (keep e) (suc i) = suc (ren∋ e i)

  infix 4 _≟∋_
  _≟∋_ : ∀ {Γ A} (i i′ : Γ ∋ A) → Dec (i ≡ i′)
  zero  ≟∋ zero   = yes refl
  zero  ≟∋ suc i′ = no λ ()
  suc i ≟∋ zero   = no λ ()
  suc i ≟∋ suc i′ with i ≟∋ i′
  ... | yes refl    = yes refl
  ... | no ¬eq      = no λ { refl → refl ↯ ¬eq }


----------------------------------------------------------------------------------------------------

module CtxKit (Ty : Set) where
  Ctx : Set
  Ctx = List Ty


----------------------------------------------------------------------------------------------------

  module ⊢*Kit
    (Tm : Ctx → Ty → Set)
      where
    private
      infix 3 _⊢_
      _⊢_ = Tm

    ty : ∀ {Γ A} → Γ ⊢ A → Ty
    ty {A = A} t = A

    -- simultaneous substitutions
    infix 3 _⊢*_
    data _⊢*_ (Γ : Ctx) : Ctx → Set where
      []  : Γ ⊢* []
      _∷_ : ∀ {A Δ} (t : Γ ⊢ A) (ts : Γ ⊢* Δ) → Γ ⊢* A ∷ Δ


----------------------------------------------------------------------------------------------------

    module RenKit
      (`v  : ∀ {Γ A} → Γ ∋ A → Γ ⊢ A)
      (ren : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A)
        where
      weak : ∀ {Γ A B} → Γ ⊢ B → A ∷ Γ ⊢ B
      weak t = ren wk⊆ t

      ren* : ∀ {Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⊢* Δ → Γ′ ⊢* Δ
      ren* e []       = []
      ren* e (t ∷ ts) = ren e t ∷ ren* e ts

      weak* : ∀ {Γ Δ A} → Γ ⊢* Δ → A ∷ Γ ⊢* Δ
      weak* ts = ren* wk⊆ ts

      lift* : ∀ {Γ Δ A} → Γ ⊢* Δ → A ∷ Γ ⊢* A ∷ Δ
      lift* ts = `v zero ∷ weak* ts

      refl* : ∀ {Γ} → Γ ⊢* Γ
      refl* {[]}    = []
      refl* {A ∷ Γ} = lift* refl*

      -- substitution of indices
      sub∋ : ∀ {Γ Ξ A} → Ξ ⊢* Γ → Γ ∋ A → Ξ ⊢ A
      sub∋ (s ∷ ss) zero    = s
      sub∋ (s ∷ ss) (suc i) = sub∋ ss i


----------------------------------------------------------------------------------------------------

      module SubKit
        (sub : ∀ {Γ Ξ A} → Ξ ⊢* Γ → Γ ⊢ A → Ξ ⊢ A)
          where
        sub* : ∀ {Γ Ξ Δ} → Ξ ⊢* Γ → Γ ⊢* Δ → Ξ ⊢* Δ
        sub* ss []       = []
        sub* ss (t ∷ ts) = sub ss t ∷ sub* ss ts

        _[_] : ∀ {Γ A B} → A ∷ Γ ⊢ B → Γ ⊢ A → Γ ⊢ B
        t [ s ] = sub (s ∷ refl*) t

        _[_∣_] : ∀ {Γ A B C} → B ∷ A ∷ Γ ⊢ C → Γ ⊢ A → Γ ⊢ B → Γ ⊢ C
        t [ s₁ ∣ s₂ ] = sub (s₂ ∷ s₁ ∷ refl*) t

        get* : ∀ {Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⊢* Δ′ → Γ ⊢* Δ
        get* stop     ts       = ts
        get* (drop e) (t ∷ ts) = get* e ts
        get* (keep e) (t ∷ ts) = t ∷ get* e ts


----------------------------------------------------------------------------------------------------

    module ≝Kit
      {_≝_    : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set}
      (refl≝  : ∀ {Γ A} {t : Γ ⊢ A} → t ≝ t)
      (sym≝   : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ≝ t′ → t′ ≝ t)
      (trans≝ : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ≝ t′ → t′ ≝ t″ → t ≝ t″)
        where
      ≡→≝ : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ≡ t′ → t ≝ t′
      ≡→≝ refl = refl≝

      module ≝-Reasoning where
        infix 1 begin_
        begin_ : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ≝ t′ → t ≝ t′
        begin_ eq = eq

        infixr 2 _≝⟨⟩_
        _≝⟨⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′} → t ≝ t′ → t ≝ t′
        t ≝⟨⟩ eq = eq

        infixr 2 _≝⟨_⟩_
        _≝⟨_⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′ t″} → t ≝ t′ → t′ ≝ t″ → t ≝ t″
        t ≝⟨ eq ⟩ eq′ = trans≝ eq eq′

        infixr 2 _≝˘⟨_⟩_
        _≝˘⟨_⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′ t″} → t′ ≝ t → t′ ≝ t″ → t ≝ t″
        t ≝˘⟨ eq ⟩ eq′ = trans≝ (sym≝ eq) eq′

        infixr 2 _≡⟨_⟩_
        _≡⟨_⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′ t″} → t ≡ t′ → t′ ≝ t″ → t ≝ t″
        t ≡⟨ eq ⟩ eq′ = trans≝ (≡→≝ eq) eq′

        infixr 2 _≡˘⟨_⟩_
        _≡˘⟨_⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′ t″} → t′ ≡ t → t′ ≝ t″ → t ≝ t″
        t ≡˘⟨ eq ⟩ eq′ = trans≝ (≡→≝ (sym eq)) eq′

        infix 3 _∎
        _∎ : ∀ {Γ A} (t : Γ ⊢ A) → t ≝ t
        t ∎ = refl≝


----------------------------------------------------------------------------------------------------

    module ⇒Kit
      (Red : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set)
        where
      private
        infix 4 _⇒_
        _⇒_ = Red

      -- reducible forms
      RF : ∀ {Γ A} → Γ ⊢ A → Set
      RF t = Σ _ λ t′ → t ⇒ t′

      -- irreducible forms
      ¬R : ∀ {Γ A} → Γ ⊢ A → Set
      ¬R t = ∀ {t′} → ¬ t ⇒ t′

      ¬RF→¬R : ∀ {Γ A} {t : Γ ⊢ A} → ¬ RF t → ¬R t
      ¬RF→¬R ¬p r = (_ , r) ↯ ¬p

      ¬R→¬RF : ∀ {Γ A} {t : Γ ⊢ A} → ¬R t → ¬ RF t
      ¬R→¬RF ¬r (_ , r) = r ↯ ¬r

      data Prog {Γ A} (NF : ∀ {Γ A} → Γ ⊢ A → Set) (t : Γ ⊢ A) : Set where
        step : ∀ {t′} (r : t ⇒ t′) → Prog NF t
        done : ∀ (p : NF t) → Prog NF t

      -- iterated reduction
      infix 4 _⇒*_
      data _⇒*_ {Γ A} : Γ ⊢ A → Γ ⊢ A → Set where
        done : ∀ {t} → t ⇒* t
        step : ∀ {t t′ t″} (r : t ⇒ t′) (rs : t′ ⇒* t″) → t ⇒* t″

      trans⇒* : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒* t′ → t′ ⇒* t″ → t ⇒* t″
      trans⇒* done        rs′ = rs′
      trans⇒* (step r rs) rs′ = step r (trans⇒* rs rs′)

      ≡→⇒* : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ≡ t′ → t ⇒* t′
      ≡→⇒* refl = done

      module ⇒-Reasoning where
        infix 1 begin_
        begin_ : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇒* t′ → t ⇒* t′
        begin_ rs = rs

        infixr 2 _⇒⟨_⟩_
        _⇒⟨_⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′ t″} → t ⇒ t′ → t′ ⇒* t″ → t ⇒* t″
        t ⇒⟨ r ⟩ rs = step r rs

        infixr 2 _⇒*⟨⟩_
        _⇒*⟨⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′} → t ⇒* t′ → t ⇒* t′
        t ⇒*⟨⟩ rs = rs

        infixr 2 _⇒*⟨_⟩_
        _⇒*⟨_⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′ t″} → t ⇒* t′ → t′ ⇒* t″ → t ⇒* t″
        t ⇒*⟨ rs ⟩ rs′ = trans⇒* rs rs′

        infixr 2 _≡⟨_⟩_
        _≡⟨_⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′ t″} → t ≡ t′ → t′ ⇒* t″ → t ⇒* t″
        t ≡⟨ eq ⟩ rs′ = trans⇒* (≡→⇒* eq) rs′

        infixr 2 _≡˘⟨_⟩_
        _≡˘⟨_⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′ t″} → t′ ≡ t → t′ ⇒* t″ → t ⇒* t″
        t ≡˘⟨ eq ⟩ rs′ = trans⇒* (≡→⇒* (sym eq)) rs′

        infix 3 _∎
        _∎ : ∀ {Γ A} (t : Γ ⊢ A) → t ⇒* t
        t ∎ = done


----------------------------------------------------------------------------------------------------

      -- TODO: delete?
      module ProgKit
        {NF     : ∀ {Γ A} → Γ ⊢ A → Set}
        (NF→¬R : ∀ {Γ A} {t : Γ ⊢ A} → NF t → ¬R t)
        (prog⇒ : ∀ {Γ A} (t : Γ ⊢ A) → Prog NF t)
          where
        ¬R→NF : ∀ {Γ A} {t : Γ ⊢ A} → ¬R t → NF t
        ¬R→NF {t = t} ¬r with prog⇒ t
        ... | step r        = r ↯ ¬r
        ... | done p        = p

        ¬NF→RF : ∀ {Γ A} {t : Γ ⊢ A} → ¬ NF t → RF t
        ¬NF→RF {t = t} ¬p with prog⇒ t
        ... | step r         = (_ , r)
        ... | done p         = p ↯ ¬p

        RF→¬NF : ∀ {Γ A} {t : Γ ⊢ A} → RF t → ¬ NF t
        RF→¬NF (_ , r) p = r ↯ NF→¬R p

        ¬RF→NF : ∀ {Γ A} {t : Γ ⊢ A} → ¬ RF t → NF t
        ¬RF→NF = ¬R→NF ∘ ¬RF→¬R

        NF→¬RF : ∀ {Γ A} {t : Γ ⊢ A} → NF t → ¬ RF t
        NF→¬RF = ¬R→¬RF ∘ NF→¬R


----------------------------------------------------------------------------------------------------

      module DetKit
        {NF     : ∀ {Γ A} → Γ ⊢ A → Set}
        (NF→¬R : ∀ {Γ A} {t : Γ ⊢ A} → NF t → ¬R t)
        (det⇒  : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒ t′ → t ⇒ t″ → t′ ≡ t″)
          where
        skip⇒ : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → NF t″ → t ⇒ t′ → t ⇒* t″ → t′ ⇒* t″
        skip⇒ p″ r done          = r ↯ NF→¬R p″
        skip⇒ p″ r (step r′ rs′) with det⇒ r r′
        ... | refl                  = rs′

        -- determinism
        det⇒* : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → NF t′ → NF t″ → t ⇒* t′ → t ⇒* t″ → t′ ≡ t″
        det⇒* p′ p″ done        done          = refl
        det⇒* p′ p″ done        (step r′ rs′) = r′ ↯ NF→¬R p′
        det⇒* p′ p″ (step r rs) rs′           = det⇒* p′ p″ rs (skip⇒ p″ r rs′)

        -- local confluence
        lconf⇒ : ∀ {Γ A} {t t₁ t₂ : Γ ⊢ A} → t ⇒ t₁ → t ⇒ t₂ →
                  Σ _ λ t′ → t₁ ⇒* t′ × t₂ ⇒* t′
        lconf⇒ r r′ with det⇒ r r′
        ... | refl     = _ , done , done

        -- global confluence
        gconf⇒ : ∀ {Γ A} {t t₁ t₂ : Γ ⊢ A} → t ⇒* t₁ → t ⇒* t₂ →
                  Σ _ λ t′ → t₁ ⇒* t′ × t₂ ⇒* t′
        gconf⇒ done        rs′           = _ , rs′ , done
        gconf⇒ (step r rs) done          = _ , done , step r rs
        gconf⇒ (step r rs) (step r′ rs′) with det⇒ r r′
        ... | refl                          = gconf⇒ rs rs′


----------------------------------------------------------------------------------------------------
