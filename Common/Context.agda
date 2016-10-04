module Common.Context where

open import Common public


-- Contexts.

data Cx (U : Set) : Set where
  ∅   : Cx U
  _,_ : Cx U → U → Cx U


-- Vector contexts.

data VCx (U : Set) : ℕ → Set where
  ∅   : VCx U zero
  _,_ : ∀ {n} → VCx U n → U → VCx U (suc n)


-- Inversion principles for contexts.

module _ {U : Set} where
  inv,₁ : ∀ {Γ Γ′ : Cx U} {A A′ : U} → (Γ Cx., A) ≡ (Γ′ , A′) → Γ ≡ Γ′
  inv,₁ refl = refl

  inv,₂ : ∀ {Γ Γ′ : Cx U} {A A′ : U} → (Γ Cx., A) ≡ (Γ′ , A′) → A ≡ A′
  inv,₂ refl = refl


-- Decidable equality for contexts.

module ContextEquality {U : Set} (_≟ᵁ_ : (A A′ : U) → Dec (A ≡ A′)) where
  _≟ᵀ⋆_ : (Γ Γ′ : Cx U) → Dec (Γ ≡ Γ′)
  ∅       ≟ᵀ⋆ ∅         = yes refl
  ∅       ≟ᵀ⋆ (Γ′ , A′) = no λ ()
  (Γ , A) ≟ᵀ⋆ ∅         = no λ ()
  (Γ , A) ≟ᵀ⋆ (Γ′ , A′) with Γ ≟ᵀ⋆ Γ′ | A ≟ᵁ A′
  (Γ , A) ≟ᵀ⋆ (.Γ , .A) | yes refl | yes refl = yes refl
  (Γ , A) ≟ᵀ⋆ (Γ′ , A′) | no  Γ≢Γ′ | _        = no (Γ≢Γ′ ∘ inv,₁)
  (Γ , A) ≟ᵀ⋆ (Γ′ , A′) | _        | no  A≢A′ = no (A≢A′ ∘ inv,₂)


-- Context membership, or nameless typed de Bruijn indices.

module _ {U : Set} where
  infix 3 _∈_
  data _∈_ (A : U) : Cx U → Set where
    instance
      top : ∀ {Γ} → A ∈ Γ , A
      pop : ∀ {B Γ} → A ∈ Γ → A ∈ Γ , B

  pop² : ∀ {A B C Γ} → A ∈ Γ → A ∈ Γ , B , C
  pop² = pop ∘ pop

  i₀ : ∀ {A Γ} → A ∈ Γ , A
  i₀ = top

  i₁ : ∀ {A B Γ} → A ∈ Γ , A , B
  i₁ = pop top

  i₂ : ∀ {A B C Γ} → A ∈ Γ , A , B , C
  i₂ = pop² top

  [_]ⁱ : ∀ {A Γ} → A ∈ Γ → ℕ
  [ top ]ⁱ   = zero
  [ pop i ]ⁱ = suc [ i ]ⁱ


-- Inversion priciples for context membership.

module _ {U : Set} where
  invpop : ∀ {A B : U} {Γ} {i i′ : A ∈ Γ} → pop {B = B} i ≡ pop i′ → i ≡ i′
  invpop refl = refl


-- Decidable equality for context membership.

module _ {U : Set} where
  _≟ⁱ_ : ∀ {A : U} {Γ} → (i i′ : A ∈ Γ) → Dec (i ≡ i′)
  top   ≟ⁱ top    = yes refl
  top   ≟ⁱ pop i′ = no λ ()
  pop i ≟ⁱ top    = no λ ()
  pop i ≟ⁱ pop i′ with i ≟ⁱ i′
  pop i ≟ⁱ pop .i | yes refl = yes refl
  pop i ≟ⁱ pop i′ | no  i≢i′ = no (i≢i′ ∘ invpop)


-- Context inclusion, or order-preserving embedding.

module _ {U : Set} where
  infix 3 _⊆_
  data _⊆_ : Cx U → Cx U → Set where
    instance
      done : ∅ ⊆ ∅
      skip : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊆ Γ′ , A
      keep : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ , A ⊆ Γ′ , A

  skip² : ∀ {A B Γ Γ′} → Γ ⊆ Γ′ → Γ ⊆ Γ′ , B , A
  skip² = skip ∘ skip

  keep² : ∀ {A B Γ Γ′} → Γ ⊆ Γ′ → Γ , B , A ⊆ Γ′ , B , A
  keep² = keep ∘ keep

  instance
    refl⊆ : ∀ {Γ} → Γ ⊆ Γ
    refl⊆ {∅}     = done
    refl⊆ {Γ , A} = keep refl⊆

  trans⊆ : ∀ {Γ Γ′ Γ″} → Γ ⊆ Γ′ → Γ′ ⊆ Γ″ → Γ ⊆ Γ″
  trans⊆ η        done      = η
  trans⊆ η        (skip η′) = skip (trans⊆ η η′)
  trans⊆ (skip η) (keep η′) = skip (trans⊆ η η′)
  trans⊆ (keep η) (keep η′) = keep (trans⊆ η η′)

  unskip⊆ : ∀ {A Γ Γ′} → Γ , A ⊆ Γ′ → Γ ⊆ Γ′
  unskip⊆ (skip η) = skip (unskip⊆ η)
  unskip⊆ (keep η) = skip η

  unkeep⊆ : ∀ {A Γ Γ′} → Γ , A ⊆ Γ′ , A → Γ ⊆ Γ′
  unkeep⊆ (skip η) = unskip⊆ η
  unkeep⊆ (keep η) = η

  weak⊆ : ∀ {A Γ} → Γ ⊆ Γ , A
  weak⊆ = skip refl⊆

  weak²⊆ : ∀ {A B Γ} → Γ ⊆ Γ , A , B
  weak²⊆ = skip² refl⊆

  bot⊆ : ∀ {Γ} → ∅ ⊆ Γ
  bot⊆ {∅}     = done
  bot⊆ {Γ , A} = skip bot⊆


-- Monotonicity of context membership with respect to context inclusion.

module _ {U : Set} where
  mono∈ : ∀ {A : U} {Γ Γ′} → Γ ⊆ Γ′ → A ∈ Γ → A ∈ Γ′
  mono∈ done     ()
  mono∈ (skip η) i       = pop (mono∈ η i)
  mono∈ (keep η) top     = top
  mono∈ (keep η) (pop i) = pop (mono∈ η i)

  reflmono∈ : ∀ {A Γ} → (i : A ∈ Γ) → i ≡ mono∈ refl⊆ i
  reflmono∈ top     = refl
  reflmono∈ (pop i) = cong pop (reflmono∈ i)

  transmono∈ : ∀ {A Γ Γ′ Γ″} → (η : Γ ⊆ Γ′) (η′ : Γ′ ⊆ Γ″) (i : A ∈ Γ)
               → mono∈ η′ (mono∈ η i) ≡ mono∈ (trans⊆ η η′) i
  transmono∈ done     η′        ()
  transmono∈ η        (skip η′) i       = cong pop (transmono∈ η η′ i)
  transmono∈ (skip η) (keep η′) i       = cong pop (transmono∈ η η′ i)
  transmono∈ (keep η) (keep η′) top     = refl
  transmono∈ (keep η) (keep η′) (pop i) = cong pop (transmono∈ η η′ i)


-- Concatenation of contexts.

module _ {U : Set} where
  _⧺_ : Cx U → Cx U → Cx U
  Γ ⧺ ∅        = Γ
  Γ ⧺ (Γ′ , A) = (Γ ⧺ Γ′) , A

  id⧺₁ : ∀ {Γ} → Γ ⧺ ∅ ≡ Γ
  id⧺₁ = refl

  id⧺₂ : ∀ {Γ} → ∅ ⧺ Γ ≡ Γ
  id⧺₂ {∅}     = refl
  id⧺₂ {Γ , A} = cong² _,_ id⧺₂ refl

  weak⊆⧺₁ : ∀ {Γ} Γ′ → Γ ⊆ Γ ⧺ Γ′
  weak⊆⧺₁ ∅        = refl⊆
  weak⊆⧺₁ (Γ′ , A) = skip (weak⊆⧺₁ Γ′)

  weak⊆⧺₂ : ∀ {Γ Γ′} → Γ′ ⊆ Γ ⧺ Γ′
  weak⊆⧺₂ {Γ} {∅}      = bot⊆
  weak⊆⧺₂ {Γ} {Γ′ , A} = keep weak⊆⧺₂


-- Thinning of contexts.

module _ {U : Set} where
  _∖_ : ∀ {A} → (Γ : Cx U) → A ∈ Γ → Cx U
  ∅       ∖ ()
  (Γ , A) ∖ top   = Γ
  (Γ , B) ∖ pop i = (Γ ∖ i) , B

  thin⊆ : ∀ {A Γ} → (i : A ∈ Γ) → Γ ∖ i ⊆ Γ
  thin⊆ top     = weak⊆
  thin⊆ (pop i) = keep (thin⊆ i)


-- Thinning-based decidable equality of context membership.

module _ {U : Set} where
  data _=∈_ {A : U} {Γ} (i : A ∈ Γ) : ∀ {B} → B ∈ Γ → Set where
    same : i =∈ i
    diff : ∀ {B} → (j : B ∈ Γ ∖ i) → i =∈ mono∈ (thin⊆ i) j

  _≟∈_ : ∀ {A B : U} {Γ} → (i : A ∈ Γ) (j : B ∈ Γ) → i =∈ j
  top   ≟∈ top    = same
  top   ≟∈ pop j  rewrite reflmono∈ j = diff j
  pop i ≟∈ top    = diff top
  pop i ≟∈ pop j  with i ≟∈ j
  pop i ≟∈ pop .i | same   = same
  pop i ≟∈ pop ._ | diff j = diff (pop j)
