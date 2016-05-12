module Try8 where

{-

...
          ⇑²   ⇓³
level 3:  t₂ : t : u : A
          ⇑    ⇓²
level 2:  t : u : A
          !    ⇓
level 1:  u : A
          int  ¡
level 0:  A true

-}


infixl 3 _∘_ _∘²_ _∘³_
infixl 2 𝜆_ 𝜆²_ 𝜆³_
infixr 1 _⊃_
infixr 0 _⊢_ ⊩_
infixr 0 _⊢_∷_ ⊩_∷_
infixr 0 _⊢_∷_∷_ ⊩_∷_∷_
infixr 0 _⊢_∷_∷_∷_


mutual
  data Cx : Set where
    ∅   : Cx
    _,_ : Cx → Ty → Cx

  data Ty : Set where
    ⊥   : Ty
    _⊃_ : Ty → Ty → Ty
    [_∶_]     : (A : Ty) → ∅ ⊢ A → Ty
    τ_∷_∷_   : (A : Ty) (t : ∅ ⊢ A) → ∅ ⊢ A ∷ t → Ty
    τ_∷_∷_∷_ : (A : Ty) (t : ∅ ⊢ A) (t₂ : ∅ ⊢ A ∷ t) → ∅ ⊢ A ∷ t ∷ t₂ → Ty

  data _∈_ : Ty → Cx → Set where
    Z  : ∀{A Γ} → A ∈ (Γ , A)
    S_ : ∀{A B Γ} → A ∈ Γ → A ∈ (Γ , B)


  data _⊢_ (Γ : Cx) : Ty → Set where
    wk_ : ∀{A}  → ∅ ⊢ A
                → Γ ⊢ A

    wk′_ : ∀{A t}  → ∅ ⊢ A ∷ t
                   → Γ ⊢ [ A ∶ t ]

    wk″_ : ∀{A t t₂}  → ∅ ⊢ A ∷ t ∷ t₂
                      → Γ ⊢ (τ A ∷ t ∷ t₂)

    𝑣_ : ∀{A}  → A ∈ Γ
               → Γ ⊢ A

    𝜆_ : ∀{A B}  → Γ , A ⊢ B
                 → Γ ⊢ A ⊃ B

    _∘_ : ∀{A B}  → Γ ⊢ A ⊃ B  → Γ ⊢ A
                  → Γ ⊢ B

    !_ : ∀{A}  → (u : ∅ ⊢ A)
               → Γ ⊢ [ A ∶ u ]

    ⇓_ : ∀{A u}  → Γ ⊢ A ∷ u
                 → Γ ⊢ A


  data _⊢_∷_ (Γ : Cx) : (A : Ty) → Γ ⊢ A → Set where
    wk_ : ∀{A t}  → ∅ ⊢ A ∷ t
                  → Γ ⊢ A ∷ wk t

    wk′_ : ∀{A t t₂}  → ∅ ⊢ A ∷ t ∷ t₂
                      → Γ ⊢ [ A ∶ t ] ∷ wk′ t₂

    wk″_ : ∀{A t t₂ t₃}  → ∅ ⊢ A ∷ t ∷ t₂ ∷ t₃
                         → Γ ⊢ (τ A ∷ t ∷ t₂) ∷ wk″ t₃

--    kw_  : ∀{A t}  → Γ ⊢ (τ A ∷ t)
--                   → Γ ⊢ A ∷ wk t

    𝑣_ : ∀{A x}  → [ A ∶ x ] ∈ Γ
                 → Γ ⊢ A ∷ wk x

    𝑣²_ : ∀{A}  → (x : A ∈ Γ)
                → Γ ⊢ A ∷ 𝑣 x

    𝜆²_ : ∀{A B t}  → Γ , A ⊢ B ∷ t
                    → Γ ⊢ A ⊃ B ∷ 𝜆 t

    _∘²_ : ∀{A B t s}  → Γ ⊢ A ⊃ B ∷ t  → Γ ⊢ A ∷ s
                       → Γ ⊢ B ∷ t ∘ s

    !_ : ∀{A}  → (u : Γ ⊢ A)
               → Γ ⊢ A ∷ u

    ⇑_ : ∀{A u}  → Γ ⊢ [ A ∶ u ]
                 → Γ ⊢ [ A ∶ u ] ∷ ! u

    ⇓²_ : ∀{A u t}  → Γ ⊢ A ∷ u ∷ t
                    → Γ ⊢ A ∷ ⇓ t


  data _⊢_∷_∷_ (Γ : Cx) : (A : Ty) (t : Γ ⊢ A) → Γ ⊢ A ∷ t → Set where
    wk_ : ∀{A t t₂}  → ∅ ⊢ A ∷ t ∷ t₂
                     → Γ ⊢ A ∷ wk t ∷ wk t₂

    wk′_ : ∀{A t t₂ t₃}  → ∅ ⊢ A ∷ t ∷ t₂ ∷ t₃
                         → Γ ⊢ [ A ∶ t ] ∷ wk′ t₂ ∷ wk′ t₃

--    kw_  : ∀{A t t₂}  → Γ ⊢ (τ A ∷ t ∷ t₂)
--                      → Γ ⊢ A ∷ wk t ∷ wk t₂

    𝑣_ : ∀{A x x₂}  → (τ A ∷ x ∷ x₂) ∈ Γ
                    → Γ ⊢ A ∷ wk x ∷ wk x₂

    𝑣³_ : ∀{A}  → (x : A ∈ Γ)
                → Γ ⊢ A ∷ 𝑣 x ∷ 𝑣² x

    𝜆³_ : ∀{A B t t₂}  → Γ , A ⊢ B ∷ t ∷ t₂
                       → Γ ⊢ A ⊃ B ∷ 𝜆 t ∷ 𝜆² t₂

    _∘³_ : ∀{A B t t₂ s s₂}  → Γ ⊢ A ⊃ B ∷ t ∷ t₂  → Γ ⊢ A ∷ s ∷ s₂
                             → Γ ⊢ B ∷ t ∘ s ∷ t₂ ∘² s₂

    ⇑_ : ∀{A u}  → Γ ⊢ A ∷ u
                 → Γ ⊢ A ∷ u ∷ ! u

    ⇓³_ : ∀{A u t t₂}  → Γ ⊢ A ∷ u ∷ t ∷ t₂
                       → Γ ⊢ A ∷ ⇓ t ∷ ⇓² t₂


  data _⊢_∷_∷_∷_ (Γ : Cx) : (A : Ty) (t : Γ ⊢ A) (t₂ : Γ ⊢ A ∷ t) → Γ ⊢ A ∷ t ∷ t₂ → Set where
    ⇑²_ : ∀{A u t}  → Γ ⊢ A ∷ u ∷ t
                    → Γ ⊢ A ∷ u ∷ ! u ∷ ⇑ t


⊩_ : Ty → Set
⊩ A = {Γ : Cx} → Γ ⊢ A

⊩_∷_ : (A : Ty) → ∅ ⊢ A → Set
⊩ A ∷ t = {Γ : Cx} → Γ ⊢ A ∷ wk t

⊩_∷_∷_ : (A : Ty) (t : ∅ ⊢ A) → ∅ ⊢ A ∷ t → Set
⊩ A ∷ t ∷ t₂ = {Γ : Cx} → Γ ⊢ A ∷ wk t ∷ wk t₂


eI : ∀{Γ A} → Γ ⊢ A ⊃ A
eI = 𝜆 𝑣 Z

eI² : ∀{Γ A} → Γ ⊢ A ⊃ A ∷ 𝜆 𝑣 Z
eI² = 𝜆² 𝑣² Z

eI²′ : ∀{Γ A} → Γ ⊢ A ⊃ A ∷ 𝜆 𝑣 Z
eI²′ = ! (𝜆 𝑣 Z)

eI³ : ∀{Γ A} → Γ ⊢ A ⊃ A ∷ 𝜆 𝑣 Z ∷ 𝜆² 𝑣² Z
eI³ = 𝜆³ 𝑣³ Z

eI³′ : ∀{Γ A} → Γ ⊢ A ⊃ A ∷ 𝜆 𝑣 Z ∷ ! (𝜆 𝑣 Z)
eI³′ = ⇑ (! (𝜆 𝑣 Z))


{-
proposition:
  if x proves A, then A.
proof:
  assume x proves A.
  reflect x.
-}

e11 : ∀{Γ A x} → Γ ⊢ [ A ∶ 𝑣 x ] ⊃ A ∷ 𝜆 ⇓ 𝑣 Z
e11 = ! (𝜆 ⇓ 𝑣 Z)  -- why "!"?

{-
proposition:
  if x proves A, then !x proves that x proves A.
proof:
  assume x proves A.
  reify x.
-}

e12 : ∀{Γ A x} → Γ ⊢ [ A ∶ 𝑣 x ] ⊃ (τ A ∷ 𝑣 x ∷ ! 𝑣 x) ∷ 𝜆 {!⇑ ?!}
e12 = {!!}


--                Γ ⊢    A ∷ u    ∷  !  u
--Γ , (τ A ∷ (𝑣 x)) ⊢ (τ A ∷ 𝑣 x) ∷ (! (𝑣 x))
