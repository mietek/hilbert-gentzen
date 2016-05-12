module Try9 where

open import Data.Nat using (ℕ)

{-

...
          ⇑³
level 3:  A ∋ u ∋ t ∋ t₂
          ⇑²  ⇓²
level 2:  A ∋ u ∋ t
          ⇑   ⇓²
level 1:  A ∋ u
          !   ⇓
level 0:  A true

-}


Var : Set
Var = ℕ


mutual
  infixl 5 _∷_
  infixl 4 _∧_
  infixr 3 _⊃_
  data Ty : Set where
    ⊥   : Ty
    _⊃_ : Ty → Ty → Ty
    _∧_ : Ty → Ty → Ty
    _∷_ : Ty → Tm → Ty

  infixl 9 !_
  data Tm : Set where
    𝑣_ : Var → Tm
    𝜆_∙_ : Var → Tm → Tm
    𝜆²_∙_ : Var → Tm → Tm
    _∘_ : Tm → Tm → Tm
    _∘²_ : Tm → Tm → Tm
    𝑝⟨_,_⟩ : Tm → Tm → Tm
    𝑝²⟨_,_⟩ : Tm → Tm → Tm
    𝜋₀_ : Tm → Tm
    𝜋₀²_ : Tm → Tm
    𝜋₁_ : Tm → Tm
    𝜋₁²_ : Tm → Tm
    !_ : Tm → Tm
    ⇑_ : Tm → Tm
    ⇑²_ : Tm → Tm
    ⇓_ : Tm → Tm
    ⇓²_ : Tm → Tm


infixl 2 _,_
data Cx : Set where
  ∅   : Cx
  _,_ : Cx → Ty → Cx

infixr 1 _∈_
data _∈_ : Ty → Cx → Set where
  Z  : ∀{Γ A}           → A ∈ Γ , A
  S_ : ∀{Γ A B} → A ∈ Γ → A ∈ Γ , B


mutual
  infixr 0 _⊢_true
  data _⊢_true (Γ : Cx) : Ty → Set where
    M𝑣⁰ : ∀{A}  → A ∈ Γ
                → Γ ⊢ A true

    M𝜆⁰ : ∀{A B}  → Γ , A ⊢ B true
                  → Γ ⊢ A ⊃ B true

    M∘⁰ : ∀{A B}  → Γ ⊢ A ⊃ B true  → Γ ⊢ A true
                  → Γ ⊢ B true

    M𝑝⁰ : ∀{A B}  → Γ ⊢ A true  → Γ ⊢ B true
                  → Γ ⊢ A ∧ B true

    M⇓⁰ : ∀{A u}  → Γ ⊢ A ∋ u
                  → Γ ⊢ A true

  infixr 0 _⊢_∋_
  data _⊢_∋_ (Γ : Cx) : Ty → Tm → Set where
    M𝑣¹ : ∀{A x}  → A ∷ 𝑣 x ∈ Γ
                  → Γ ⊢ A ∋ 𝑣 x

    M𝜆¹ : ∀{A B x t}  → Γ , A ∷ 𝑣 x ⊢ B ∋ t
                      → Γ ⊢ A ⊃ B ∋ 𝜆 x ∙ t

    M∘¹ : ∀{A B t s}  → Γ ⊢ A ⊃ B ∋ t  → Γ ⊢ A ∋ s
                      → Γ ⊢ B ∋ t ∘ s

    M𝑝¹ : ∀{A B t s}  → Γ ⊢ A ∋ t  → Γ ⊢ B ∋ s
                      → Γ ⊢ (A ∧ B) ∋ 𝑝⟨ t , s ⟩

    M⇓¹ : ∀{A u t}  → Γ ⊢ A ∷ u ∋ t
                    → Γ ⊢ A ∋ ⇓ t

    M⇑¹ : ∀{A u t}  → Γ ⊢ A ∷ u ∋ t
                    → Γ ⊢ A ∷ u ∷ ! u ∋ ⇑ t

  infixr 0 _⊢_∋_∋_
  data _⊢_∋_∋_ (Γ : Cx) : Ty → Tm → Tm → Set where
    M𝑣² : ∀{A x x₂}  → A ∷ 𝑣 x ∷ 𝑣 x₂ ∈ Γ
                     → Γ ⊢ A ∋ 𝑣 x ∋ 𝑣 x₂

    M𝜆² : ∀{A B x t x₂ t₂}  → Γ , A ∷ 𝑣 x ∷ 𝑣 x₂ ⊢ B ∋ t ∋ t₂
                            → Γ ⊢ A ⊃ B ∋ 𝜆 x ∙ t ∋ 𝜆² x₂ ∙ t₂

    M∘² : ∀{A B t s t₂ s₂}  → Γ ⊢ A ⊃ B ∋ t ∋ t₂  → Γ ⊢ A ∋ s ∋ s₂
                            → Γ ⊢ B ∋ t ∘ s ∋ t₂ ∘² s₂

    M𝑝² : ∀{A B t s t₂ s₂}  → Γ ⊢ A ∋ t ∋ t₂  → Γ ⊢ B ∋ s ∋ s₂
                            → Γ ⊢ (A ∧ B) ∋ 𝑝⟨ t , s ⟩ ∋ 𝑝²⟨ t₂ , s₂ ⟩

    M⇓² : ∀{A u t t₂}  → Γ ⊢ A ∷ u ∋ t ∋ t₂
                       → Γ ⊢ A ∋ ⇓ t ∋ ⇓² t₂

    M⇑² : ∀{A u t t₂}  → Γ ⊢ A ∷ u ∋ t ∋ t₂
                       → Γ ⊢ A ∷ u ∷ ! u ∋ ⇑ t ∋ ⇑² t₂

  infixr 0 _⊢_∋_∋_∋_
  data _⊢_∋_∋_∋_ (Γ : Cx) : Ty → Tm → Tm → Tm → Set where


eI⁰ : ∀{Γ A} → Γ ⊢ A ⊃ A true
eI⁰ = M𝜆⁰ (M𝑣⁰ Z)

eI¹ : ∀{Γ A x} → Γ ⊢ (A ⊃ A) ∋ 𝜆 x ∙ 𝑣 x
eI¹ = M𝜆¹ (M𝑣¹ Z)

eI² : ∀{Γ A x u} → Γ ⊢ (A ⊃ A) ∋ 𝜆 x ∙ 𝑣 x ∋ 𝜆² u ∙ 𝑣 u
eI² = M𝜆² (M𝑣² Z)


e11 : ∀{Γ A x y} → Γ ⊢ (A ∷ x ⊃ A) ∋ 𝜆 y ∙ ⇓ 𝑣 y
e11 = M𝜆¹ (M⇓¹ (M𝑣¹ Z))

e12 : ∀{Γ A x y} → Γ ⊢ (A ∷ x ⊃ A ∷ x ∷ ! x) ∋ 𝜆 y ∙ ⇑ 𝑣 y
e12 = M𝜆¹ (M⇑¹ (M𝑣¹ Z))

e13 : ∀{Γ A B x y u v} → Γ ⊢ (A ⊃ B ⊃ A ∧ B) ∋ 𝜆 x ∙ 𝜆 y ∙ 𝑝⟨ 𝑣 x , 𝑣 y ⟩ ∋ 𝜆² u ∙ 𝜆² v ∙ 𝑝²⟨ 𝑣 u , 𝑣 v ⟩
e13 = M𝜆² (M𝜆² (M𝑝² (M𝑣² (S Z)) (M𝑣² Z)))

e14 : ∀{Γ A B x y u v} → Γ ⊢ (A ∷ x ⊃ B ∷ y ⊃ (A ∧ B) ∷ 𝑝⟨ x , y ⟩ ∷ ! 𝑝⟨ x , y ⟩) ∋ 𝜆 u ∙ 𝜆 v ∙ ⇑ 𝑝²⟨ 𝑣 u , 𝑣 v ⟩
e14 = M𝜆¹ (M𝜆¹ (M⇑¹ {!M𝑝² ? ?!}))
