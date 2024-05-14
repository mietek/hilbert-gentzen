{-

'(agda-input-user-translations
   (quote
    (("i" "⊃") (":" "∵") ("e" "⊢") ("t" "⊩")
     ("N" "ℕ") ("'" "′") ("''" "″") ("'''" "‴")
     ("v" "𝑣") ("v0" "𝑣⁰") ("v1" "𝑣¹") ("v2" "𝑣²") ("v3" "𝑣³") ("vn" "𝑣ⁿ")
     ("l" "𝜆") ("l0" "𝜆⁰") ("l1" "𝜆¹") ("l2" "𝜆²") ("l3" "𝜆³") ("ln" "𝜆ⁿ")
     ("o" "∘") ("o0" "∘⁰") ("o1" "∘¹") ("o2" "∘²") ("o3" "∘³") ("on" "∘ⁿ")
     ("p" "𝑝") ("p0" "𝑝⁰") ("p1" "𝑝¹") ("p2" "𝑝²") ("p3" "𝑝³") ("pn" "𝑝ⁿ")
     ("1" "𝜋₀") ("10" "𝜋₀⁰") ("11" "𝜋₀¹") ("12" "𝜋₀²") ("13" "𝜋₀³") ("1n" "𝜋₀ⁿ")
     ("2" "𝜋₁") ("20" "𝜋₁⁰") ("21" "𝜋₁¹") ("22" "𝜋₁²") ("23" "𝜋₁³") ("2n" "𝜋₁ⁿ")
     ("u" "⇑") ("u0" "⇑⁰") ("u1" "⇑¹") ("u2" "⇑²") ("u3" "⇑³") ("un" "⇑ⁿ")
     ("d" "⇓") ("d0" "⇓⁰") ("d1" "⇓¹") ("d2" "⇓²") ("d3" "⇓³") ("dn" "⇓ⁿ"))))

-}

module A201602.Try11 where

open import Data.Nat using (ℕ ; zero ; suc)

infixl 5 _∘_ _∘²_
infixr 4 𝜆_∙_ 𝜆²_∙_
infixr 3 _∵_
infixl 2 _∧_
infixr 1 _⊃_ _⊃⊂_
infixr 0 _⊢_
infixr 0 _⊢_∷_
infixr 0 _⊢_∷_∷_
infixr 0 _⊢_∷_∷_∷_


Var : Set
Var = ℕ


mutual
  data Ty : Set where
    ⊥   : Ty
    _⊃_ : Ty → Ty → Ty
    _∧_ : Ty → Ty → Ty
    _∵_ : Tm → Ty → Ty

  data Tm : Set where
    𝑣_      : Var → Tm
    𝜆_∙_    : Var → Tm → Tm
    𝜆²_∙_   : Var → Tm → Tm
    _∘_     : Tm → Tm → Tm
    _∘²_    : Tm → Tm → Tm
    𝑝⟨_,_⟩  : Tm → Tm → Tm
    𝑝²⟨_,_⟩ : Tm → Tm → Tm
    𝜋₀_     : Tm → Tm
    𝜋₀²_    : Tm → Tm
    𝜋₁_     : Tm → Tm
    𝜋₁²_    : Tm → Tm
    !_      : Tm → Tm
    ⇑_      : Tm → Tm
    ⇑²_     : Tm → Tm
    ⇓_      : Tm → Tm
    ⇓²_     : Tm → Tm


⊤ : Ty
⊤ = ⊥ ⊃ ⊥

¬_ : Ty → Ty
¬ A = A ⊃ ⊥

_⊃⊂_ : Ty → Ty → Ty
A ⊃⊂ B = A ⊃ B ∧ B ⊃ A


data Cx : ℕ → Set where
  ∅   : Cx zero
  _,_ : ∀{n} → Cx n → Ty → Cx (suc n)

data _∈_ : ∀{n} → Ty → Cx n → Set where
  Z  : ∀{n A} {Γ : Cx n}  → A ∈ (Γ , A)
  S_ : ∀{n A B} {Γ : Cx n}  → A ∈ Γ  → A ∈ (Γ , B)


mutual
  data _⊢_ {n : ℕ} (Γ : Cx n) : Ty → Set where
    M𝑣⁰ : ∀{A}  → A ∈ Γ
                → Γ ⊢ A

    M𝜆⁰ : ∀{A B}  → Γ , A ⊢ B
                  → Γ ⊢ A ⊃ B

    M∘⁰ : ∀{A B}  → Γ ⊢ A ⊃ B   → Γ ⊢ A
                  → Γ ⊢ B

    M𝑝⁰ : ∀{A B}  → Γ ⊢ A   → Γ ⊢ B
                  → Γ ⊢ A ∧ B

    M𝜋₀⁰ : ∀{A B}  → Γ ⊢ A ∧ B
                   → Γ ⊢ A

    M𝜋₁⁰ : ∀{A B}  → Γ ⊢ A ∧ B
                   → Γ ⊢ B

    M⇑⁰ : ∀{A u}  → Γ ⊢ u ∵ A
                  → Γ ⊢ ! u ∵ u ∵ A

    M⇓⁰ : ∀{A u}  → Γ ⊢ u ∵ A
                  → Γ ⊢ A

    M⁰⁺¹ : ∀{A u}  → Γ ⊢ u ∷ A
                   → Γ ⊢ u ∵ A


  data _⊢_∷_ {n : ℕ} (Γ : Cx n) : Tm → Ty → Set where
    M𝑣¹ : ∀{A t}  → (t ∵ A) ∈ Γ
                  → Γ ⊢ t ∷ A

    M𝜆¹ : ∀{A B x t}  → Γ , (𝑣 x ∵ A) ⊢ t ∷ B
                      → Γ ⊢ 𝜆 x ∙ t ∷ A ⊃ B

    M∘¹ : ∀{A B t s}  → Γ ⊢ t ∷ A ⊃ B  → Γ ⊢ s ∷ A
                      → Γ ⊢ t ∘ s ∷ B

    M𝑝¹ : ∀{A B t s}  → Γ ⊢ t ∷ A  → Γ ⊢ s ∷ B
                      → Γ ⊢ 𝑝⟨ t , s ⟩ ∷ A ∧ B

    M𝜋₀¹ : ∀{A B t}  → Γ ⊢ t ∷ A ∧ B
                     → Γ ⊢ 𝜋₀ t ∷ A

    M𝜋₁¹ : ∀{A B t}  → Γ ⊢ t ∷ A ∧ B
                     → Γ ⊢ 𝜋₁ t ∷ B

    M⇑¹ : ∀{A u t}  → Γ ⊢ t ∷ u ∵ A
                    → Γ ⊢ ⇑ t ∷ ! u ∵ u ∵ A

    M⇓¹ : ∀{A u t}  → Γ ⊢ t ∷ u ∵ A
                    → Γ ⊢ ⇓ t ∷ A

    M¹⁻¹ : ∀{A u t}  → Γ ⊢ t ∵ u ∵ A
                     → Γ ⊢ t ∷ u ∵ A

    M¹⁺¹ : ∀{A u t}  → Γ ⊢ t ∷ u ∷ A
                     → Γ ⊢ t ∷ u ∵ A


  data _⊢_∷_∷_ {n : ℕ} (Γ : Cx n) : Tm → Tm → Ty → Set where
    M𝑣² : ∀{A t t₂}  → (t₂ ∵ t ∵ A) ∈ Γ
                     → Γ ⊢ t₂ ∷ t ∷ A

    M𝜆² : ∀{A B x t x₂ t₂}  → Γ , (𝑣 x₂ ∵ 𝑣 x ∵ A) ⊢ t₂ ∷ t ∷ B
                            → Γ ⊢ 𝜆² x₂ ∙ t₂ ∷ 𝜆 x ∙ t ∷ A ⊃ B

    M∘² : ∀{A B t s t₂ s₂}  → Γ ⊢ t₂ ∷ t ∷ A ⊃ B  → Γ ⊢ s₂ ∷ s ∷ A
                            → Γ ⊢ t₂ ∘² s₂ ∷ t ∘ s ∷ B

    M𝑝² : ∀{A B t s t₂ s₂}  → Γ ⊢ t₂ ∷ t ∷ A  → Γ ⊢ s₂ ∷ s ∷ B
                            → Γ ⊢ 𝑝²⟨ t₂ , s₂ ⟩ ∷ 𝑝⟨ t , s ⟩ ∷ A ∧ B

    M𝜋₀² : ∀{A B t t₂}  → Γ ⊢ t₂ ∷ t ∷ A ∧ B
                        → Γ ⊢ 𝜋₀² t₂ ∷ 𝜋₀ t ∷ A

    M𝜋₁² : ∀{A B t t₂}  → Γ ⊢ t₂ ∷ t ∷ A ∧ B
                        → Γ ⊢ 𝜋₁² t₂ ∷ 𝜋₁ t ∷ B

    M⇑² : ∀{A u t t₂}  → Γ ⊢ t₂ ∷ t ∷ u ∵ A
                       → Γ ⊢ ⇑² t₂ ∷ ⇑ t ∷ ! u ∵ u ∵ A

    M⇓² : ∀{A u t t₂}  → Γ ⊢ t₂ ∷ t ∷ u ∵ A
                       → Γ ⊢ ⇓² t₂ ∷ ⇓ t ∷ A

    M²⁻² : ∀{A u t t₂}  → Γ ⊢ t₂ ∵ t ∵ u ∵ A
                        → Γ ⊢ t₂ ∷ t ∷ u ∵ A

    M²⁻¹ : ∀{A u t t₂}  → Γ ⊢ t₂ ∷ t ∵ u ∵ A
                        → Γ ⊢ t₂ ∷ t ∷ u ∵ A

    M²⁺¹ : ∀{A u t t₂}  → Γ ⊢ t₂ ∷ t ∷ u ∷ A
                        → Γ ⊢ t₂ ∷ t ∷ u ∵ A


  data _⊢_∷_∷_∷_ {n : ℕ} (Γ : Cx n) : Tm → Tm → Tm → Ty → Set where


eI⁰ : ∀{n A} {Γ : Cx n}
    → Γ ⊢ A ⊃ A
eI⁰ = M𝜆⁰ (M𝑣⁰ Z)

eI¹ : ∀{n A x} {Γ : Cx n}
    → Γ ⊢ 𝜆 x ∙ 𝑣 x ∷ (A ⊃ A)
eI¹ = M𝜆¹ (M𝑣¹ Z)

eI² : ∀{n A x u} {Γ : Cx n}
    → Γ ⊢ 𝜆² u ∙ 𝑣 u ∷ 𝜆 x ∙ 𝑣 x ∷ (A ⊃ A)
eI² = M𝜆² (M𝑣² Z)


e11 : ∀{n A x y} {Γ : Cx n}
    → Γ ⊢ 𝜆 y ∙ ⇓ 𝑣 y ∷ (x ∵ A ⊃ A)
e11 = M𝜆¹ (M⇓¹ (M𝑣¹ Z))

e12 : ∀{n A x y} {Γ : Cx n}
    → Γ ⊢ 𝜆 y ∙ ⇑ 𝑣 y ∷ (x ∵ A ⊃ ! x ∵ x ∵ A)
e12 = M𝜆¹ (M⇑¹ (M𝑣¹ Z))

e13 : ∀{n A B x y u v} {Γ : Cx n}
    → Γ ⊢ 𝜆² u ∙ 𝜆² v ∙ 𝑝²⟨ 𝑣 u , 𝑣 v ⟩ ∷ 𝜆 x ∙ 𝜆 y ∙ 𝑝⟨ 𝑣 x , 𝑣 y ⟩ ∷ (A ⊃ B ⊃ A ∧ B)
e13 = M𝜆² (M𝜆² (M𝑝² (M𝑣² (S Z)) (M𝑣² Z)))

e14 : ∀{n A B x y u v} {Γ : Cx n}
    → Γ ⊢ 𝜆 u ∙ 𝜆 v ∙ ⇑ 𝑝²⟨ 𝑣 u , 𝑣 v ⟩ ∷ (x ∵ A ⊃ y ∵ B ⊃ ! 𝑝⟨ x , y ⟩ ∵ 𝑝⟨ x , y ⟩ ∵ (A ∧ B))
e14 = M𝜆¹ (M𝜆¹ (M⇑¹ (M¹⁺¹ (M𝑝² (M𝑣² (S Z)) (M𝑣² Z)))))
