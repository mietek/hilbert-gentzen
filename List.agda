module List where

open import Prelude
open import Fin


--------------------------------------------------------------------------------


data List (X : Set) : Set
  where
    ∙   : List X
    _,_ : List X → X → List X


len : ∀ {X} → List X
            → Nat
len ∙       = zero
len (Ξ , A) = suc (len Ξ)


map : ∀ {X Y} → (X → Y) → List X
              → List Y
map F ∙       = ∙
map F (Ξ , A) = map F Ξ , F A


--------------------------------------------------------------------------------


GET : ∀ {X n} → (Ξ : List X) {{_ : len Ξ ≡ n}} → Fin n
              → X
GET ∙       {{refl}} ()
GET (Ξ , A) {{refl}} zero    = A
GET (Ξ , B) {{refl}} (suc i) = GET Ξ i


GETS : ∀ {X n n′} → (Ξ : List X) {{_ : len Ξ ≡ n′}} → n′ ≥ n
                  → List X
GETS ∙       {{refl}} done     = ∙
GETS (Ξ , B) {{refl}} (drop e) = GETS Ξ e
GETS (Ξ , A) {{refl}} (keep e) = GETS Ξ e , A


--------------------------------------------------------------------------------


infix 4 _⊇_
data _⊇_ {X} : List X → List X → Set
  where
    done : ∙ ⊇ ∙

    drop : ∀ {A Ξ Ξ′} → Ξ′ ⊇ Ξ
                      → Ξ′ , A ⊇ Ξ

    keep : ∀ {A Ξ Ξ′} → Ξ′ ⊇ Ξ
                      → Ξ′ , A ⊇ Ξ , A


bot⊇ : ∀ {X} → {Ξ : List X}
             → Ξ ⊇ ∙
bot⊇ {Ξ = ∙}     = done
bot⊇ {Ξ = Ξ , A} = drop bot⊇


id⊇ : ∀ {X} → {Ξ : List X}
            → Ξ ⊇ Ξ
id⊇ {Ξ = ∙}     = done
id⊇ {Ξ = Ξ , A} = keep id⊇


_∘⊇_ : ∀ {X} → {Ξ Ξ′ Ξ″ : List X}
             → Ξ′ ⊇ Ξ → Ξ″ ⊇ Ξ′
             → Ξ″ ⊇ Ξ
η₁      ∘⊇ done    = η₁
η₁      ∘⊇ drop η₂ = drop (η₁ ∘⊇ η₂)
drop η₁ ∘⊇ keep η₂ = drop (η₁ ∘⊇ η₂)
keep η₁ ∘⊇ keep η₂ = keep (η₁ ∘⊇ η₂)


--------------------------------------------------------------------------------


infix 4 _∋_
data _∋_ {X} : List X → X → Set
  where
    zero : ∀ {A Ξ} → Ξ , A ∋ A

    suc : ∀ {A B Ξ} → Ξ ∋ A
                    → Ξ , B ∋ A


ren∋ : ∀ {X A} → {Ξ Ξ′ : List X}
               → Ξ′ ⊇ Ξ → Ξ ∋ A
               → Ξ′ ∋ A
ren∋ done     𝒾       = 𝒾
ren∋ (drop η) 𝒾       = suc (ren∋ η 𝒾)
ren∋ (keep η) zero    = zero
ren∋ (keep η) (suc 𝒾) = suc (ren∋ η 𝒾)


--------------------------------------------------------------------------------
