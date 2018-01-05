module ListOrnaments where

open import Prelude
open import Fin
open import List


--------------------------------------------------------------------------------


infix 4 _⊇⟨_⟩_
data _⊇⟨_⟩_ {X P} : {Ξ Ξ′ : List X} → All P Ξ′ → Ξ′ ⊇ Ξ → All P Ξ → Set
  where
    done : ∙ ⊇⟨ done ⟩ ∙

    drop : ∀ {A Ξ Ξ′} → {η : Ξ′ ⊇ Ξ}
                         {x : P A} {ξ : All P Ξ} {ξ′ : All P Ξ′}
                      → ξ′ ⊇⟨ η ⟩ ξ
                      → ξ′ , x ⊇⟨ drop η ⟩ ξ

    keep : ∀ {A Ξ Ξ′} → {η : Ξ′ ⊇ Ξ}
                         {x : P A} {ξ : All P Ξ} {ξ′ : All P Ξ′}
                      → ξ′ ⊇⟨ η ⟩ ξ
                      → ξ′ , x ⊇⟨ keep η ⟩ ξ , x


bot⊇◇ : ∀ {X P} → {Ξ : List X} {ξ : All P Ξ}
                → ξ ⊇⟨ bot⊇ ⟩ ∙
bot⊇◇ {ξ = ∙}     = done
bot⊇◇ {ξ = ξ , x} = drop bot⊇◇


id⊇◇ : ∀ {X P} → {Ξ : List X} {ξ : All P Ξ}
               → ξ ⊇⟨ id⊇ ⟩ ξ
id⊇◇ {ξ = ∙}     = done
id⊇◇ {ξ = ξ , x} = keep id⊇◇


_∘⊇◇_ : ∀ {X P} → {Ξ Ξ′ Ξ″ : List X} {η₁ : Ξ′ ⊇ Ξ} {η₂ : Ξ″ ⊇ Ξ′}
                   {ξ : All P Ξ} {ξ′ : All P Ξ′} {ξ″ : All P Ξ″}
                → ξ′ ⊇⟨ η₁ ⟩ ξ → ξ″ ⊇⟨ η₂ ⟩ ξ′
                → ξ″ ⊇⟨ η₁ ∘⊇ η₂ ⟩ ξ
`η₁      ∘⊇◇ done     = `η₁
`η₁      ∘⊇◇ drop `η₂ = drop (`η₁ ∘⊇◇ `η₂)
drop `η₁ ∘⊇◇ keep `η₂ = drop (`η₁ ∘⊇◇ `η₂)
keep `η₁ ∘⊇◇ keep `η₂ = keep (`η₁ ∘⊇◇ `η₂)


--------------------------------------------------------------------------------


infix 4 _∋⟨_⟩_
data _∋⟨_⟩_ {X P} : ∀ {A} → {Ξ : List X} → All P Ξ → Ξ ∋ A → P A → Set
  where
    zero : ∀ {Ξ A} → {ξ : All P Ξ} {x : P A}
                   → ξ , x ∋⟨ zero ⟩ x

    suc : ∀ {B Ξ A} → {𝒾 : Ξ ∋ A}
                       {y : P B} {ξ : All P Ξ} {x : P A}
                    → ξ ∋⟨ 𝒾 ⟩ x
                    → ξ , y ∋⟨ suc 𝒾 ⟩ x


ren∋◇ : ∀ {X P A} → {Ξ Ξ′ : List X} {η : Ξ′ ⊇ Ξ} {𝒾 : Ξ ∋ A}
                     {ξ : All P Ξ} {ξ′ : All P Ξ′} {x : P A}
                  → ξ′ ⊇⟨ η ⟩ ξ → ξ ∋⟨ 𝒾 ⟩ x
                  → ξ′ ∋⟨ ren∋ η 𝒾 ⟩ x
ren∋◇ done      `𝒾       = `𝒾
ren∋◇ (drop `η) `𝒾       = suc (ren∋◇ `η `𝒾)
ren∋◇ (keep `η) zero     = zero
ren∋◇ (keep `η) (suc `𝒾) = suc (ren∋◇ `η `𝒾)


--------------------------------------------------------------------------------


data All◇ {X P} (`P : ∀ {A : X} → P A → Set) : ∀ {Ξ} → All P Ξ → Set
  where
    ∙ : All◇ `P ∙

    _,_ : ∀ {Ξ A} → {ξ : All P Ξ} {x : P A}
                  → All◇ `P ξ → `P x
                  → All◇ `P (ξ , x)


lookup◇ : ∀ {X P A} → {Ξ : List X} {x : P A}
                       {ξ : All P Ξ} {𝒾 : Ξ ∋ A}
                       {`P : ∀ {A} → P A → Set}
                    → All◇ `P ξ → ξ ∋⟨ 𝒾 ⟩ x
                    → `P x
lookup◇ (`ξ , `x) zero     = `x
lookup◇ (`ξ , `y) (suc `𝒾) = lookup◇ `ξ `𝒾


mapAll◇ : ∀ {X P} → {Ξ : List X} {Q : X → Set}
                     {f : ∀ {A} → P A → Q A} {ξ : All P Ξ}
                     {`P : ∀ {A} → P A → Set} {`Q : ∀ {A} → Q A → Set}
                  → (∀ {A} → {x : P A} → `P x → `Q (f x)) → All◇ `P ξ
                  → All◇ `Q (mapAll f ξ)
mapAll◇ `f ∙         = ∙
mapAll◇ `f (`ξ , `x) = mapAll◇ `f `ξ , `f `x



--------------------------------------------------------------------------------
