module VecOrnaments where

open import Prelude
open import Fin
open import Vec


--------------------------------------------------------------------------------


infix 4 _⊇◇⟨_⟩_
data _⊇◇⟨_⟩_ {X P} : ∀ {n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′}
                                → All P Ξ′ → Ξ′ ⊇⟨ e ⟩ Ξ → All P Ξ → Set
  where
    done : ∙ ⊇◇⟨ done ⟩ ∙

    drop : ∀ {A n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {η : Ξ′ ⊇⟨ e ⟩ Ξ}
                           {x : P A} {ξ : All P Ξ} {ξ′ : All P Ξ′}
                        → ξ′ ⊇◇⟨ η ⟩ ξ
                        → ξ′ , x ⊇◇⟨ drop η ⟩ ξ

    keep : ∀ {A n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {η : Ξ′ ⊇⟨ e ⟩ Ξ}
                           {x : P A} {ξ : All P Ξ} {ξ′ : All P Ξ′}
                        → ξ′ ⊇◇⟨ η ⟩ ξ
                        → ξ′ , x ⊇◇⟨ keep η ⟩ ξ , x


bot⊇◇ : ∀ {X P n} → {Ξ : Vec X n} {ξ : All P Ξ}
                  → ξ ⊇◇⟨ bot⊇ ⟩ ∙
bot⊇◇ {ξ = ∙}     = done
bot⊇◇ {ξ = ξ , x} = drop bot⊇◇


id⊇◇ : ∀ {X P n} → {Ξ : Vec X n} {ξ : All P Ξ}
                 → ξ ⊇◇⟨ id⊇ ⟩ ξ
id⊇◇ {ξ = ∙}     = done
id⊇◇ {ξ = ξ , x} = keep id⊇◇


_∘⊇◇_ : ∀ {X P n n′ n″ e₁ e₂} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {Ξ″ : Vec X n″}
                                 {η₁ : Ξ′ ⊇⟨ e₁ ⟩ Ξ} {η₂ : Ξ″ ⊇⟨ e₂ ⟩ Ξ′}
                                 {ξ : All P Ξ} {ξ′ : All P Ξ′} {ξ″ : All P Ξ″}
                              → ξ′ ⊇◇⟨ η₁ ⟩ ξ → ξ″ ⊇◇⟨ η₂ ⟩ ξ′
                              → ξ″ ⊇◇⟨ η₁ ∘⊇ η₂ ⟩ ξ
`η₁      ∘⊇◇ done     = `η₁
`η₁      ∘⊇◇ drop `η₂ = drop (`η₁ ∘⊇◇ `η₂)
drop `η₁ ∘⊇◇ keep `η₂ = drop (`η₁ ∘⊇◇ `η₂)
keep `η₁ ∘⊇◇ keep `η₂ = keep (`η₁ ∘⊇◇ `η₂)


--------------------------------------------------------------------------------


infix 4 _∋◇⟨_⟩_
data _∋◇⟨_⟩_ {X P} : ∀ {A n i} → {Ξ : Vec X n}
                               → All P Ξ → Ξ ∋⟨ i ⟩ A → P A → Set
  where
    zero : ∀ {A n} → {Ξ : Vec X n}
                      {ξ : All P Ξ} {x : P A}
                   → ξ , x ∋◇⟨ zero ⟩ x

    suc : ∀ {B n i A} → {Ξ : Vec X n} {𝒾 : Ξ ∋⟨ i ⟩ A}
                         {y : P B} {ξ : All P Ξ} {x : P A}
                      → ξ ∋◇⟨ 𝒾 ⟩ x
                      → ξ , y ∋◇⟨ suc 𝒾 ⟩ x


ren∋◇ : ∀ {X P A n n′ e i} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {η : Ξ′ ⊇⟨ e ⟩ Ξ} {𝒾 : Ξ ∋⟨ i ⟩ A}
                              {ξ : All P Ξ} {ξ′ : All P Ξ′} {x : P A}
                           → ξ′ ⊇◇⟨ η ⟩ ξ → ξ ∋◇⟨ 𝒾 ⟩ x
                           → ξ′ ∋◇⟨ ren∋ η 𝒾 ⟩ x
ren∋◇ done      `𝒾       = `𝒾
ren∋◇ (drop `η) `𝒾       = suc (ren∋◇ `η `𝒾)
ren∋◇ (keep `η) zero     = zero
ren∋◇ (keep `η) (suc `𝒾) = suc (ren∋◇ `η `𝒾)


zip∋◇₁ : ∀ {X Y P Q A₁ n i} → {Ξ₁ : Vec X n} {Ξ₂ : Vec Y n} {𝒾 : Ξ₁ ∋⟨ i ⟩ A₁}
                               {ξ₁ : All P Ξ₁} {ξ₂ : All Q Ξ₂} {x₁ : P A₁}
                            → ξ₁ ∋◇⟨ 𝒾 ⟩ x₁
                            → zipAll ξ₁ ξ₂ ∋◇⟨ zip∋₁ 𝒾 ⟩ (x₁ , lookup ξ₂ (find Ξ₂ i))
zip∋◇₁ {ξ₁ = ξ₁ , x₁} {ξ₂ , x₂} zero     = zero
zip∋◇₁ {ξ₁ = ξ₁ , x₁} {ξ₂ , x₂} (suc `𝒾) = suc (zip∋◇₁ `𝒾)


zip∋◇₂ : ∀ {X Y P Q A₂ n i} → {Ξ₁ : Vec X n} {Ξ₂ : Vec Y n} {𝒾 : Ξ₂ ∋⟨ i ⟩ A₂}
                               {ξ₁ : All P Ξ₁} {ξ₂ : All Q Ξ₂} {x₂ : Q A₂}
                            → ξ₂ ∋◇⟨ 𝒾 ⟩ x₂
                            → zipAll ξ₁ ξ₂ ∋◇⟨ zip∋₂ 𝒾 ⟩ (lookup ξ₁ (find Ξ₁ i) , x₂)
zip∋◇₂ {ξ₁ = ξ₁ , x₁} {ξ₂ , x₂} zero     = zero
zip∋◇₂ {ξ₁ = ξ₁ , x₁} {ξ₂ , x₂} (suc `𝒾) = suc (zip∋◇₂ `𝒾)


--------------------------------------------------------------------------------


data All◇ {X P} (`P : ∀ {A : X} → P A → Set) : ∀ {n} → {Ξ : Vec X n}
                                                       → All P Ξ → Set
  where
    ∙ : All◇ `P ∙

    _,_ : ∀ {A n} → {Ξ : Vec X n}
                     {ξ : All P Ξ} {x : P A}
                  → All◇ `P ξ → `P x
                  → All◇ `P (ξ , x)


lookup◇ : ∀ {X P A n i} → {Ξ : Vec X n} {x : P A}
                           {ξ : All P Ξ} {𝒾 : Ξ ∋⟨ i ⟩ A}
                           {`P : ∀ {A} → P A → Set}
                        → All◇ `P ξ → ξ ∋◇⟨ 𝒾 ⟩ x
                        → `P x
lookup◇ (`ξ , `x) zero     = `x
lookup◇ (`ξ , `y) (suc `𝒾) = lookup◇ `ξ `𝒾


mapAll◇ : ∀ {X P n} → {Ξ : Vec X n} {Q : X → Set}
                       {f : ∀ {A} → P A → Q A} {ξ : All P Ξ}
                       {`P : ∀ {A} → P A → Set} {`Q : ∀ {A} → Q A → Set}
                    → (∀ {A} → {x : P A} → `P x → `Q (f x)) → All◇ `P ξ
                    → All◇ `Q (mapAll f ξ)
mapAll◇ `f ∙         = ∙
mapAll◇ `f (`ξ , `x) = mapAll◇ `f `ξ , `f `x


--------------------------------------------------------------------------------
