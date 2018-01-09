module AllVec where

open import Prelude
open import Vec


--------------------------------------------------------------------------------


data All {X} (P : X → Set) : ∀ {n} → Vec X n → Set
  where
    ∙   : All P ∙
    _,_ : ∀ {n Ξ A} → All P {n} Ξ → P A → All P (Ξ , A)


maps : ∀ {X P Q n} → {Ξ : Vec X n}
                   → (∀ {A} → P A → Q A) → All P Ξ
                   → All Q Ξ
maps f ∙       = ∙
maps f (ξ , a) = maps f ξ , f a


--------------------------------------------------------------------------------


get : ∀ {X P A n i} → {Ξ : Vec X n}
                    → All P Ξ → Ξ ∋⟨ i ⟩ A
                    → P A
get (ξ , a) zero    = a
get (ξ , b) (suc 𝒾) = get ξ 𝒾


gets : ∀ {X P n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′}
                      → All P Ξ′ → Ξ′ ⊇⟨ e ⟩ Ξ
                      → All P Ξ
gets ξ       done     = ∙
gets (ξ , b) (drop η) = gets ξ η
gets (ξ , a) (keep η) = gets ξ η , a


--------------------------------------------------------------------------------


infix 4 _⊇◇⟨_⟩_
data _⊇◇⟨_⟩_ {X P} : ∀ {n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′}
                                → All P Ξ′ → Ξ′ ⊇⟨ e ⟩ Ξ → All P Ξ → Set
  where
    done : ∙ ⊇◇⟨ done ⟩ ∙

    drop : ∀ {A n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {η : Ξ′ ⊇⟨ e ⟩ Ξ}
                           {a : P A} {ξ : All P Ξ} {ξ′ : All P Ξ′}
                        → ξ′ ⊇◇⟨ η ⟩ ξ
                        → ξ′ , a ⊇◇⟨ drop η ⟩ ξ

    keep : ∀ {A n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {η : Ξ′ ⊇⟨ e ⟩ Ξ}
                           {a : P A} {ξ : All P Ξ} {ξ′ : All P Ξ′}
                        → ξ′ ⊇◇⟨ η ⟩ ξ
                        → ξ′ , a ⊇◇⟨ keep η ⟩ ξ , a


id⊇◇ : ∀ {X P n} → {Ξ : Vec X n} {ξ : All P Ξ}
                 → ξ ⊇◇⟨ id⊇ ⟩ ξ
id⊇◇ {ξ = ∙}     = done
id⊇◇ {ξ = ξ , a} = keep id⊇◇


_∘⊇◇_ : ∀ {X P n n′ n″ e₁ e₂} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {Ξ″ : Vec X n″}
                                 {η₁ : Ξ′ ⊇⟨ e₁ ⟩ Ξ} {η₂ : Ξ″ ⊇⟨ e₂ ⟩ Ξ′}
                                 {ξ : All P Ξ} {ξ′ : All P Ξ′} {ξ″ : All P Ξ″}
                              → ξ′ ⊇◇⟨ η₁ ⟩ ξ → ξ″ ⊇◇⟨ η₂ ⟩ ξ′
                              → ξ″ ⊇◇⟨ η₁ ∘⊇ η₂ ⟩ ξ
𝛈₁      ∘⊇◇ done    = 𝛈₁
𝛈₁      ∘⊇◇ drop 𝛈₂ = drop (𝛈₁ ∘⊇◇ 𝛈₂)
drop 𝛈₁ ∘⊇◇ keep 𝛈₂ = drop (𝛈₁ ∘⊇◇ 𝛈₂)
keep 𝛈₁ ∘⊇◇ keep 𝛈₂ = keep (𝛈₁ ∘⊇◇ 𝛈₂)


--------------------------------------------------------------------------------


infix 4 _∋◇⟨_⟩_
data _∋◇⟨_⟩_ {X P} : ∀ {A n i} → {Ξ : Vec X n}
                               → All P Ξ → Ξ ∋⟨ i ⟩ A → P A → Set
  where
    zero : ∀ {A n} → {Ξ : Vec X n} {ξ : All P Ξ} {a : P A}
                   → ξ , a ∋◇⟨ zero ⟩ a

    suc : ∀ {B n i A} → {Ξ : Vec X n} {𝒾 : Ξ ∋⟨ i ⟩ A}
                         {a : P A} {b : P B} {ξ : All P Ξ}
                      → ξ ∋◇⟨ 𝒾 ⟩ a
                      → ξ , b ∋◇⟨ suc 𝒾 ⟩ a


ren∋◇ : ∀ {X P A n n′ e i} → {Ξ : Vec X n} {Ξ′ : Vec X n′}
                              {η : Ξ′ ⊇⟨ e ⟩ Ξ} {𝒾 : Ξ ∋⟨ i ⟩ A}
                              {a : P A} {ξ : All P Ξ} {ξ′ : All P Ξ′}
                           → ξ′ ⊇◇⟨ η ⟩ ξ → ξ ∋◇⟨ 𝒾 ⟩ a
                           → ξ′ ∋◇⟨ ren∋ η 𝒾 ⟩ a
ren∋◇ done     𝓲       = 𝓲
ren∋◇ (drop 𝛈) 𝓲       = suc (ren∋◇ 𝛈 𝓲)
ren∋◇ (keep 𝛈) zero    = zero
ren∋◇ (keep 𝛈) (suc 𝓲) = suc (ren∋◇ 𝛈 𝓲)


--------------------------------------------------------------------------------
