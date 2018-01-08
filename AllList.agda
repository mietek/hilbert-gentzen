module AllList where

open import Prelude
open import List


--------------------------------------------------------------------------------


data All {X} (P : X → Set) : List X → Set
  where
    ∙   : All P ∙
    _,_ : ∀ {Ξ A} → All P Ξ → P A → All P (Ξ , A)


maps : ∀ {X P Q} → {Ξ : List X}
                 → (∀ {A} → P A → Q A) → All P Ξ
                 → All Q Ξ
maps f ∙       = ∙
maps f (ξ , a) = maps f ξ , f a


module GetAllList
  where
    get : ∀ {X P A} → {Ξ : List X}
                    → All P Ξ → Ξ ∋ A
                    → P A
    get (ξ , a) zero    = a
    get (ξ , b) (suc 𝒾) = get ξ 𝒾


    gets : ∀ {X P} → {Ξ Ξ′ : List X}
                   → All P Ξ′ → Ξ′ ⊇ Ξ
                   → All P Ξ
    gets ξ       done     = ∙
    gets (ξ , b) (drop η) = gets ξ η
    gets (ξ , a) (keep η) = gets ξ η , a


--------------------------------------------------------------------------------


infix 4 _⊇′⟨_⟩_
data _⊇′⟨_⟩_ {X P} : {Ξ Ξ′ : List X} → All P Ξ′ → Ξ′ ⊇ Ξ → All P Ξ → Set
  where
    done : ∙ ⊇′⟨ done ⟩ ∙

    drop : ∀ {A Ξ Ξ′} → {η : Ξ′ ⊇ Ξ} {a : P A} {ξ : All P Ξ} {ξ′ : All P Ξ′}
                      → ξ′ ⊇′⟨ η ⟩ ξ
                      → ξ′ , a ⊇′⟨ drop η ⟩ ξ

    keep : ∀ {A Ξ Ξ′} → {η : Ξ′ ⊇ Ξ} {a : P A} {ξ : All P Ξ} {ξ′ : All P Ξ′}
                      → ξ′ ⊇′⟨ η ⟩ ξ
                      → ξ′ , a ⊇′⟨ keep η ⟩ ξ , a


id⊇′ : ∀ {X P} → {Ξ : List X} {ξ : All P Ξ}
               → ξ ⊇′⟨ id⊇ ⟩ ξ
id⊇′ {ξ = ∙}     = done
id⊇′ {ξ = ξ , a} = keep id⊇′


_∘⊇′_ : ∀ {X P} → {Ξ Ξ′ Ξ″ : List X} {η₁ : Ξ′ ⊇ Ξ} {η₂ : Ξ″ ⊇ Ξ′}
                   {ξ : All P Ξ} {ξ′ : All P Ξ′} {ξ″ : All P Ξ″}
                → ξ′ ⊇′⟨ η₁ ⟩ ξ → ξ″ ⊇′⟨ η₂ ⟩ ξ′
                → ξ″ ⊇′⟨ η₁ ∘⊇ η₂ ⟩ ξ
𝛈₁      ∘⊇′ done    = 𝛈₁
𝛈₁      ∘⊇′ drop 𝛈₂ = drop (𝛈₁ ∘⊇′ 𝛈₂)
drop 𝛈₁ ∘⊇′ keep 𝛈₂ = drop (𝛈₁ ∘⊇′ 𝛈₂)
keep 𝛈₁ ∘⊇′ keep 𝛈₂ = keep (𝛈₁ ∘⊇′ 𝛈₂)


--------------------------------------------------------------------------------


infix 4 _∋′⟨_⟩_
data _∋′⟨_⟩_ {X P} : ∀ {A} → {Ξ : List X} → All P Ξ → Ξ ∋ A → P A → Set
  where
    zero : ∀ {A Ξ} → {a : P A} {ξ : All P Ξ}
                   → ξ , a ∋′⟨ zero ⟩ a

    suc : ∀ {A B Ξ} → {𝒾 : Ξ ∋ A} {a : P A} {b : P B} {ξ : All P Ξ}
                    → ξ ∋′⟨ 𝒾 ⟩ a
                    → ξ , b ∋′⟨ suc 𝒾 ⟩ a


ren∋′ : ∀ {X P A} → {Ξ Ξ′ : List X} {η : Ξ′ ⊇ Ξ} {𝒾 : Ξ ∋ A}
                     {a : P A} {ξ : All P Ξ} {ξ′ : All P Ξ′}
                  → ξ′ ⊇′⟨ η ⟩ ξ → ξ ∋′⟨ 𝒾 ⟩ a
                  → ξ′ ∋′⟨ ren∋ η 𝒾 ⟩ a
ren∋′ done     𝓲       = 𝓲
ren∋′ (drop 𝛈) 𝓲       = suc (ren∋′ 𝛈 𝓲)
ren∋′ (keep 𝛈) zero    = zero
ren∋′ (keep 𝛈) (suc 𝓲) = suc (ren∋′ 𝛈 𝓲)


--------------------------------------------------------------------------------
