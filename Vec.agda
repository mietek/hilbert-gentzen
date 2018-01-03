module Vec where

open import Prelude
open import Fin


--------------------------------------------------------------------------------


data Vec (X : Set) : Nat → Set
  where
    ∙   : Vec X zero
    _,_ : ∀ {n} → Vec X n → X → Vec X (suc n)


get : ∀ {X n} → Vec X n → Fin n
              → X
get (Ξ , A) zero    = A
get (Ξ , B) (suc i) = get Ξ i


gets : ∀ {X n n′} → Vec X n′ → n′ ≥ n
                  → Vec X n
gets Ξ       done     = ∙
gets (Ξ , A) (drop e) = gets Ξ e
gets (Ξ , A) (keep e) = gets Ξ e , A


map : ∀ {X Y n} → (X → Y) → Vec X n
                → Vec Y n
map F ∙       = ∙
map F (Ξ , A) = map F Ξ , F A


zip : ∀ {X Y n} → Vec X n → Vec Y n
                → Vec (X × Y) n
zip ∙         ∙         = ∙
zip (Ξ₁ , A₁) (Ξ₂ , A₂) = zip Ξ₁ Ξ₂ , (A₁ , A₂)


--------------------------------------------------------------------------------


infix 4 _⊇⟨_⟩_
data _⊇⟨_⟩_ {X} : ∀ {n n′} → Vec X n′ → n′ ≥ n → Vec X n → Set
  where
    done : ∙ ⊇⟨ done ⟩ ∙

    drop : ∀ {A n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′}
                        → Ξ′ ⊇⟨ e ⟩ Ξ
                        → Ξ′ , A ⊇⟨ drop e ⟩ Ξ

    keep : ∀ {A n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′}
                        → Ξ′ ⊇⟨ e ⟩ Ξ
                        → Ξ′ , A ⊇⟨ keep e ⟩ Ξ , A


bot⊇ : ∀ {X n} → {Ξ : Vec X n}
               → Ξ ⊇⟨ bot≥ ⟩ ∙
bot⊇ {Ξ = ∙}     = done
bot⊇ {Ξ = Ξ , A} = drop bot⊇


id⊇ : ∀ {X n} → {Ξ : Vec X n}
              → Ξ ⊇⟨ id≥ ⟩ Ξ
id⊇ {Ξ = ∙}     = done
id⊇ {Ξ = Ξ , A} = keep id⊇


_∘⊇_ : ∀ {X n n′ n″ e₁ e₂} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {Ξ″ : Vec X n″}
                           → Ξ′ ⊇⟨ e₁ ⟩ Ξ → Ξ″ ⊇⟨ e₂ ⟩ Ξ′
                           → Ξ″ ⊇⟨ e₁ ∘≥ e₂ ⟩ Ξ
η₁      ∘⊇ done    = η₁
η₁      ∘⊇ drop η₂ = drop (η₁ ∘⊇ η₂)
drop η₁ ∘⊇ keep η₂ = drop (η₁ ∘⊇ η₂)
keep η₁ ∘⊇ keep η₂ = keep (η₁ ∘⊇ η₂)


--------------------------------------------------------------------------------


infix 4 _∋⟨_⟩_
data _∋⟨_⟩_ {X} : ∀ {n} → Vec X n → Fin n → X → Set
  where
    zero : ∀ {A n} → {Ξ : Vec X n}
                   → Ξ , A ∋⟨ zero ⟩ A

    suc : ∀ {B A n i} → {Ξ : Vec X n}
                      → Ξ ∋⟨ i ⟩ A
                      → Ξ , B ∋⟨ suc i ⟩ A


ren∋ : ∀ {X A n n′ e i} → {Ξ : Vec X n} {Ξ′ : Vec X n′}
                        → Ξ′ ⊇⟨ e ⟩ Ξ → Ξ ∋⟨ i ⟩ A
                        → Ξ′ ∋⟨ renF e i ⟩ A
ren∋ done     𝒾       = 𝒾
ren∋ (drop η) 𝒾       = suc (ren∋ η 𝒾)
ren∋ (keep η) zero    = zero
ren∋ (keep η) (suc 𝒾) = suc (ren∋ η 𝒾)


find : ∀ {X n} → (Ξ : Vec X n) (i : Fin n)
               → Ξ ∋⟨ i ⟩ get Ξ i
find (Ξ , A) zero    = zero
find (Ξ , B) (suc i) = suc (find Ξ i)


zip∋₁ : ∀ {X Y A₁ n i} → {Ξ₁ : Vec X n} {Ξ₂ : Vec Y n}
                       → Ξ₁ ∋⟨ i ⟩ A₁
                       → zip Ξ₁ Ξ₂ ∋⟨ i ⟩ (A₁ , get Ξ₂ i)
zip∋₁ {Ξ₁ = Ξ₁ , A₁} {Ξ₂ , A₂} zero    = zero
zip∋₁ {Ξ₁ = Ξ₁ , B₁} {Ξ₂ , B₂} (suc 𝒾) = suc (zip∋₁ 𝒾)


zip∋₂ : ∀ {X Y A₂ n i} → {Ξ₁ : Vec X n} {Ξ₂ : Vec Y n}
                       → Ξ₂ ∋⟨ i ⟩ A₂
                       → zip Ξ₁ Ξ₂ ∋⟨ i ⟩ (get Ξ₁ i , A₂)
zip∋₂ {Ξ₁ = Ξ₁ , A₁} {Ξ₂ , A₂} zero    = zero
zip∋₂ {Ξ₁ = Ξ₁ , B₁} {Ξ₂ , B₂} (suc 𝒾) = suc (zip∋₂ 𝒾)


--------------------------------------------------------------------------------


data All {X} (P : X → Set) : ∀ {n} → Vec X n → Set
  where
    ∙ : All P ∙

    _,_ : ∀ {n Ξ A} → All P {n} Ξ → P A
                    → All P (Ξ , A)


fromVec : ∀ {X P n} → (Ξ : Vec X n)
                    → (∀ A → P A)
                    → All P Ξ
fromVec ∙       p = ∙
fromVec (Ξ , A) p = fromVec Ξ p , p A

fromVec′ : ∀ {X n} → (Ξ : Vec X n)
                   → All (\ A → ⊤) Ξ
fromVec′ Ξ = fromVec Ξ (\ A → tt)

lookup : ∀ {X P A n i} → {Ξ : Vec X n}
                       → All P Ξ → Ξ ∋⟨ i ⟩ A
                       → P A
lookup (ξ , x) zero    = x
lookup (ξ , y) (suc 𝒾) = lookup ξ 𝒾

mapAll : ∀ {X P Q n} → {Ξ : Vec X n}
                     → (∀ {A} → P A → Q A) → All P Ξ
                     → All Q Ξ
mapAll f ∙       = ∙
mapAll f (ξ , x) = mapAll f ξ , f x

zipAll : ∀ {X Y P Q n} → {Ξ₁ : Vec X n} {Ξ₂ : Vec Y n}
                       → All P Ξ₁ → All Q Ξ₂
                       → All (\ { (A , B) → P A × Q B }) (zip Ξ₁ Ξ₂)
zipAll ∙         ∙         = ∙
zipAll (ξ₁ , x₁) (ξ₂ , x₂) = zipAll ξ₁ ξ₂ , (x₁ , x₂)


--------------------------------------------------------------------------------
