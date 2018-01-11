module List2 where

open import Prelude
open import Category
open import List
open import ListLemmas


--------------------------------------------------------------------------------


infix 5 _⨾_
pattern _⨾_ Δ Γ = _,_ Δ Γ


List² : Set → Set → Set
List² X Y = List X × List Y


--------------------------------------------------------------------------------


infix 4 _⊇²_
_⊇²_ : ∀ {X Y} → List² X Y → List² X Y → Set
Δ′ ⨾ Γ′ ⊇² Δ ⨾ Γ = Δ′ ⊇ Δ × Γ′ ⊇ Γ


drop₁ : ∀ {X Y A} → {Δ Δ′ : List X} {Γ Γ′ : List Y}
                  → Δ′ ⨾ Γ′ ⊇² Δ ⨾ Γ
                  → Δ′ , A ⨾ Γ′ ⊇² Δ ⨾ Γ
drop₁ η = drop (proj₁ η) , proj₂ η


drop₂ : ∀ {X Y A} → {Δ Δ′ : List X} {Γ Γ′ : List Y}
                  → Δ′ ⨾ Γ′ ⊇² Δ ⨾ Γ
                  → Δ′ ⨾ Γ′ , A ⊇² Δ ⨾ Γ
drop₂ η = proj₁ η , drop (proj₂ η)


--------------------------------------------------------------------------------


instance
  𝐎𝐏𝐄² : ∀ {X Y} → Category (List² X Y) _⊇²_
  𝐎𝐏𝐄² = Product 𝐎𝐏𝐄 𝐎𝐏𝐄


--------------------------------------------------------------------------------
