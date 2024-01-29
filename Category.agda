module Category where

open import Common hiding (_∘_ ; id)
import Function


----------------------------------------------------------------------------------------------------

record Category (ℴ 𝓇 : Level) : Set (ℓsuc (ℴ ⊔ 𝓇)) where
  field
    Obj  : Set ℴ
    _▻_  : ∀ (x y : Obj) → Set 𝓇
    id   : ∀ {x} → x ▻ x
    _∘_  : ∀ {x y z} (q : y ▻ z) (p : x ▻ y) → x ▻ z
    lid▻ : ∀ {x y} (p : y ▻ x) → id ∘ p ≡ p
    rid▻ : ∀ {x y} (p : y ▻ x) → p ∘ id ≡ p
    ass▻ : ∀ {w x y z} (r : y ▻ z) (q : x ▻ y) (p : w ▻ x) →
           r ∘ (q ∘ p) ≡ (r ∘ q) ∘ p

_ᵒᵖ : ∀ {ℴ 𝓇} (C : Category ℴ 𝓇) → Category ℴ 𝓇
_ᵒᵖ C = record
          { Obj  = C.Obj
          ; _▻_  = flip C._▻_
          ; id   = C.id
          ; _∘_  = flip C._∘_
          ; lid▻ = C.rid▻
          ; rid▻ = C.lid▻
          ; ass▻ = λ r q p → sym (C.ass▻ p q r)
          }
        where
          private
            module C = Category C

⟪Set⟫ : ∀ (𝓍 : Level) → Category (ℓsuc 𝓍) 𝓍
⟪Set⟫ 𝓍 = record
            { Obj  = Set 𝓍
            ; _▻_  = λ X Y → X → Y
            ; id   = Function.id
            ; _∘_  = λ q p → q Function.∘ p
            ; lid▻ = λ p → refl
            ; rid▻ = λ p → refl
            ; ass▻ = λ r q p → refl
            }

⟪Set₀⟫ : Category (ℓsuc ℓzero) ℓzero
⟪Set₀⟫ = ⟪Set⟫ ℓzero


----------------------------------------------------------------------------------------------------

record Functor {ℴ₁ ℴ₂ 𝓇₁ 𝓇₂} (C : Category ℴ₁ 𝓇₁) (D : Category ℴ₂ 𝓇₂) :
    Set (ℴ₁ ⊔ ℴ₂ ⊔ 𝓇₁ ⊔ 𝓇₂) where
  private
    module C = Category C
    module D = Category D

  field
    ƒObj : ∀ (x : C.Obj) → D.Obj
    ƒ    : ∀ {x y} (p : x C.▻ y) → (ƒObj x) D.▻ (ƒObj y)
    idƒ  : ∀ {x} → ƒ (C.id {x = x}) ≡ D.id
    _∘ƒ_ : ∀ {x y z} (q : y C.▻ z) (p : x C.▻ y) →
           ƒ (q C.∘ p) ≡ (ƒ q) D.∘ (ƒ p)

  op : Functor (C ᵒᵖ) (D ᵒᵖ)
  op = record
         { ƒObj = ƒObj
         ; ƒ    = ƒ
         ; idƒ  = idƒ
         ; _∘ƒ_ = flip _∘ƒ_
         }

⟪Id⟫ : ∀ {ℴ 𝓇} (C : Category ℴ 𝓇) → Functor C C
⟪Id⟫ C = record
           { ƒObj = Function.id
           ; ƒ    = Function.id
           ; idƒ  = refl
           ; _∘ƒ_ = λ q p → refl
           }

Presheaf : ∀ {ℴ 𝓇} (C : Category ℴ 𝓇) (𝓍 : Level) → Set (ℴ ⊔ 𝓇 ⊔ ℓsuc 𝓍)
Presheaf C 𝓍 = Functor (C ᵒᵖ) (⟪Set⟫ 𝓍)


----------------------------------------------------------------------------------------------------

record NatTrans {ℴ₁ ℴ₂ 𝓇₁ 𝓇₂} {C : Category ℴ₁ 𝓇₁} {D : Category ℴ₂ 𝓇₂} (F G : Functor C D) :
    Set (ℴ₁ ⊔ ℴ₂ ⊔ 𝓇₁ ⊔ 𝓇₂) where
  private
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G

  field
    η    : ∀ (x : C.Obj) → (F.ƒObj x) D.▻ (G.ƒObj x)
    natη : ∀ (x y : C.Obj) (p : x C.▻ y) →
           η y D.∘ F.ƒ p ≡ G.ƒ p D.∘ η x

  op : NatTrans G.op F.op
  op = record
         { η    = η
         ; natη = λ x y f → sym (natη y x f)
         }


----------------------------------------------------------------------------------------------------
