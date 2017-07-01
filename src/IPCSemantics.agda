module IPCSemantics where

open import IPC public


-- Intuitionistic Kripke models.

record Model : Set₁ where
  field
    World  : Set
    _⊒_    : World → World → Set
    refl⊒  : ∀ {w} → w ⊒ w
    trans⊒ : ∀ {w w′ w″} → w″ ⊒ w′ → w′ ⊒ w → w″ ⊒ w
    G      : World → Set
    monoG  : ∀ {w w′} → w′ ⊒ w → G w → G w′
open Model {{…}} public


-- Values.

infix 3 _⊩_
_⊩_ : ∀ {{_ : Model}} → World → Ty → Set
w ⊩ •      = G w
w ⊩ A ⇒ B = ∀ {w′} → w′ ⊒ w → w′ ⊩ A → w′ ⊩ B

mono⊩ : ∀ {{_ : Model}} {A w w′} → w′ ⊒ w → w ⊩ A → w′ ⊩ A
mono⊩ {•}      η a = monoG η a
mono⊩ {A ⇒ B} η f = λ η′ a → f (trans⊒ η′ η) a


-- Lists of values.

module IPCSemanticsList where
  open IPCList public

  infix 3 _⊩⋆_
  _⊩⋆_ : ∀ {{_ : Model}} → World → Ty⋆ → Set
  w ⊩⋆ Ξ = All (w ⊩_) Ξ

  mono⊩⋆ : ∀ {{_ : Model}} {w w′ Ξ} → w′ ⊒ w → w ⊩⋆ Ξ → w′ ⊩⋆ Ξ
  mono⊩⋆ η ξ = mapAll (λ {A} → mono⊩ {A} η) ξ

  lookup⊩ : ∀ {{_ : Model}} {w Ξ A} → w ⊩⋆ Ξ → Ξ ∋ A → w ⊩ A
  lookup⊩ ξ 𝒾 = lookupAll ξ 𝒾


-- Vectors of values.

module IPCSemanticsVec where
  open IPCVec public

  infix 3 _⊩⋆_
  _⊩⋆_ : ∀ {{_ : Model}} {n} → World → Ty⋆ n → Set
  w ⊩⋆ Ξ = All (w ⊩_) Ξ

  mono⊩⋆ : ∀ {{_ : Model}} {w w′ n} {Ξ : Ty⋆ n} →
              w′ ⊒ w → w ⊩⋆ Ξ → w′ ⊩⋆ Ξ
  mono⊩⋆ η ξ = mapAll (λ {A} → mono⊩ {A} η) ξ

  lookup⊩ : ∀ {{_ : Model}} {w n} {Ξ : Ty⋆ n} {A i} →
               w ⊩⋆ Ξ → Ξ ∋⟨ i ⟩ A → w ⊩ A
  lookup⊩ ξ 𝒾 = lookupAll ξ 𝒾
