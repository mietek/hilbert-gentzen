module ICMLSemanticsNoTerms where

open import ICMLSyntaxNoTerms public


-- Introspective Kripke models.

record Model : Set₁ where
  field
    World  : Set
    _⊒_    : World → World → Set
    refl⊒  : ∀ {w} → w ⊒ w
    trans⊒ : ∀ {w w′ w″} → w″ ⊒ w′ → w′ ⊒ w → w″ ⊒ w
    _Я_    : World → World → Set
    reflЯ  : ∀ {w} → w Я w
    transЯ : ∀ {w w′ w″} → w″ Я w′ → w′ Я w → w″ Я w
    G      : World → Set
    monoG  : ∀ {w w′} → w′ ⊒ w → G w → G w′
    ⊒→Я   : ∀ {w w′} → w′ ⊒ w → w′ Я w
    peek   : World → Cx
    peek⊒₁ : ∀ {w w′} → w′ ⊒ w → π₁ (peek w′) ⊇ π₁ (peek w)
    peek⊒₂ : ∀ {w w′} → w′ ⊒ w → π₂ (peek w′) ⊇ π₂ (peek w)
open Model {{…}} public


-- Values.

mutual
  infix 3 _⊩_
  _⊩_ : ∀ {{_ : Model}} → World → Ty → Set
  w ⊩ A = ∀ {C w′} → w′ ⊒ w →
             (∀ {w″} → w″ ⊒ w′ → w″ ⊪ A → peek w″ ⊢ⁿᶠ C) →
             peek w′ ⊢ⁿᶠ C

  infix 3 _⊪_
  _⊪_ : ∀ {{_ : Model}} → World → Ty → Set
  w ⊪ •       = G w
  w ⊪ A ⇒ B  = ∀ {w′} → w′ ⊒ w → w′ ⊩ A → w′ ⊩ B
  w ⊪ [ Ψ ] A = ∀ {w′} → w′ Я w → π₁ (peek w′) ⁏ Ψ ⊢ A ∧ (∀ {w″} → w″ ⊒ w′ → w″ ⊩⋆ Ψ → w″ ⊩ A)

  infix 3 _⊩⋆_
  _⊩⋆_ : ∀ {{_ : Model}} → World → Ty⋆ → Set
  w ⊩⋆ ∅       = ⊤
  w ⊩⋆ (Ξ , A) = w ⊩⋆ Ξ ∧ w ⊩ A

infix 3 _⊩⧆_
_⊩⧆_ : ∀ {{_ : Model}} → World → BoxTy⋆ → Set
w ⊩⧆ ∅             = ⊤
w ⊩⧆ (Ξ , [ Ψ ] A) = w ⊩⧆ Ξ ∧ (π₁ (peek w) ⁏ Ψ ⊢ A ∧ (∀ {w′} → w′ ⊒ w → w′ ⊩⋆ Ψ → w′ ⊩ A))

mutual
  mono⊩ : ∀ {{_ : Model}} {A w w′} → w′ ⊒ w → w ⊩ A → w′ ⊩ A
  mono⊩ θ f = λ θ′ κ → f (trans⊒ θ′ θ) κ

  mono⊪ : ∀ {{_ : Model}} {A w w′} → w′ ⊒ w → w ⊪ A → w′ ⊪ A
  mono⊪ {•}       θ a = monoG θ a
  mono⊪ {A ⇒ B}  θ f = λ θ′ a → f (trans⊒ θ′ θ) a
  mono⊪ {[ Ψ ] A} θ q = λ ζ → q (transЯ ζ (⊒→Я θ))

mono⊩⋆ : ∀ {{_ : Model}} {w w′ Ξ} → w′ ⊒ w → w ⊩⋆ Ξ → w′ ⊩⋆ Ξ
mono⊩⋆ {Ξ = ∅}     θ ∅       = ∅
mono⊩⋆ {Ξ = Ξ , A} θ (ξ , a) = mono⊩⋆ θ ξ , mono⊩ {A} θ a

mono⊩⧆ : ∀ {{_ : Model}} {w w′ Ξ} → w′ ⊒ w → w ⊩⧆ Ξ → w′ ⊩⧆ Ξ
mono⊩⧆ {Ξ = ∅}           θ ∅       = ∅
mono⊩⧆ {Ξ = Ξ , [ Ψ ] A} θ (ξ , a) = mono⊩⧆ θ ξ , (mono⊢ (peek⊒₁ θ) refl⊇ (π₁ a) ,
                                       λ θ′ ψ → π₂ a (trans⊒ θ′ θ) ψ)

lookup⊩ : ∀ {{_ : Model}} {w Ξ A} → w ⊩⋆ Ξ → Ξ ∋ A → w ⊩ A
lookup⊩ (ξ , a) zero    = a
lookup⊩ (ξ , b) (suc 𝒾) = lookup⊩ ξ 𝒾


-- Continuations.

return : ∀ {{_ : Model}} {A w} → w ⊪ A → w ⊩ A
return {A} a = λ θ κ → κ refl⊒ (mono⊪ {A} θ a)

bind : ∀ {{_ : Model}} {A B w} → w ⊩ A →
         (∀ {w′} → w′ ⊒ w → w′ ⊪ A → w′ ⊩ B) →
         w ⊩ B
bind f κ = λ θ κ′ → f θ
             λ θ′ a → κ (trans⊒ θ′ θ) a refl⊒
               λ θ″ b → κ′ (trans⊒ θ″ θ′) b
