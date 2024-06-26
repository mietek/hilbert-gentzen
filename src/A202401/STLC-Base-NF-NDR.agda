----------------------------------------------------------------------------------------------------

-- non-deterministic reduction to β-short normal form

module A202401.STLC-Base-NF-NDR where

open import A202401.STLC-Base-RenSub public
open import A202401.STLC-Base-NF public
open import A202401.Kit3 public


----------------------------------------------------------------------------------------------------

infix 4 _⇒_
data _⇒_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
  congλ  : ∀ {A B} {t t′ : Γ , A ⊢ B} (r : t ⇒ t′) → ⌜λ⌝ t ⇒ ⌜λ⌝ t′
  cong$₁ : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (r₁ : t₁ ⇒ t₁′) →
           t₁ ⌜$⌝ t₂ ⇒ t₁′ ⌜$⌝ t₂
  cong$₂ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (r₂ : t₂ ⇒ t₂′) →
           t₁ ⌜$⌝ t₂ ⇒ t₁ ⌜$⌝ t₂′
  βred⊃  : ∀ {A B} {t₁ : Γ , A ⊢ B} {t₂ : Γ ⊢ A} {t′} (eq : t′ ≡ t₁ [ t₂ ]) →
           ⌜λ⌝ t₁ ⌜$⌝ t₂ ⇒ t′

open RedKit1 (kit tmkit _⇒_) public

mutual
  NF→¬R : ∀ {Γ A} {t : Γ ⊢ A} → NF t → ¬R t
  NF→¬R (⌜λ⌝ p) (congλ r) = r ↯ NF→¬R p
  NF→¬R (nnf p) r         = r ↯ NNF→¬R p

  NNF→¬R : ∀ {Γ A} {t  : Γ ⊢ A} → NNF t → ¬R t
  NNF→¬R (p₁ ⌜$⌝ p₂) (cong$₁ r₁) = r₁ ↯ NNF→¬R p₁
  NNF→¬R (p₁ ⌜$⌝ p₂) (cong$₂ r₂) = r₂ ↯ NF→¬R p₂

open RedKit2 (kit redkit1 uniNF NF→¬R) public


----------------------------------------------------------------------------------------------------

prog⇒ : ∀ {Γ A} (t : Γ ⊢ A) → Prog t
prog⇒ (var i)                = done (nnf var-)
prog⇒ (⌜λ⌝ t)                with prog⇒ t
... | step r                    = step (congλ r)
... | done p                    = done (⌜λ⌝ p)
prog⇒ (t₁ ⌜$⌝ t₂)            with prog⇒ t₁ | prog⇒ t₂
... | step r₁       | _         = step (cong$₁ r₁)
... | done p₁       | step r₂   = step (cong$₂ r₂)
... | done (⌜λ⌝ p₁) | done p₂   = step (βred⊃ refl)
... | done (nnf p₁) | done p₂   = done (nnf (p₁ ⌜$⌝ p₂))

open ProgKit (kit redkit2 prog⇒) public


----------------------------------------------------------------------------------------------------

ren⇒ : ∀ {Γ Γ′ A} {t t′ : Γ ⊢ A} (ϱ : Γ ⊑ Γ′) → t ⇒ t′ → ren ϱ t ⇒ ren ϱ t′
ren⇒ ϱ (congλ r)              = congλ (ren⇒ (lift⊑ ϱ) r)
ren⇒ ϱ (cong$₁ r₁)            = cong$₁ (ren⇒ ϱ r₁)
ren⇒ ϱ (cong$₂ r₂)            = cong$₂ (ren⇒ ϱ r₂)
ren⇒ ϱ (βred⊃ {t₁ = t₁} refl) = βred⊃ (rencut ϱ t₁ _ ⁻¹)

sub⇒ : ∀ {Γ Ξ A} (σ : Ξ ⊢§ Γ) {t t′ : Γ ⊢ A} → t ⇒ t′ → sub σ t ⇒ sub σ t′
sub⇒ σ (congλ r)              = congλ (sub⇒ (lift§ σ) r)
sub⇒ σ (cong$₁ r₁)            = cong$₁ (sub⇒ σ r₁)
sub⇒ σ (cong$₂ r₂)            = cong$₂ (sub⇒ σ r₂)
sub⇒ σ (βred⊃ {t₁ = t₁} refl) = βred⊃ (subcut σ t₁ _ ⁻¹)


----------------------------------------------------------------------------------------------------
