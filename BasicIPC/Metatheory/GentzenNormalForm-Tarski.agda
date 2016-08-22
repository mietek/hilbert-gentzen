module BasicIPC.Metatheory.GentzenNormalForm-Tarski where

open import BasicIPC.Syntax.GentzenNormalForm public
open import BasicIPC.Semantics.Tarski public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)           γ = lookup i γ
eval (lam t)           γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
eval (app {A} {B} t u) γ = _⟪$⟫_ {A} {B} (eval t γ) (eval u γ)
eval (pair t u)        γ = eval t γ , eval u γ
eval (fst t)           γ = π₁ (eval t γ)
eval (snd t)           γ = π₂ (eval t γ)
eval tt                γ = ∙

eval⋆ : ∀ {Ξ Γ} → Γ ⊢⋆ Ξ → Γ ⊨⋆ Ξ
eval⋆ {⌀}     ∙        γ = ∙
eval⋆ {Ξ , A} (ts , t) γ = eval⋆ ts γ , eval t γ


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { _⊩ᵅ_   = λ Γ P → Γ ⊢ⁿᵉ α P
      ; mono⊩ᵅ = mono⊢ⁿᵉ
      }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflectᶜ : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊩ A
  reflectᶜ {α P}   t = t
  reflectᶜ {A ▻ B} t = λ η a → reflectᶜ (appⁿᵉ (mono⊢ⁿᵉ η t) (reifyᶜ a))
  reflectᶜ {A ∧ B} t = reflectᶜ (fstⁿᵉ t) , reflectᶜ (sndⁿᵉ t)
  reflectᶜ {⊤}    t = ∙

  reifyᶜ : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ⁿᶠ A
  reifyᶜ {α P}   s       = neⁿᶠ s
  reifyᶜ {A ▻ B} s       = lamⁿᶠ (reifyᶜ (s weak⊆ (reflectᶜ {A} (varⁿᵉ top))))
  reifyᶜ {A ∧ B} (a , b) = pairⁿᶠ (reifyᶜ a) (reifyᶜ b)
  reifyᶜ {⊤}    s       = ttⁿᶠ

reflectᶜ⋆ : ∀ {Ξ Γ} → Γ ⊢⋆ⁿᵉ Ξ → Γ ⊩⋆ Ξ
reflectᶜ⋆ {⌀}     ∙        = ∙
reflectᶜ⋆ {Ξ , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t

reifyᶜ⋆ : ∀ {Ξ Γ} → Γ ⊩⋆ Ξ → Γ ⊢⋆ⁿᶠ Ξ
reifyᶜ⋆ {⌀}     ∙        = ∙
reifyᶜ⋆ {Ξ , A} (ts , t) = reifyᶜ⋆ ts , reifyᶜ t


-- Reflexivity and transitivity.

refl⊢⋆ⁿᵉ : ∀ {Γ} → Γ ⊢⋆ⁿᵉ Γ
refl⊢⋆ⁿᵉ {⌀}     = ∙
refl⊢⋆ⁿᵉ {Γ , A} = mono⊢⋆ⁿᵉ weak⊆ refl⊢⋆ⁿᵉ , varⁿᵉ top

refl⊩⋆ : ∀ {Γ} → Γ ⊩⋆ Γ
refl⊩⋆ = reflectᶜ⋆ refl⊢⋆ⁿᵉ

trans⊩⋆ : ∀ {Γ Γ′ Γ″} → Γ ⊩⋆ Γ′ → Γ′ ⊩⋆ Γ″ → Γ ⊩⋆ Γ″
trans⊩⋆ ts us = eval⋆ (trans⊢⋆ (nf→tm⋆ (reifyᶜ⋆ ts)) (nf→tm⋆ (reifyᶜ⋆ us))) refl⊩⋆


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ} → Γ ⊨ A → Γ ⊢ A
quot s = nf→tm (reifyᶜ (s refl⊩⋆))


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.