module BasicIPC.Metatheory.Gentzen-TarskiGentzen where

open import BasicIPC.Syntax.Gentzen public
open import BasicIPC.Semantics.TarskiGentzen public


-- Soundness with respect to the syntax representation in a particular model.

module _ {{_ : Model}} where
  reflect[] : ∀ {A Γ} → Γ ⊢ A → [ Γ ⊢ A ]
  reflect[] (var i)    = [var] i
  reflect[] (lam t)    = [lam] (reflect[] t)
  reflect[] (app t u)  = [app] (reflect[] t) (reflect[] u)
  reflect[] (pair t u) = [pair] (reflect[] t) (reflect[] u)
  reflect[] (fst t)    = [fst] (reflect[] t)
  reflect[] (snd t)    = [snd] (reflect[] t)
  reflect[] tt         = [tt]

  [multicut] : ∀ {Π A Γ} → [ Γ ⊢ Π ]⋆ → [ Π ⊢ A ] → [ Γ ⊢ A ]
  [multicut] {⌀}     ∙        u = mono[⊢] bot⊆ u
  [multicut] {Π , B} (ts , t) u = [app] ([multicut] ts ([lam] u)) t


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → ∀ᴹ⊨ Γ ⇒ A
eval (var i)    γ = lookup i γ
eval (lam t)    γ = λ η → mono[⊢] η ([multicut] (reify[]⋆ γ) (reflect[] (lam t))) , λ a →
                      eval t (mono⊨⋆ η γ , a)
eval (app t u)  γ = eval t γ ⟪$⟫ eval u γ
eval (pair t u) γ = eval t γ , eval u γ
eval (fst t)    γ = π₁ (eval t γ)
eval (snd t)    γ = π₂ (eval t γ)
eval tt         γ = ∙


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

instance
  canon : Model
  canon = record
    { _⊨ᵅ_    = λ Γ P → Γ ⊢ α P
    ; mono⊨ᵅ  = mono⊢
    ; [_⊢_]   = _⊢_
    ; mono[⊢] = mono⊢
    ; [var]    = var
    ; [lam]    = lam
    ; [app]    = app
    ; [pair]   = pair
    ; [fst]    = fst
    ; [snd]    = snd
    ; [tt]     = tt
    }


-- Soundness with respect to the canonical model.

reflect : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
reflect {α P}   t = t , t
reflect {A ▻ B} t = λ η → mono⊢ η t , λ a →
                      reflect {B} (app (mono⊢ η t) (reify[] {A} a))
reflect {A ∧ B} t = reflect {A} (fst t) , reflect {B} (snd t)
reflect {⊤}    t = ∙

reflect⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ⊨⋆ Π
reflect⋆ {⌀}     ∙        = ∙
reflect⋆ {Π , A} (ts , t) = reflect⋆ ts , reflect t


-- Reflexivity and transitivity.

refl⊨⋆ : ∀ {Γ} → Γ ⊨⋆ Γ
refl⊨⋆ = reflect⋆ refl⊢⋆

-- TODO: Transitivity.


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ} → ∀ᴹ⊨ Γ ⇒ A → Γ ⊢ A
quot t = reify[] (t refl⊨⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
