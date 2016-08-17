module BasicIS4.Metatheory.DyadicHilbert-TarskiDyadicGabbayNanevski where

open import BasicIS4.Syntax.DyadicHilbert public
open import BasicIS4.Semantics.TarskiDyadicGabbayNanevski public

open SyntacticComponent (_⁏_⊢_) (_⁏_⊢⋆_) (mono⊢) (mmono⊢) public


-- Completeness with respect to a particular model.

module _ {{_ : Model}} where
  reify : ∀ {A Γ Δ} → Γ ⁏ Δ ⊨ A → Γ ⁏ Δ ⊢ A
  reify {α P}   (t , s) = t
  reify {A ▻ B} s       = let t , f = s refl⊆ refl⊆ in t
  reify {□ A}   s       = let t , a = s refl⊆ refl⊆ in mono⊢ bot⊆ (box t)
  reify {A ∧ B} (a , b) = pair (reify a) (reify b)
  reify {⊤}    ∙       = tt

  reify⋆ : ∀ {Π Γ Δ} → Γ ⁏ Δ ⊨⋆ Π → Γ ⁏ Δ ⊢⋆ Π
  reify⋆ {⌀}     ∙        = ∙
  reify⋆ {Π , A} (ts , t) = reify⋆ ts , reify t


-- Additional useful equipment.

module _ {{_ : Model}} where
  ⟪const⟫ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊨ A → Γ ⁏ Δ ⊨ B ▻ A
  ⟪const⟫ {A} a η θ = let a′ = mono²⊨ {A} (η , θ) a
                      in  app ck (reify a′) , const a′

  ⟪ap⟫′ : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊨ A ▻ B ▻ C → Γ ⁏ Δ ⊨ (A ▻ B) ▻ A ▻ C
  ⟪ap⟫′ {A} {B} {C} s₁ η θ = let s₁′   = mono²⊨ {A ▻ B ▻ C} (η , θ) s₁
                                 t , _ = s₁′ refl⊆ refl⊆
                             in  app cs t , λ s₂ η′ θ′ →
                                   let s₁″    = mono²⊨ {A ▻ B ▻ C} (trans⊆ η η′ , trans⊆ θ θ′) s₁
                                       t′ , _ = s₁″ refl⊆ refl⊆
                                       s₂′    = mono²⊨ {A ▻ B} (η′ , θ′) s₂
                                       u  , g = s₂′ refl⊆ refl⊆
                                   in  app (app cs t′) u , ⟪ap⟫ s₁″ s₂′

  _⟪◎⟫_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊨ □ (A ▻ B) → Γ ⁏ Δ ⊨ □ A → Γ ⁏ Δ ⊨ □ B
  (s₁ ⟪◎⟫ s₂) η θ = let t , f = s₁ η θ
                        u , a = s₂ η θ
                    in  app t u , f ⟪$⟫ a

  -- TODO: Report bug.
  _⟪◎⟫′_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊨ □ (A ▻ B) → Γ ⁏ Δ ⊨ □ A ▻ □ B
  _⟪◎⟫′_ {A} {B} s η θ = let s′ = mono²⊨ {□ (A ▻ B)} (η , θ) s
                         in  app cdist (reify (λ {Γ′} {Δ′} η′ θ′ → s′ η′ θ′)) , _⟪◎⟫_ s′

  ⟪⇑⟫ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊨ □ A → Γ ⁏ Δ ⊨ □ □ A
  ⟪⇑⟫ {A} s η θ = let t , a = s η θ
                  in  box t , λ η′ θ′ → s (trans⊆ η η′) (trans⊆ θ θ′)

  _⟪,⟫′_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊨ A → Γ ⁏ Δ ⊨ B ▻ A ∧ B
  _⟪,⟫′_ {A} a η θ = let a′ = mono²⊨ {A} (η , θ) a
                     in  app cpair (reify a′) , _,_ a′


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → ∀ᴹ⊨ Γ ⁏ Δ ⇒ A
eval (var i)      γ δ = lookup i γ
eval (app t u)    γ δ = eval t γ δ ⟪$⟫ eval u γ δ
eval ci           γ δ = const₂ (ci , id)
eval ck           γ δ = const₂ (ck , ⟪const⟫)
eval cs           γ δ = const₂ (cs , ⟪ap⟫′)
eval (mvar {A} i) γ δ = mono⊨ {A} bot⊆ (mlookup i δ)
eval (box t)      γ δ = λ η θ → multicut (reify⋆ (mmono⊨⋆ θ δ)) (msplit (mmono⊢ weak⊆⧺ᵣ t)) ,
                          eval t ∙ (mmono⊨⋆ θ δ)
eval cdist        γ δ = const₂ (cdist , _⟪◎⟫′_)
eval cup          γ δ = const₂ (cup , ⟪⇑⟫)
eval cdown        γ δ = const₂ (cdown , ⟪⇓⟫)
eval cpair        γ δ = const₂ (cpair , _⟪,⟫′_)
eval cfst         γ δ = const₂ (cfst , π₁)
eval csnd         γ δ = const₂ (csnd , π₂)
eval tt           γ δ = ∙


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

instance
  canon : Model
  canon = record
    { _⁏_⊨ᵅ_  = λ Γ Δ P → Γ ⁏ Δ ⊢ α P
    ; mono⊨ᵅ  = mono⊢
    ; mmono⊨ᵅ = mmono⊢
    }


-- Soundness with respect to the canonical model.

-- FIXME: The semantics must be wrong...
postulate
  oops : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → ⌀ ⁏ Δ ⊢ A

reflect : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
reflect {α P}   t = t , t
reflect {A ▻ B} t = λ η θ → mono²⊢ (η , θ) t , λ a → reflect (app (mono²⊢ (η , θ) t) (reify a))
reflect {□ A}   t = λ η θ → oops (down (mmono⊢ θ t)) , reflect (mono²⊢ (η , θ) (down t))
reflect {A ∧ B} t = reflect (fst t) , reflect (snd t)
reflect {⊤}    t = ∙

reflect⋆ : ∀ {Π Γ Δ} → Γ ⁏ Δ ⊢⋆ Π → Γ ⁏ Δ ⊨⋆ Π
reflect⋆ {⌀}     ∙        = ∙
reflect⋆ {Π , A} (ts , t) = reflect⋆ ts , reflect t


-- Reflexivity and transitivity.

lose : ∀ {Π′ Π Γ Δ} → Γ ⁏ Δ ⊢⋆ Π ⧺ Π′ → Γ ⁏ Δ ⊢⋆ Π
lose {⌀}      ts       = ts
lose {Π′ , A} (ts , t) = lose {Π′} ts

refl⊢⋆′ : ∀ {Δ Γ} → Γ ⁏ Δ ⊢⋆ Γ
refl⊢⋆′ {Δ} = lose {□⋆ Δ} refl⊢⋆

mrefl⊢⋆′ : ∀ {Δ} → ⌀ ⁏ Δ ⊢⋆ □⋆ Δ
mrefl⊢⋆′ {Δ} = subst (λ Π → ⌀ ⁏ Δ ⊢⋆ Π) (id⧺ᵣ {Γ = □⋆ Δ}) refl⊢⋆

refl⊨⋆ : ∀ {Δ Γ} → Γ ⁏ Δ ⊨⋆ Γ
refl⊨⋆ = reflect⋆ refl⊢⋆′

mrefl⊨⋆ : ∀ {Δ} → ⌀ ⁏ Δ ⊨⋆ □⋆ Δ
mrefl⊨⋆ = reflect⋆ mrefl⊢⋆′

-- TODO: Transitivity.


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ Δ} → ∀ᴹ⊨ Γ ⁏ Δ ⇒ A → Γ ⁏ Δ ⊢ A
quot t = reify (t refl⊨⋆ mrefl⊨⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
