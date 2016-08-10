module BasicIPC.Hilbert.Tree.TarskiSoundness where

open import BasicIPC.Hilbert.Tree public
open import BasicIPC.TarskiSemantics public




module NaturalSoundness where
  open NaturalSemantics public


  -- Soundness with respect to all models, or evaluation.

  eval : ∀ {A} → ⊢ A → ᴹ⊨ A
  eval (app t u) = (eval t) (eval u)
  eval ci        = id
  eval ck        = const
  eval cs        = ap
  eval cpair     = _,_
  eval cfst      = π₁
  eval csnd      = π₂
  eval tt        = ∙


  -- Correctness of evaluation with respect to conversion.

  check : ∀ {{_ : Model}} {A} {t t′ : ⊢ A} → t ⇒ t′ → eval t ≡ eval t′
  check refl⇒           = refl
  check (trans⇒ p q)    = trans (check p) (check q)
  check (sym⇒ p)        = sym (check p)
  check (congapp⇒ p q)  = cong₂ _$_ (check p) (check q)
  check (congpair⇒ p q) = cong₂ _,_ (check p) (check q)
  check (congfst⇒ p)    = cong π₁ (check p)
  check (congsnd⇒ p)    = cong π₂ (check p)
  check beta▻ₖ⇒         = refl
  check beta▻ₛ⇒         = refl
  check beta∧₁⇒         = refl
  check beta∧₂⇒         = refl
  check eta∧⇒           = refl
  check eta⊤⇒          = refl




-- Using satisfaction with a syntactic component, inspired by Coquand and Dybjer.

module CoquandDybjerSoundness where
  open CoquandDybjerSemantics (⊢_) public


  -- Completeness with respect to a particular model.

  reify : ∀ {{_ : Model}} {A} → ⊨ A → ⊢ A
  reify {α P}   (t , s) = t
  reify {A ▻ B} (t , f) = t
  reify {A ∧ B} (a , b) = pair (reify {A} a) (reify {B} b)
  reify {⊤}    ∙       = tt


  -- Soundness with respect to all models, or evaluation.

  eval : ∀ {A} → ⊢ A → ᴹ⊨ A
  eval (app t u) = (eval t) $ˢ (eval u)
  eval ci        = ci , id
  eval ck        = ck , (λ a → app ck (reify a) , const a)
  eval cs        = cs , (λ f →
                     app cs (reify f) , (λ g →
                       app (app cs (reify f)) (reify g) , (λ a →
                         (f $ˢ a) $ˢ (g $ˢ a))))
  eval cpair     = cpair , (λ a → app cpair (reify a) , (λ b → a , b))
  eval cfst      = cfst , π₁
  eval csnd      = csnd , π₂
  eval tt        = ∙


  -- Correctness of evaluation with respect to conversion.

  check : ∀ {{_ : Model}} {A} {t t′ : ⊢ A} → t ⇒ t′ → eval t ≡ eval t′
  check refl⇒           = refl
  check (trans⇒ p q)    = trans (check p) (check q)
  check (sym⇒ p)        = sym (check p)
  check (congapp⇒ p q)  = cong₂ _$ˢ_ (check p) (check q)
  check (congpair⇒ p q) = cong₂ _,_ (check p) (check q)
  check (congfst⇒ p)    = cong π₁ (check p)
  check (congsnd⇒ p)    = cong π₂ (check p)
  check beta▻ₖ⇒         = refl
  check beta▻ₛ⇒         = refl
  check beta∧₁⇒         = refl
  check beta∧₂⇒         = refl
  check eta∧⇒           = refl
  check eta⊤⇒          = refl
