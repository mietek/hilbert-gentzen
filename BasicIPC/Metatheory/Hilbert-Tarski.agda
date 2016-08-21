module BasicIPC.Metatheory.Hilbert-Tarski where

open import BasicIPC.Syntax.Hilbert public
open import BasicIPC.Semantics.Tarski public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)   γ = lookup i γ
eval (app t u) γ = eval t γ $ eval u γ
eval ci        γ = id
eval ck        γ = const
eval cs        γ = ap
eval cpair     γ = _,_
eval cfst      γ = π₁
eval csnd      γ = π₂
eval tt        γ = ∙


-- Correctness of evaluation with respect to conversion.

eval✓ : ∀ {{_ : Model}} {A Γ} {t t′ : Γ ⊢ A} → t ⋙ t′ → eval t ≡ eval t′
eval✓ refl⋙                      = refl
eval✓ (trans⋙ p q)               = trans (eval✓ p) (eval✓ q)
eval✓ (sym⋙ p)                   = sym (eval✓ p)
eval✓ (congapp⋙ {A} {B} p q)     = cong₂ (_⟦$⟧_ {A} {B}) (eval✓ p) (eval✓ q)
eval✓ (congi⋙ p)                 = cong id (eval✓ p)
eval✓ (congk⋙ p q)               = cong₂ const (eval✓ p) (eval✓ q)
eval✓ (congs⋙ {A} {B} {C} p q r) = cong₃ (⟦ap⟧ {A} {B} {C}) (eval✓ p) (eval✓ q) (eval✓ r)
eval✓ (congpair⋙ {A} {B} p q)    = cong₂ (_⟦,⟧_ {A} {B}) (eval✓ p) (eval✓ q)
eval✓ (congfst⋙ {A} {B} p)       = cong (⟦π₁⟧ {A} {B}) (eval✓ p)
eval✓ (congsnd⋙ {A} {B} p)       = cong (⟦π₂⟧ {A} {B}) (eval✓ p)
eval✓ beta▻ₖ⋙                    = refl
eval✓ beta▻ₛ⋙                    = refl
eval✓ beta∧₁⋙                    = refl
eval✓ beta∧₂⋙                    = refl
eval✓ eta∧⋙                      = refl
eval✓ eta⊤⋙                     = refl
