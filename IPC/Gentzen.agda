module IPC.Gentzen where

open import IPC.Core public


-- Proofs of IPC, as Gentzen-style natural deduction trees.

infix 1 _⊢_
data _⊢_ (Γ : Cx Ty) : Ty → Set where
  var  : ∀ {A}     → A ∈ Γ → Γ ⊢ A
  lam  : ∀ {A B}   → Γ , A ⊢ B → Γ ⊢ A ⇒ B
  app  : ∀ {A B}   → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  pair : ∀ {A B}   → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ∧ B
  fst  : ∀ {A B}   → Γ ⊢ A ∧ B → Γ ⊢ A
  snd  : ∀ {A B}   → Γ ⊢ A ∧ B → Γ ⊢ B
  inl  : ∀ {A B}   → Γ ⊢ A → Γ ⊢ A ∨ B
  inr  : ∀ {A B}   → Γ ⊢ B → Γ ⊢ A ∨ B
  case : ∀ {A B C} → Γ ⊢ A ∨ B → Γ , A ⊢ C → Γ , B ⊢ C → Γ ⊢ C
  boom : ∀ {C}     → Γ ⊢ ⊥ → Γ ⊢ C


-- Monotonicity of syntactic consequence.

mono⊢ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A
mono⊢ η (var i)      = var (mono∈ η i)
mono⊢ η (lam t)      = lam (mono⊢ (keep η) t)
mono⊢ η (app t u)    = app (mono⊢ η t) (mono⊢ η u)
mono⊢ η (pair t u)   = pair (mono⊢ η t) (mono⊢ η u)
mono⊢ η (fst t)      = fst (mono⊢ η t)
mono⊢ η (snd t)      = snd (mono⊢ η t)
mono⊢ η (inl t)      = inl (mono⊢ η t)
mono⊢ η (inr t)      = inr (mono⊢ η t)
mono⊢ η (case t u v) = case (mono⊢ η t) (mono⊢ (keep η) u) (mono⊢ (keep η) v)
mono⊢ η (boom t)     = boom (mono⊢ η t)


-- Shorthand for variables.

v₀ : ∀ {A Γ} → Γ , A ⊢ A
v₀ = var top

v₁ : ∀ {A B Γ} → Γ , A , B ⊢ A
v₁ = var (pop top)

v₂ : ∀ {A B C Γ} → Γ , A , B , C ⊢ A
v₂ = var (pop (pop top))


-- Deduction theorem.

ded : ∀ {A B Γ} → Γ , A ⊢ B → Γ ⊢ A ⇒ B
ded t = lam t


-- Useful theorems in combinatory form.

ci : ∀ {A Γ} → Γ ⊢ A ⇒ A
ci = lam v₀

ck : ∀ {A B Γ} → Γ ⊢ A ⇒ B ⇒ A
ck = lam (lam v₁)

cs : ∀ {A B C Γ} → Γ ⊢ (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C
cs = lam (lam (lam (app (app v₂ v₀) (app v₁ v₀))))

cpair : ∀ {A B Γ} → Γ ⊢ A ⇒ B ⇒ A ∧ B
cpair = lam (lam (pair v₁ v₀))

cfst : ∀ {A B Γ} → Γ ⊢ A ∧ B ⇒ A
cfst = lam (fst v₀)

csnd : ∀ {A B Γ} → Γ ⊢ A ∧ B ⇒ B
csnd = lam (snd v₀)

cinl : ∀ {A B Γ} → Γ ⊢ A ⇒ A ∨ B
cinl = lam (inl v₀)

cinr : ∀ {A B Γ} → Γ ⊢ B ⇒ A ∨ B
cinr = lam (inr v₀)

ccase : ∀ {A B C Γ} → Γ ⊢ A ∨ B ⇒ (A ⇒ C) ⇒ (B ⇒ C) ⇒ C
ccase = lam (lam (lam (case v₂ (app v₂ v₀) (app v₁ v₀))))

cboom : ∀ {C Γ} → Γ ⊢ ⊥ ⇒ C
cboom = lam (boom v₀)