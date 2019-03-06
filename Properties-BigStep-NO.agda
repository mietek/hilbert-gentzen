---------------------------------------------------------------------------------------------------------------
--
-- Properties of BS-NO

module Properties-BigStep-NO where

open import Semantics-BigStep
open NO public
import Properties-BigStep-CBN as BS-CBN


---------------------------------------------------------------------------------------------------------------
--
-- BS-NO goes to NF

na←naxnf-cbn-⇓ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e CBN.⇓ e′ → NA e′
na←naxnf-cbn-⇓ var      CBN.var           = var
na←naxnf-cbn-⇓ (app p₁) (CBN.applam r₁ r) = case p₁′ of λ ()
  where
    p₁′ = naxnf←whnf (BS-CBN.whnf-⇓ r₁) (na←naxnf-cbn-⇓ p₁ r₁)
na←naxnf-cbn-⇓ (app p₁) (CBN.app r₁ q₁)   = app

na←naxnf-⇓ : ∀ {n} {e : Tm n} {e′} → NAXNF e → e ⇓ e′ → NA e′
na←naxnf-⇓ var      var                = var
na←naxnf-⇓ (app p₁) (applam r₁ r)      = case (na←naxnf-cbn-⇓ p₁ r₁) of λ ()
na←naxnf-⇓ (app p₁) (app r₁ q₁ r₁′ r₂) = app

na←whnf-⇓ : ∀ {n} {e : Tm n} {e′} → WHNF e → NA e → e ⇓ e′ → NA e′
na←whnf-⇓ lam      () r
na←whnf-⇓ (whnf p) q  r = na←naxnf-⇓ p r

nf-⇓ : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → NF e′
nf-⇓ var                = nf var
nf-⇓ (lam r)            = lam (nf-⇓ r)
nf-⇓ (applam r₁ r)      = nf-⇓ r
nf-⇓ (app r₁ q₁ r₁′ r₂) = nf (app (nanf←nf (nf-⇓ r₁′) p₁) (nf-⇓ r₂))
  where
    p₁ = na←whnf-⇓ (BS-CBN.whnf-⇓ r₁) q₁ r₁′


---------------------------------------------------------------------------------------------------------------
--
-- BS-NO is reflexive

mutual
  refl-⇓ : ∀ {n} {e : Tm n} → NF e → e ⇓ e
  refl-⇓ (lam p) = lam (refl-⇓ p)
  refl-⇓ (nf p)  = refl-⇓′ p

  refl-⇓′ : ∀ {n} {e : Tm n} → NANF e → e ⇓ e
  refl-⇓′ var         = var
  refl-⇓′ (app p₁ p₂) = app (BS-CBN.refl-⇓′ (naxnf←nanf p₁)) (na←nanf p₁) (refl-⇓′ p₁) (refl-⇓ p₂)


---------------------------------------------------------------------------------------------------------------
