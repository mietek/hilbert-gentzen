---------------------------------------------------------------------------------------------------------------
--
-- Equivalence of SS-H and BS-H
--
--                    5.7.1
--      SS-CBN|SS-H₂ ← SS-H ⎫       SS-H        ⎫     SS-H
--  5.1.1 ↓      ↓ 5.7.2     ⎬ 5.7.4 ↓   ↑ 5.7.5 ⎬ 5.7.6 ↕
--      BS-CBN|BS-H₂ → BS-H ⎭       BS-H        ⎭     BS-H
--                    5.7.3

module 5-7-Equivalence-H where

open import 1-2-Syntax-Predicates
import 2-1-Semantics-BigStep as BS
import 2-2-Semantics-SmallStep as SS
import 3-1-Properties-BigStep-CBN as BS-CBN
import 3-7-1-Properties-BigStep-H as BS-H
import 3-7-2-Properties-BigStep-H₂ as BS-H₂
import 4-1-Properties-SmallStep-CBN as SS-CBN
import 4-7-1-Properties-SmallStep-H as SS-H
import 4-7-2-Properties-SmallStep-H₂ as SS-H₂
open import 5-1-Equivalence-CBN


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 5.7.1.  SS-H to HNF implies SS-CBN to WHNF followed by SS-H₂ to HNF

module Lem-5-7-1 where
  open SS

  cbn←h : ∀ {n} {e : Tm n} {e′} → ¬ WHNF e → e H.⇒ e′ → e CBN.⇒ e′
  cbn←h ¬p (H.lam r)      = lam ↯ ¬p
  cbn←h ¬p H.applam       = CBN.applam
  cbn←h ¬p (H.app₁ p₁ r₁) with whnf? _
  ... | no ¬p₁′            = CBN.app₁ (cbn←h ¬p₁′ r₁)
  ... | yes p₁′            = whnf (app (naxnf←whnf p₁′ p₁)) ↯ ¬p

  h₂←h : ∀ {n} {e : Tm n} {e′} → WHNF e → e H.⇒ e′ → e H₂.⇒ e′
  h₂←h lam             (H.lam r)       with whnf? _
  ... | no ¬p                           = H₂.lam₋ ¬p (cbn←h ¬p r)
  ... | yes p                           = H₂.lam₊ p (h₂←h p r)
  h₂←h (whnf var)      ()
  h₂←h (whnf (app ())) H.applam
  h₂←h (whnf (app p₁)) (H.app₁ p₁′ r₁) = H₂.app₁₊ p₁ (h₂←h (whnf p₁) r₁)

  cbn|h₂←h : ∀ {n} {e : Tm n} {e′} → e H.⇒ e′ → (e CBN.⇒ e′) ⊎ (e H₂.⇒ e′)
  cbn|h₂←h r with whnf? _
  ... | no ¬p = inj₁ (cbn←h ¬p r)
  ... | yes p = inj₂ (h₂←h p r)

  h₂←h* : ∀ {n} {e : Tm n} {e′} → WHNF e → e H.⇒* e′ → e H₂.⇒* e′
  h₂←h* p ε        = ε
  h₂←h* p (r ◅ rs) = h₂←h p r ◅ h₂←h* (SS-H₂.whnf-⇒ (h₂←h p r)) rs

  cbn|h₂←h* : ∀ {n} {e : Tm n} {e′} → e H.⇒* e′ → HNF e′ →
                 (∃ λ e″ →
                   e CBN.⇒* e″ × WHNF e″ × e″ H₂.⇒* e′)
  cbn|h₂←h* ε        p′   = _ , ε , whnf←hnf p′ , ε
  cbn|h₂←h* (r ◅ rs) p′   with cbn|h₂←h r
  ... | inj₂ r′            = _ , ε , SS-H₂.rev-whnf-⇒ r′ , r′ ◅ h₂←h* (SS-H₂.whnf-⇒ r′) rs
  ... | inj₁ r′            with cbn|h₂←h* rs p′
  ... | _ , rs′ , p″ , rs″ = _ , r′ ◅ rs′ , p″ , rs″


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 5.7.2.  SS-H₂ to HNF implies BS-H₂

module Lem-5-7-2 where
  open BS-H₂
  open SS-H₂

  rev-lam₊* : ∀ {n i} {e : Tm (suc n)} {e′} → WHNF e → lam e ⇒*⟨ i ⟩ lam e′ → e ⇒*⟨ i ⟩ e′
  rev-lam₊* p ε                = ε
  rev-lam₊* p (lam₋ ¬p r ◅ rs) = p ↯ ¬p
  rev-lam₊* p (lam₊ p′ r ◅ rs) = r ◅ rev-lam₊* (whnf-⇒ r) rs

  rev-lam₋* : ∀ {n i} {e : Tm (suc n)} {e′} →
              lam e ⇒*⟨ i ⟩ lam e′ → HNF e′ →
              (∃ λ e″ →
                e SS.CBN.⇒*⟨ i ⟩ e″ × WHNF e″ × e″ ⇒* e′)
  rev-lam₋* ε                p′ = _ , ε , whnf←hnf p′ , ε
  rev-lam₋* (lam₋ ¬p r ◅ rs) p′ with rev-lam₋* rs p′
  ... | _ , rs′ , p″ , rs″      = _ , r ◅ rs′ , p″ , rs″
  rev-lam₋* (lam₊ p r ◅ rs)  p′ = _ , ε , p , r ◅ rev-lam₊* (whnf-⇒ r) rs

  ¬lam⇒*var : ∀ {n} {e : Tm (suc n)} {x} → ¬ (lam e ⇒* var x)
  ¬lam⇒*var = λ { (lam₋ ¬p r ◅ rs) → rs ↯ ¬lam⇒*var
                 ; (lam₊ p r ◅ rs)  → rs ↯ ¬lam⇒*var }

  ¬lam⇒*app : ∀ {n} {e : Tm (suc n)} {e₁ e₂} → ¬ (lam e ⇒* app e₁ e₂)
  ¬lam⇒*app = λ { (lam₋ ¬p r ◅ rs) → rs ↯ ¬lam⇒*app
                 ; (lam₊ p r ◅ rs)  → rs ↯ ¬lam⇒*app }

  rev-app₁₊* : ∀ {n i} {e₁ e₂ : Tm n} {e′} →
               app e₁ e₂ ⇒*⟨ i ⟩ e′ → HNF e′ →
               (∃ λ e₁′ →
                 e₁ ⇒*⟨ i ⟩ e₁′ × NAXNF e₁′ × app e₁′ e₂ ≡ e′)
  rev-app₁₊* ε                  (hnf (app p₁′)) = _ , ε , p₁′ , refl
  rev-app₁₊* (app₁₊ p₁ r₁ ◅ rs) p′              with rev-app₁₊* rs p′
  ... | _ , rs₁ , p₁′ , refl                    = _ , r₁ ◅ rs₁ , p₁′ , refl

  mutual
    bs←ss : ∀ {n i} {e : Tm n} {e′} → e ⇒*⟨ i ⟩ e′ → HNF e′ → e ⟱ e′
    bs←ss ε        p′ = refl-⟱ p′
    bs←ss (r ◅ rs) p′ = bs←ss′ r rs p′

    bs←ss′ : ∀ {n i} {e : Tm n} {e′ e″} → e ⇒ e′ → e′ ⇒*⟨ i ⟩ e″ → HNF e″ → e ⟱ e″
    bs←ss′ (lam₋ ¬p r)       rs (lam p″)      with rev-lam₋* rs p″
    ... | _ , rs′ , p′ , rs″                   = lam (Lem-5-1-1.bs←ss′ r rs′ p′)
                                                     (bs←ss rs″ p″)
    bs←ss′ (lam₋ ¬p r)       rs (hnf var)     = rs ↯ ¬lam⇒*var
    bs←ss′ (lam₋ ¬p r)       rs (hnf (app _)) = rs ↯ ¬lam⇒*app
    bs←ss′ (lam₊ p r)        rs (lam p″)      = lam (BS-CBN.refl-⟱ p)
                                                     (bs←ss′ r (rev-lam₊* (whnf-⇒ r) rs) p″)
    bs←ss′ (lam₊ p r)        rs (hnf var)     = rs ↯ ¬lam⇒*var
    bs←ss′ (lam₊ p r)        rs (hnf (app _)) = rs ↯ ¬lam⇒*app
    bs←ss′ (app₁₊ p₁ r₁)     rs p″            with rev-app₁₊* rs p″
    ... | _ , rs₁ , p₁′ , refl                 = app p₁ (bs←ss′ r₁ rs₁ (hnf p₁′))


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 5.7.3.  BS-CBN followed by BS-H₂ implies BS-H

module Lem-5-7-3 where
  open BS

  h←cbn|h₂ : ∀ {n} {e : Tm n} {e′ e″} → e CBN.⟱ e′ → e′ H₂.⟱ e″ → e H.⟱ e″
  h←cbn|h₂ CBN.var           H₂.var          = H.var
  h←cbn|h₂ CBN.lam           (H₂.lam r r′)   = H.lam (h←cbn|h₂ r r′)
  h←cbn|h₂ (CBN.applam r₁ r) r′              = H.applam r₁ (h←cbn|h₂ r r′)
  h←cbn|h₂ (CBN.app r₁ p₁′)  (H₂.app p₁ r₁′) = H.app r₁ p₁′ r₁″
    where
      r₁″ = h←cbn|h₂ (BS-CBN.refl-⟱ (BS-CBN.whnf-⟱ r₁)) r₁′


---------------------------------------------------------------------------------------------------------------
--
-- Corollary 5.7.4.  SS-H to HNF implies BS-H

module Cor-5-7-4 where
  open SS-H
  open BS-H

  bs←ss : ∀ {n} {e : Tm n} {e′} → e ⇒* e′ → HNF e′ → e ⟱ e′
  bs←ss rs p′             with Lem-5-7-1.cbn|h₂←h* rs p′
  ... | _ , rs′ , p″ , rs″ = Lem-5-7-3.h←cbn|h₂ (Lem-5-1-1.bs←ss rs′ p″)
                                                 (Lem-5-7-2.bs←ss rs″ p′)


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 5.7.5.  BS-H implies SS-H

module Lem-5-7-5 where
  open SS-H
  open BS-H

  lam* : ∀ {n} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam e ⇒* lam e′
  lam* = map lam

  applam* : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} → app (lam e₁) e₂ ⇒* e₁ [ e₂ ]
  applam* = applam ◅ ε

  cbn-app₁* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ SS.CBN.⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
  cbn-app₁* = map cbn-app₁

  app₁₊* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → NAXNF e₁ → e₁ ⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
  app₁₊* p₁ ε          = ε
  app₁₊* p₁ (r₁ ◅ rs₁) = app₁₊ p₁ r₁ ◅ app₁₊* (naxnf-⇒ p₁ r₁) rs₁

  bs-lam : ∀ {n} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam e ⇒* lam e′
  bs-lam = lam*

  bs-applam : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e′} →
              e₁ SS.CBN.⇒* lam e₁′ → e₁′ [ e₂ ] ⇒* e′ →
              app e₁ e₂ ⇒* e′
  bs-applam rs₁ rs = cbn-app₁* rs₁ ◅◅ applam* ◅◅ rs

  bs-app : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e₁″} →
           e₁ SS.CBN.⇒* e₁′ → NAXNF e₁′ → e₁′ ⇒* e₁″ →
           app e₁ e₂ ⇒* app e₁″ e₂
  bs-app rs₁ p₁′ rs₁′ = cbn-app₁* rs₁ ◅◅ app₁₊* p₁′ rs₁′

  ss←bs : ∀ {n} {e : Tm n} {e′} → e ⟱ e′ → e ⇒* e′
  ss←bs var              = ε
  ss←bs (lam r)          = bs-lam (ss←bs r)
  ss←bs (applam r₁ r)    = bs-applam (Lem-5-1-2.ss←bs r₁) (ss←bs r)
  ss←bs (app r₁ p₁′ r₁′) = bs-app (Lem-5-1-2.ss←bs r₁) p₁″ (ss←bs r₁′)
    where
      p₁″ = naxnf←whnf (BS-CBN.whnf-⟱ r₁) p₁′


---------------------------------------------------------------------------------------------------------------
--
-- Theorem 5.7.6.  SS-H to HNF and BS-H coincide

module Thm-5-7-6 where
  ss↔bs : ∀ {n} {e : Tm n} {e′} → (e SS.H.⇒* e′ × HNF e′) ↔ e BS.H.⟱ e′
  ss↔bs = uncurry Cor-5-7-4.bs←ss , λ r → Lem-5-7-5.ss←bs r , BS-H.hnf-⟱ r


---------------------------------------------------------------------------------------------------------------
