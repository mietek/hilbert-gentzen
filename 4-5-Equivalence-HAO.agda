---------------------------------------------------------------------------------------------------------------
--
-- Equivalence of SS-HAO and BS-HAO
--
--                     5.1
--      SS-CBV|SS-HAO₂ ← SS-HAO ⎫       SS-HAO      ⎫     SS-HAO
--  4.3.1 ↓      ↓ 4.5.2         ⎬ 4.5.4 ↓ × ↑ 4.5.5 ⎬ 4.5.6 ↕
--      BS-CBV|BS-HAO₂ → BS-HAO ⎭       BS-HAO      ⎭     BS-HAO
--                     5.3

module 4-5-Equivalence-HAO where

open import 1-2-Syntax-Predicates
import 1-3-Semantics-SmallStep as SS
import 1-4-Semantics-BigStep as BS
import 2-3-Properties-SmallStep-CBV as SS-CBV
import 2-5-1-Properties-SmallStep-HAO as SS-HAO
-- import 2-5-2-Properties-SmallStep-HAO₂ as SS-HAO₂
import 3-3-Properties-BigStep-CBV as BS-CBV
import 3-5-1-Properties-BigStep-HAO as BS-HAO
-- import 3-5-2-Properties-BigStep-HAO₂ as BS-HAO₂
import 4-3-Equivalence-CBV as CBV


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 4.5.1.  SS-HAO to NF implies SS-CBV to WNF followed by SS-HAO₂ to NF

module Lem-4-5-1 where
  open SS


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 4.5.2.  SS-HAO₂ to NF implies BS-HAO₂

module Lem-4-5-2 where
--  open SS-HAO₂
--  open BS-HAO₂


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 4.5.3.  BS-CBV followed by BS-HAO₂ implies BS-HAO

module Lem-4-5-3 where
  open BS


---------------------------------------------------------------------------------------------------------------
--
-- Corollary 4.5.4.  SS-HAO to NF implies BS-HAO

module Cor-4-5-4 where
  open SS-HAO
  open BS-HAO


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 4.5.5.  BS-HAO implies SS-HAO

module Lem-4-5-5 where
  open SS-HAO
  open BS-HAO

  lam* : ∀ {n} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam e ⇒* lam e′
  lam* = map lam

  applam* : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} → NF e₂ → app (lam e₁) e₂ ⇒* e₁ [ e₂ ]
  applam* p₂ = applam p₂ ◅ ε

  cbv-app₁* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ SS.CBV.⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
  cbv-app₁* = map cbv-app₁

  app₁* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → NAWNF e₁ → e₁ ⇒* e₁′ → app e₁ e₂ ⇒* app e₁′ e₂
  app₁* p₁ ε          = ε
  app₁* p₁ (r₁ ◅ rs₁) = app₁ p₁ r₁ ◅ app₁* (nawnf-⇒ p₁ r₁) rs₁

  app₂ₐ* : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} {e₂′} → e₂ ⇒* e₂′ → app (lam e₁) e₂ ⇒* app (lam e₁) e₂′
  app₂ₐ* = map app₂ₐ

  app₂* : ∀ {n} {e₁ e₂ : Tm n} {e₂′} → NANF e₁ → e₂ ⇒* e₂′ → app e₁ e₂ ⇒* app e₁ e₂′
  app₂* p₁ = map (app₂ p₁)

  bs-lam : ∀ {n} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam e ⇒* lam e′
  bs-lam = lam*

  bs-applam : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e₂′ e′} →
              e₁ SS.CBV.⇒* lam e₁′ → e₂ ⇒* e₂′ → NF e₂′ → e₁′ [ e₂′ ] ⇒* e′ →
              app e₁ e₂ ⇒* e′
  bs-applam rs₁ rs₂ p₂′ rs = cbv-app₁* rs₁ ◅◅ app₂ₐ* rs₂ ◅◅ applam* p₂′ ◅◅ rs

  bs-app : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e₁″ e₂′} →
           e₁ SS.CBV.⇒* e₁′ → NAWNF e₁′ → e₁′ ⇒* e₁″ → NANF e₁″ → e₂ ⇒* e₂′ →
           app e₁ e₂ ⇒* app e₁″ e₂′
  bs-app rs₁ p₁′ rs₁′ p₁″ rs₂ = cbv-app₁* rs₁ ◅◅ app₁* p₁′ rs₁′ ◅◅ app₂* p₁″ rs₂

  ss←bs : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → e ⇒* e′
  ss←bs var                 = ε
  ss←bs (lam r)             = bs-lam (ss←bs r)
  ss←bs (applam r₁ r₂ r)    = bs-applam (CBV.Lem-4-3-2.ss←bs r₁) (ss←bs r₂) (nf-⇓ r₂) (ss←bs r)
  ss←bs (app r₁ q₁′ r₁′ r₂) = bs-app (CBV.Lem-4-3-2.ss←bs r₁) p₁′ (ss←bs r₁′) p₁″ (ss←bs r₂)
    where
      p₁′ = nawnf←wnf (BS-CBV.wnf-⇓ r₁) q₁′
      p₁″ = nanf←nf (nf-⇓ r₁′) (na←wnf-⇓ (BS-CBV.wnf-⇓ r₁) q₁′ r₁′)


---------------------------------------------------------------------------------------------------------------
--
-- Theorem 4.5.6.  SS-HAO to NF and BS-HAO coincide

module Thm-4-5-6 where
--  ss-hao↔bs-hao : ∀ {n} {e : Tm n} {e′} → (e SS.HAO.⇒* e′ × NF e′) ↔ e BS.HAO.⇓ e′
--  ss-hao↔bs-hao = uncurry Cor-4-5-4.bs←ss , λ r → Lem-4-5-5.ss←bs r , BS-HAO.nf-⇓ r


---------------------------------------------------------------------------------------------------------------
