---------------------------------------------------------------------------------------------------------------
--
-- A formalisation of big-step and small-step operational semantics for λ-calculus

module Everything where

open import Prelude

open import Syntax-Terms
open import Syntax-Predicates

import Semantics-SmallStep as SS
import Semantics-BigStep as BS

import Properties-SmallStep-CBN
import Properties-SmallStep-NO
import Properties-SmallStep-NO₂
import Properties-SmallStep-CBV
import Properties-SmallStep-AO
import Properties-SmallStep-HAO
import Properties-SmallStep-HS
import Properties-SmallStep-H
import Properties-SmallStep-HNO

import Properties-BigStep-CBN
import Properties-BigStep-NO
import Properties-BigStep-NO₂
import Properties-BigStep-CBV
import Properties-BigStep-AO
import Properties-BigStep-HAO
import Properties-BigStep-HS
import Properties-BigStep-H
import Properties-BigStep-HNO

import Equivalence-CBN as CBN
import Equivalence-NO  as NO
import Equivalence-CBV as CBV
import Equivalence-AO  as AO
import Equivalence-HAO as HAO
import Equivalence-HS  as HS
import Equivalence-H   as H
import Equivalence-HNO as HNO


---------------------------------------------------------------------------------------------------------------
--
-- Call-by-name reduction to weak head normal forms

-- Theorem 1.3.  SS-CBN to WHNF and BS-CBN coincide

thm-1-3 : ∀ {n} {e : Tm n} {e′} → (e SS.CBN.⇒* e′ × WHNF e′) ↔ e BS.CBN.⇓ e′
thm-1-3 = CBN.Thm-1-3.ss-cbn↔bs-cbn


---------------------------------------------------------------------------------------------------------------
--
-- Normal order reduction to normal forms

-- Theorem 2.6.  SS-NO to NF and BS-NO coincide

thm-2-6 : ∀ {n} {e : Tm n} {e′} → (e SS.NO.⇒* e′ × NF e′) ↔ e BS.NO.⇓ e′
thm-2-6 = NO.Thm-2-6.ss-no↔bs-no


---------------------------------------------------------------------------------------------------------------
--
-- Call-by-value reduction to weak normal forms

-- Theorem 3.3.  SS-CBV to WNF and BS-CBV coincide

thm-3-3 : ∀ {n} {e : Tm n} {e′} → (e SS.CBV.⇒* e′ × WNF e′) ↔ e BS.CBV.⇓ e′
thm-3-3 = CBV.Thm-3-3.ss-cbv↔bs-cbv


---------------------------------------------------------------------------------------------------------------
--
-- Applicative order reduction to normal forms

-- Theorem 4.3.  SS-AO to NF and BS-AO coincide

thm-4-3 : ∀ {n} {e : Tm n} {e′} → (e SS.AO.⇒* e′ × NF e′) ↔ e BS.AO.⇓ e′
thm-4-3 = AO.Thm-4-3.ss-ao↔bs-ao


---------------------------------------------------------------------------------------------------------------
--
-- Hybrid applicative order reduction to normal forms

-- Theorem 5.6.  SS-HAO to NF and BS-HAO coincide

-- thm-5-6 : ∀ {n} {e : Tm n} {e′} → (e SS.HAO.⇒* e′ × NF e′) ↔ e BS.HAO.⇓ e′
-- thm-5-6 = HAO.Thm-5-6.ss-hao↔bs-hao


---------------------------------------------------------------------------------------------------------------
--
-- Head spine reduction to head normal forms

-- Theorem 6.3.  SS-HS to HNF and BS-HS coincide

thm-6-3 : ∀ {n} {e : Tm n} {e′} → (e SS.HS.⇒* e′ × HNF e′) ↔ e BS.HS.⇓ e′
thm-6-3 = HS.Thm-6-3.ss-hs↔bs-hs


---------------------------------------------------------------------------------------------------------------
--
-- Head reduction to head normal forms

-- Theorem 7.6.  SS-H to HNF and BS-H coincide

-- thm-7-6 : ∀ {n} {e : Tm n} {e′} → (e SS.H.⇒* e′ × HNF e′) ↔ e BS.H.⇓ e′
-- thm-7-6 = H.Thm-7-6.ss-h↔bs-h


---------------------------------------------------------------------------------------------------------------
--
-- Hybrid normal order reduction to normal forms

-- Theorem 8.6.  SS-HNO to NF and BS-HNO coincide

-- thm-8-6 : ∀ {n} {e : Tm n} {e′} → (e SS.HNO.⇒* e′ × NF e′) ↔ e BS.HNO.⇓ e′
-- thm-8-6 = HNO.Thm-8-6.ss-hno↔bs-hno


---------------------------------------------------------------------------------------------------------------
--
-- References
--
-- * A. Garcia-Perez, et al. (2013)
--   “Deriving the full-reducing Krivine machine from the small-step operational semantics of normal order”
--   http://oa.upm.es/30153/1/30153nogueiraINVES_MEM_2013.pdf
--
-- * J.C. Mitchell (1996)
--   “Foundations for programming languages”
--
-- * L. Paulson (1996)
--   “ML for the working programmer”
--   https://www.cl.cam.ac.uk/~lp15/MLbook/PDF/chapter9.pdf
--
-- * B. Pierce (2001)
--   “Types and programming languages”
--
-- * P. Sestoft (2002)
--   “Demonstrating lambda calculus reduction”
--   http://www.itu.dk/~sestoft/papers/sestoft-lamreduce.pdf
--
-- * G. Winskel (1993)
--   “The formal semantics of programming languages”


---------------------------------------------------------------------------------------------------------------
