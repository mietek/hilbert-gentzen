module IPC.Conversion where

open import IPC.Core public

import IPC.Hilbert.Linear as HL
import IPC.Hilbert.Nested as HN
import IPC.Gentzen as G

open HL using () renaming (_⊢⁺_ to HL⟨_⊢⁺_⟩ ; _⊢_ to HL⟨_⊢_⟩) public
open HN using () renaming (_⊢_ to HN⟨_⊢_⟩) public
open G using () renaming (_⊢_ to G⟨_⊢_⟩) public


-- Conversion from linear Hilbert-style proofs to nested.

hl→hn : ∀ {A Γ} → HL⟨ Γ ⊢ A ⟩ → HN⟨ Γ ⊢ A ⟩
hl→hn (Π ∙ ts) = aux ts top
  where
    aux : ∀ {A Γ Π} → HL⟨ Γ ⊢⁺ Π ⟩ → Π ∋ A → HN⟨ Γ ⊢ A ⟩
    aux (HL.var i ts)  top     = HN.var i
    aux (HL.mp i j ts) top     = HN.app (aux ts i) (aux ts j)
    aux (HL.ci ts)     top     = HN.ci
    aux (HL.ck ts)     top     = HN.ck
    aux (HL.cs ts)     top     = HN.cs
    aux (HL.unit ts)   top     = HN.unit
    aux (HL.cpair ts)  top     = HN.cpair
    aux (HL.cfst ts)   top     = HN.cfst
    aux (HL.csnd ts)   top     = HN.csnd
    aux (HL.cinl ts)   top     = HN.cinl
    aux (HL.cinr ts)   top     = HN.cinr
    aux (HL.ccase ts)  top     = HN.ccase
    aux (HL.cboom ts)  top     = HN.cboom
    aux (HL.var i ts)  (pop k) = aux ts k
    aux (HL.mp i j ts) (pop k) = aux ts k
    aux (HL.ci ts)     (pop k) = aux ts k
    aux (HL.ck ts)     (pop k) = aux ts k
    aux (HL.cs ts)     (pop k) = aux ts k
    aux (HL.unit ts)   (pop k) = aux ts k
    aux (HL.cpair ts)  (pop k) = aux ts k
    aux (HL.cfst ts)   (pop k) = aux ts k
    aux (HL.csnd ts)   (pop k) = aux ts k
    aux (HL.cinl ts)   (pop k) = aux ts k
    aux (HL.cinr ts)   (pop k) = aux ts k
    aux (HL.ccase ts)  (pop k) = aux ts k
    aux (HL.cboom ts)  (pop k) = aux ts k


-- Conversion from nested Hilbert-style proofs to linear.

hn→hl : ∀ {A Γ} → HN⟨ Γ ⊢ A ⟩ → HL⟨ Γ ⊢ A ⟩
hn→hl (HN.var i)   = [] ∙ HL.var i HL.nil
hn→hl (HN.app t u) = HL.app (hn→hl t) (hn→hl u)
hn→hl HN.ci        = [] ∙ HL.ci HL.nil
hn→hl HN.ck        = [] ∙ HL.ck HL.nil
hn→hl HN.cs        = [] ∙ HL.cs HL.nil
hn→hl HN.unit      = [] ∙ HL.unit HL.nil
hn→hl HN.cpair     = [] ∙ HL.cpair HL.nil
hn→hl HN.cfst      = [] ∙ HL.cfst HL.nil
hn→hl HN.csnd      = [] ∙ HL.csnd HL.nil
hn→hl HN.cinl      = [] ∙ HL.cinl HL.nil
hn→hl HN.cinr      = [] ∙ HL.cinr HL.nil
hn→hl HN.ccase     = [] ∙ HL.ccase HL.nil
hn→hl HN.cboom     = [] ∙ HL.cboom HL.nil


-- Deduction theorem for linear Hilbert-style proofs.

hl-lam : ∀ {A B Γ} → HL⟨ Γ , A ⊢ B ⟩ → HL⟨ Γ ⊢ A ⇒ B ⟩
hl-lam = hn→hl ∘ HN.lam ∘ hl→hn


-- Conversion from Hilbert-style proofs to Gentzen-style.

hn→g : ∀ {A Γ} → HN⟨ Γ ⊢ A ⟩ → G⟨ Γ ⊢ A ⟩
hn→g (HN.var i)   = G.var i
hn→g (HN.app t u) = G.app (hn→g t) (hn→g u)
hn→g HN.ci        = G.ci
hn→g HN.ck        = G.ck
hn→g HN.cs        = G.cs
hn→g HN.unit      = G.unit
hn→g HN.cpair     = G.cpair
hn→g HN.cfst      = G.cfst
hn→g HN.csnd      = G.csnd
hn→g HN.cinl      = G.cinl
hn→g HN.cinr      = G.cinr
hn→g HN.ccase     = G.ccase
hn→g HN.cboom     = G.cboom

hl→g : ∀ {A Γ} → HL⟨ Γ ⊢ A ⟩ → G⟨ Γ ⊢ A ⟩
hl→g = hn→g ∘ hl→hn


-- Conversion from Gentzen-style proofs to Hilbert-style.

g→hn : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → HN⟨ Γ ⊢ A ⟩
g→hn (G.var i)      = HN.var i
g→hn (G.lam t)      = HN.lam (g→hn t)
g→hn (G.app t u)    = HN.app (g→hn t) (g→hn u)
g→hn G.unit         = HN.unit
g→hn (G.pair t u)   = HN.pair (g→hn t) (g→hn u)
g→hn (G.fst t)      = HN.fst (g→hn t)
g→hn (G.snd t)      = HN.snd (g→hn t)
g→hn (G.inl t)      = HN.inl (g→hn t)
g→hn (G.inr t)      = HN.inr (g→hn t)
g→hn (G.case t u v) = HN.case (g→hn t) (g→hn u) (g→hn v)
g→hn (G.boom t)     = HN.boom (g→hn t)

g→hl : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → HL⟨ Γ ⊢ A ⟩
g→hl = hn→hl ∘ g→hn
