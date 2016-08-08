module IPC.Hilbert.TreeWithContext.TarskiSoundness where

open import IPC.Hilbert.TreeWithContext public
open import IPC.TarskiSemantics public




module NaturalSoundness where
  open NaturalSemantics public


  -- Soundness with respect to all models, or evaluation.

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
  eval (var i)   γ = lookup i γ
  eval (app t u) γ = (eval t γ) (eval u γ)
  eval ci        γ = id
  eval ck        γ = const
  eval cs        γ = ap
  eval cpair     γ = _,_
  eval cfst      γ = π₁
  eval csnd      γ = π₂
  eval tt        γ = ∙
  eval cboom     γ = elim𝟘
  eval cinl      γ = ι₁
  eval cinr      γ = ι₂
  eval ccase     γ = elim⊎