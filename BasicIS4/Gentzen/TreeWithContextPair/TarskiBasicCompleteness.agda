module BasicIS4.Gentzen.TreeWithContextPair.TarskiBasicCompleteness where

open import BasicIS4.Gentzen.TreeWithContextPair.TarskiSoundness public




module CoquandDybjerBasicCompleteness where
  open CoquandDybjerSoundness public


  -- The canonical model.

  instance
    canon : Model
    canon = record
      { ⊨ᵅ_ = λ P → ⌀ ⁏ ⌀ ⊢ α P
      }


  -- Completeness with respect to all models, or quotation.

  -- TODO: Can we do better here?
  quot₀ : ∀ {A} → ⌀ ⁏ ⌀ ᴹ⊨ A → ⌀ ⁏ ⌀ ⊢ A
  quot₀ t = reify (t ∙ ∙)


  -- Normalisation by evaluation.

  -- TODO: Can we do better here?
  norm₀ : ∀ {A} → ⌀ ⁏ ⌀ ⊢ A → ⌀ ⁏ ⌀ ⊢ A
  norm₀ = quot₀ ∘ eval


  -- TODO: Correctness of normalisation with respect to conversion.
