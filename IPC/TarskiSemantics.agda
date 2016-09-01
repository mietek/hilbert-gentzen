module IPC.TarskiSemantics where

open import IPC public


-- Tarski models.

record Model : Set₁ where
  infix 3 ⊩ᵅ_
  field
    -- Forcing for atomic propositions.
    ⊩ᵅ_ : Atom → Set

open Model {{…}} public




module NaturalSemantics where


  -- Forcing in a particular model.

  infix 3 ⊩_
  ⊩_ : ∀ {{_ : Model}} → Ty → Set
  ⊩ α P   = ⊩ᵅ P
  ⊩ A ▻ B = ⊩ A → ⊩ B
  ⊩ A ∧ B = ⊩ A × ⊩ B
  ⊩ ⊤    = 𝟙
  ⊩ ⊥    = 𝟘
  ⊩ A ∨ B = ⊩ A ⊎ ⊩ B

  infix 3 ⊩⋆_
  ⊩⋆_ : ∀ {{_ : Model}} → Cx Ty → Set
  ⊩⋆ ∅     = 𝟙
  ⊩⋆ Ξ , A = ⊩⋆ Ξ × ⊩ A


  -- Forcing in all models.

  infix 3 ᴹ⊩_
  ᴹ⊩_ : Ty → Set₁
  ᴹ⊩ A = ∀ {{_ : Model}} → ⊩ A

  infix 3 _ᴹ⊩_
  _ᴹ⊩_ : Cx Ty → Ty → Set₁
  Γ ᴹ⊩ A = ∀ {{_ : Model}} → ⊩⋆ Γ → ⊩ A


  -- Additional useful equipment.

  λˢ : ∀ {{_ : Model}} {A B Γ}
       → (⊩⋆ Γ × ⊩ A → ⊩ B)
       → ⊩⋆ Γ → ⊩ A → ⊩ B
  λˢ f γ = λ a → f (γ , a)

  _$ˢᶜ_ : ∀ {{_ : Model}} {A B Γ}
          → (⊩⋆ Γ → ⊩ A → ⊩ B)
          → (⊩⋆ Γ → ⊩ A)
          → ⊩⋆ Γ → ⊩ B
  (f $ˢᶜ g) γ = (f γ) (g γ)

  apˢᶜ : ∀ {{_ : Model}} {A B C Γ}
         → (⊩⋆ Γ → ⊩ A → ⊩ B → ⊩ C)
         → (⊩⋆ Γ → ⊩ A → ⊩ B)
         → (⊩⋆ Γ → ⊩ A)
         → ⊩⋆ Γ → ⊩ C
  apˢᶜ f g a γ = ((f γ) (a γ)) ((g γ) (a γ))

  _,ˢᶜ_ : ∀ {{_ : Model}} {A B Γ}
          → (⊩⋆ Γ → ⊩ A)
          → (⊩⋆ Γ → ⊩ B)
          → ⊩⋆ Γ → ⊩ A × ⊩ B
  (a ,ˢᶜ b) γ = a γ , b γ

  π₁ˢᶜ : ∀ {{_ : Model}} {A B Γ}
         → (⊩⋆ Γ → ⊩ A × ⊩ B)
         → ⊩⋆ Γ → ⊩ A
  π₁ˢᶜ s γ = π₁ (s γ)

  π₂ˢᶜ : ∀ {{_ : Model}} {A B Γ}
         → (⊩⋆ Γ → ⊩ A × ⊩ B)
         → ⊩⋆ Γ → ⊩ B
  π₂ˢᶜ s γ = π₂ (s γ)

  elim𝟘ˢᶜ : ∀ {{_ : Model}} {C Γ}
            → (⊩⋆ Γ → 𝟘)
            → ⊩⋆ Γ → ⊩ C
  elim𝟘ˢᶜ s γ = elim𝟘 (s γ)

  ι₁ˢᶜ : ∀ {{_ : Model}} {A B Γ}
         → (⊩⋆ Γ → ⊩ A)
         → ⊩⋆ Γ → ⊩ A ⊎ ⊩ B
  ι₁ˢᶜ a γ = ι₁ (a γ)

  ι₂ˢᶜ : ∀ {{_ : Model}} {A B Γ}
         → (⊩⋆ Γ → ⊩ B)
         → ⊩⋆ Γ → ⊩ A ⊎ ⊩ B
  ι₂ˢᶜ b γ = ι₂ (b γ)

  elim⊎ˢᶜ : ∀ {{_ : Model}} {A B C Γ}
            → (⊩⋆ Γ → ⊩ A ⊎ ⊩ B)
            → (⊩⋆ Γ → ⊩ A → ⊩ C)
            → (⊩⋆ Γ → ⊩ B → ⊩ C)
            → ⊩⋆ Γ → ⊩ C
  elim⊎ˢᶜ s f g γ = elim⊎ (s γ) (f γ) (g γ)

  elim⊎ˢᶜ′ : ∀ {{_ : Model}} {A B C Γ}
             → (⊩⋆ Γ → ⊩ A ⊎ ⊩ B)
             → (⊩⋆ Γ × ⊩ A → ⊩ C)
             → (⊩⋆ Γ × ⊩ B → ⊩ C)
             → ⊩⋆ Γ → ⊩ C
  elim⊎ˢᶜ′ s f g γ = elim⊎ (s γ) (λ a → f (γ , a)) (λ b → g (γ , b))

  lookup : ∀ {A Γ} → A ∈ Γ → Γ ᴹ⊩ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ




-- Forcing with a syntactic component, inspired by Coquand and Dybjer.

module CoquandDybjerSemantics (Syntax : Ty → Set) where


  -- Forcing in a particular model.

  infix 3 ⊩_
  ⊩_ : ∀ {{_ : Model}} → Ty → Set
  ⊩ α P   = Syntax (α P) × ⊩ᵅ P
  ⊩ A ▻ B = Syntax (A ▻ B) × (⊩ A → ⊩ B)
  ⊩ A ∧ B = ⊩ A × ⊩ B
  ⊩ ⊤    = 𝟙
  ⊩ ⊥    = 𝟘
  ⊩ A ∨ B = ⊩ A ⊎ ⊩ B

  infix 3 ⊩⋆_
  ⊩⋆_ : ∀ {{_ : Model}} → Cx Ty → Set
  ⊩⋆ ∅     = 𝟙
  ⊩⋆ Ξ , A = ⊩⋆ Ξ × ⊩ A


  -- Forcing in all models.

  infix 3 ᴹ⊩_
  ᴹ⊩_ : Ty → Set₁
  ᴹ⊩ A = ∀ {{_ : Model}} → ⊩ A

  infix 3 _ᴹ⊩_
  _ᴹ⊩_ : Cx Ty → Ty → Set₁
  Γ ᴹ⊩ A = ∀ {{_ : Model}} → ⊩⋆ Γ → ⊩ A


  -- Additional useful equipment.

  _$ˢ_ : ∀ {{_ : Model}} {A B}
         → Syntax (A ▻ B) × (⊩ A → ⊩ B)
         → ⊩ A
         → ⊩ B
  (t , f) $ˢ a = f a

  apˢ : ∀ {{_ : Model}} {A B C}
        → Syntax (A ▻ B ▻ C) × (⊩ A → Syntax (B ▻ C) × (⊩ B → ⊩ C))
        → Syntax (A ▻ B) × (⊩ A → ⊩ B)
        → ⊩ A
        → ⊩ C
  apˢ (t , f) (u , g) a = let (_ , h) = f a
                          in  h (g a)

  elim⊎ˢ : ∀ {{_ : Model}} {A B C}
           → ⊩ A ⊎ ⊩ B
           → Syntax (A ▻ C) × (⊩ A → ⊩ C)
           → Syntax (B ▻ C) × (⊩ B → ⊩ C)
           → ⊩ C
  elim⊎ˢ (ι₁ a) (u , f) (v , g) = f a
  elim⊎ˢ (ι₂ b) (u , f) (v , g) = g b

  _$ˢᶜ_ : ∀ {{_ : Model}} {A B Γ}
          → (⊩⋆ Γ → Syntax (A ▻ B) × (⊩ A → ⊩ B))
          → (⊩⋆ Γ → ⊩ A)
          → ⊩⋆ Γ → ⊩ B
  (f $ˢᶜ g) γ = (f γ) $ˢ (g γ)

  apˢᶜ : ∀ {{_ : Model}} {A B C Γ}
         → (⊩⋆ Γ → Syntax (A ▻ B ▻ C) × (⊩ A → Syntax (B ▻ C) × (⊩ B → ⊩ C)))
         → (⊩⋆ Γ → Syntax (A ▻ B) × (⊩ A → ⊩ B))
         → (⊩⋆ Γ → ⊩ A)
         → ⊩⋆ Γ → ⊩ C
  apˢᶜ f g a γ = apˢ (f γ) (g γ) (a γ)

  _,ˢᶜ_ : ∀ {{_ : Model}} {A B Γ}
          → (⊩⋆ Γ → ⊩ A)
          → (⊩⋆ Γ → ⊩ B)
          → ⊩⋆ Γ → ⊩ A × ⊩ B
  (a ,ˢᶜ b) γ = a γ , b γ

  π₁ˢᶜ : ∀ {{_ : Model}} {A B Γ}
         → (⊩⋆ Γ → ⊩ A × ⊩ B)
         → ⊩⋆ Γ → ⊩ A
  π₁ˢᶜ s γ = π₁ (s γ)

  π₂ˢᶜ : ∀ {{_ : Model}} {A B Γ}
         → (⊩⋆ Γ → ⊩ A × ⊩ B)
         → ⊩⋆ Γ → ⊩ B
  π₂ˢᶜ s γ = π₂ (s γ)

  elim𝟘ˢᶜ : ∀ {{_ : Model}} {C Γ}
            → (⊩⋆ Γ → 𝟘)
            → ⊩⋆ Γ → ⊩ C
  elim𝟘ˢᶜ s γ = elim𝟘 (s γ)

  ι₁ˢᶜ : ∀ {{_ : Model}} {A B Γ}
         → (⊩⋆ Γ → ⊩ A)
         → ⊩⋆ Γ → ⊩ A ⊎ ⊩ B
  ι₁ˢᶜ a γ = ι₁ (a γ)

  ι₂ˢᶜ : ∀ {{_ : Model}} {A B Γ}
         → (⊩⋆ Γ → ⊩ B)
         → ⊩⋆ Γ → ⊩ A ⊎ ⊩ B
  ι₂ˢᶜ b γ = ι₂ (b γ)

  elim⊎ˢᶜ : ∀ {{_ : Model}} {A B C Γ}
            → (⊩⋆ Γ → ⊩ A ⊎ ⊩ B)
            → (⊩⋆ Γ → Syntax (A ▻ C) × (⊩ A → ⊩ C))
            → (⊩⋆ Γ → Syntax (B ▻ C) × (⊩ B → ⊩ C))
            → ⊩⋆ Γ → ⊩ C
  elim⊎ˢᶜ s f g γ = elim⊎ˢ (s γ) (f γ) (g γ)

  lookup : ∀ {A Γ} → A ∈ Γ → Γ ᴹ⊩ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ
