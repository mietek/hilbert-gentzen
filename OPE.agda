----------------------------------------------------------------------------------------------------

-- order-preserving embeddings

module OPE {𝓍} {X : Set 𝓍} where

open import DBI public


----------------------------------------------------------------------------------------------------

infix 3 _⊑_
data _⊑_ : Tsil X → Tsil X → Set 𝓍 where
  stop  : ∙ ⊑ ∙
  wk⊑   : ∀ {B Γ Γ′} (ρ : Γ ⊑ Γ′) → Γ ⊑ Γ′ , B
  lift⊑ : ∀ {B Γ Γ′} (ρ : Γ ⊑ Γ′) → Γ , B ⊑ Γ′ , B

id⊑ refl⊑ : ∀ {Γ} → Γ ⊑ Γ
id⊑ {∙}     = stop
id⊑ {Γ , A} = lift⊑ id⊑
refl⊑ = id⊑

-- Kovacs: flip _∘ₑ_
_∘⊑_ : ∀ {Γ Γ′ Γ″} → Γ′ ⊑ Γ″ → Γ ⊑ Γ′ → Γ ⊑ Γ″
stop     ∘⊑ ρ       = ρ
wk⊑ ρ′   ∘⊑ ρ       = wk⊑ (ρ′ ∘⊑ ρ)
lift⊑ ρ′ ∘⊑ wk⊑ ρ   = wk⊑ (ρ′ ∘⊑ ρ)
lift⊑ ρ′ ∘⊑ lift⊑ ρ = lift⊑ (ρ′ ∘⊑ ρ)

trans⊑ _○_ : ∀ {Γ Γ′ Γ″} → Γ ⊑ Γ′ → Γ′ ⊑ Γ″ → Γ ⊑ Γ″
trans⊑ = flip _∘⊑_
_○_ = trans⊑

lid⊑ : ∀ {Γ Γ′} (ρ : Γ ⊑ Γ′) → id⊑ ∘⊑ ρ ≡ ρ
lid⊑ stop      = refl
lid⊑ (wk⊑ ρ)   = wk⊑ & lid⊑ ρ
lid⊑ (lift⊑ ρ) = lift⊑ & lid⊑ ρ

rid⊑ : ∀ {Γ Γ′} (ρ : Γ ⊑ Γ′) → ρ ∘⊑ id⊑ ≡ ρ
rid⊑ stop      = refl
rid⊑ (wk⊑ ρ)   = wk⊑ & rid⊑ ρ
rid⊑ (lift⊑ ρ) = lift⊑ & rid⊑ ρ

ass⊑ : ∀ {Γ Γ′ Γ″ Γ‴} (ρ″ : Γ″ ⊑ Γ‴) (ρ′ : Γ′ ⊑ Γ″) (ρ : Γ ⊑ Γ′) →
       ρ″ ∘⊑ (ρ′ ∘⊑ ρ) ≡ (ρ″ ∘⊑ ρ′) ∘⊑ ρ
ass⊑ stop       ρ′         ρ         = refl
ass⊑ (wk⊑ ρ″)   ρ′         ρ         = wk⊑ & ass⊑ ρ″ ρ′ ρ
ass⊑ (lift⊑ ρ″) (wk⊑ ρ′)   ρ         = wk⊑ & ass⊑ ρ″ ρ′ ρ
ass⊑ (lift⊑ ρ″) (lift⊑ ρ′) (wk⊑ ρ)   = wk⊑ & ass⊑ ρ″ ρ′ ρ
ass⊑ (lift⊑ ρ″) (lift⊑ ρ′) (lift⊑ ρ) = lift⊑ & ass⊑ ρ″ ρ′ ρ


----------------------------------------------------------------------------------------------------

ren∋ : ∀ {Γ Γ′ A} → Γ ⊑ Γ′ → Γ ∋ A → Γ′ ∋ A
ren∋ stop      i       = i
ren∋ (wk⊑ ρ)   i       = wk∋ (ren∋ ρ i)
ren∋ (lift⊑ ρ) zero    = zero
ren∋ (lift⊑ ρ) (wk∋ i) = wk∋ (ren∋ ρ i)

idren∋ : ∀ {Γ A} (i : Γ ∋ A) → ren∋ id⊑ i ≡ i
idren∋ zero    = refl
idren∋ (wk∋ i) = wk∋ & idren∋ i

compren∋ : ∀ {Γ Γ′ Γ″ A} (ρ′ : Γ′ ⊑ Γ″) (ρ : Γ ⊑ Γ′) (i : Γ ∋ A) →
           ren∋ (ρ′ ∘⊑ ρ) i ≡ (ren∋ ρ′ ∘ ren∋ ρ) i
compren∋ stop       ρ         i       = refl
compren∋ (wk⊑ ρ′)   ρ         i       = wk∋ & compren∋ ρ′ ρ i
compren∋ (lift⊑ ρ′) (wk⊑ ρ)   i       = wk∋ & compren∋ ρ′ ρ i
compren∋ (lift⊑ ρ′) (lift⊑ ρ) zero    = refl
compren∋ (lift⊑ ρ′) (lift⊑ ρ) (wk∋ i) = wk∋ & compren∋ ρ′ ρ i


----------------------------------------------------------------------------------------------------

-- TODO: delete?

injren∋ : ∀ {Γ Γ′ A} {ρ : Γ ⊑ Γ′} {i i′ : Γ ∋ A} → ren∋ ρ i ≡ ren∋ ρ i′ → i ≡ i′
injren∋ {ρ = stop}    {i}     {i′}     eq   = eq
injren∋ {ρ = wk⊑ ρ}   {i}     {i′}     eq   = injren∋ (injwk∋ eq)
injren∋ {ρ = lift⊑ ρ} {zero}  {zero}   refl = refl
injren∋ {ρ = lift⊑ ρ} {wk∋ i} {wk∋ i′} eq   = wk∋ & (injren∋ (injwk∋ eq))

unren∋ : ∀ {Γ Γ′ A} (ρ : Γ ⊑ Γ′) (i′ : Γ′ ∋ A) → Dec (Σ (Γ ∋ A) λ i → i′ ≡ ren∋ ρ i)
unren∋ stop      i′       = yes (i′ , refl)
unren∋ (wk⊑ ρ)   zero     = no λ ()
unren∋ (wk⊑ ρ)   (wk∋ i′) with unren∋ ρ i′
... | no ¬p                 = no λ { (i , refl) → (i , refl) ↯ ¬p }
... | yes (i , refl)        = yes (i , refl)
unren∋ (lift⊑ ρ) zero     = yes (zero , refl)
unren∋ (lift⊑ ρ) (wk∋ i′) with unren∋ ρ i′
... | no ¬p                 = no λ { (wk∋ i , refl) → (i , refl) ↯ ¬p }
... | yes (i , refl)        = yes (wk∋ i , refl)


----------------------------------------------------------------------------------------------------
