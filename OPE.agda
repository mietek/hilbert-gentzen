----------------------------------------------------------------------------------------------------

-- order-preserving embeddings

module OPE {𝓍} {X : Set 𝓍} where

open import DBI public


----------------------------------------------------------------------------------------------------

infix 3 _⊑_
data _⊑_ : Tsil X → Tsil X → Set 𝓍 where
  stop  : ∙ ⊑ ∙
  wk⊑   : ∀ {B Γ Γ′} (ϱ : Γ ⊑ Γ′) → Γ ⊑ Γ′ , B
  lift⊑ : ∀ {B Γ Γ′} (ϱ : Γ ⊑ Γ′) → Γ , B ⊑ Γ′ , B

id⊑ refl⊑ : ∀ {Γ} → Γ ⊑ Γ
id⊑ {∙}     = stop
id⊑ {Γ , A} = lift⊑ id⊑
refl⊑ = id⊑

-- Kovacs: flip _∘ₑ_
_∘⊑_ : ∀ {Γ Γ′ Γ″} → Γ′ ⊑ Γ″ → Γ ⊑ Γ′ → Γ ⊑ Γ″
stop     ∘⊑ ϱ       = ϱ
wk⊑ ϱ′   ∘⊑ ϱ       = wk⊑ (ϱ′ ∘⊑ ϱ)
lift⊑ ϱ′ ∘⊑ wk⊑ ϱ   = wk⊑ (ϱ′ ∘⊑ ϱ)
lift⊑ ϱ′ ∘⊑ lift⊑ ϱ = lift⊑ (ϱ′ ∘⊑ ϱ)

trans⊑ _○_ : ∀ {Γ Γ′ Γ″} → Γ ⊑ Γ′ → Γ′ ⊑ Γ″ → Γ ⊑ Γ″
trans⊑ = flip _∘⊑_
_○_ = trans⊑

lid⊑ : ∀ {Γ Γ′} (ϱ : Γ ⊑ Γ′) → id⊑ ∘⊑ ϱ ≡ ϱ
lid⊑ stop      = refl
lid⊑ (wk⊑ ϱ)   = wk⊑ & lid⊑ ϱ
lid⊑ (lift⊑ ϱ) = lift⊑ & lid⊑ ϱ

rid⊑ : ∀ {Γ Γ′} (ϱ : Γ ⊑ Γ′) → ϱ ∘⊑ id⊑ ≡ ϱ
rid⊑ stop      = refl
rid⊑ (wk⊑ ϱ)   = wk⊑ & rid⊑ ϱ
rid⊑ (lift⊑ ϱ) = lift⊑ & rid⊑ ϱ

ass⊑ : ∀ {Γ Γ′ Γ″ Γ‴} (ϱ″ : Γ″ ⊑ Γ‴) (ϱ′ : Γ′ ⊑ Γ″) (ϱ : Γ ⊑ Γ′) →
       ϱ″ ∘⊑ (ϱ′ ∘⊑ ϱ) ≡ (ϱ″ ∘⊑ ϱ′) ∘⊑ ϱ
ass⊑ stop       ϱ′         ϱ         = refl
ass⊑ (wk⊑ ϱ″)   ϱ′         ϱ         = wk⊑ & ass⊑ ϱ″ ϱ′ ϱ
ass⊑ (lift⊑ ϱ″) (wk⊑ ϱ′)   ϱ         = wk⊑ & ass⊑ ϱ″ ϱ′ ϱ
ass⊑ (lift⊑ ϱ″) (lift⊑ ϱ′) (wk⊑ ϱ)   = wk⊑ & ass⊑ ϱ″ ϱ′ ϱ
ass⊑ (lift⊑ ϱ″) (lift⊑ ϱ′) (lift⊑ ϱ) = lift⊑ & ass⊑ ϱ″ ϱ′ ϱ


----------------------------------------------------------------------------------------------------

ren∋ : ∀ {Γ Γ′ A} → Γ ⊑ Γ′ → Γ ∋ A → Γ′ ∋ A
ren∋ stop      i       = i
ren∋ (wk⊑ ϱ)   i       = wk∋ (ren∋ ϱ i)
ren∋ (lift⊑ ϱ) zero    = zero
ren∋ (lift⊑ ϱ) (wk∋ i) = wk∋ (ren∋ ϱ i)

idren∋ : ∀ {Γ A} (i : Γ ∋ A) → ren∋ id⊑ i ≡ i
idren∋ zero    = refl
idren∋ (wk∋ i) = wk∋ & idren∋ i

compren∋ : ∀ {Γ Γ′ Γ″ A} (ϱ′ : Γ′ ⊑ Γ″) (ϱ : Γ ⊑ Γ′) (i : Γ ∋ A) →
           ren∋ (ϱ′ ∘⊑ ϱ) i ≡ (ren∋ ϱ′ ∘ ren∋ ϱ) i
compren∋ stop       ϱ         i       = refl
compren∋ (wk⊑ ϱ′)   ϱ         i       = wk∋ & compren∋ ϱ′ ϱ i
compren∋ (lift⊑ ϱ′) (wk⊑ ϱ)   i       = wk∋ & compren∋ ϱ′ ϱ i
compren∋ (lift⊑ ϱ′) (lift⊑ ϱ) zero    = refl
compren∋ (lift⊑ ϱ′) (lift⊑ ϱ) (wk∋ i) = wk∋ & compren∋ ϱ′ ϱ i


----------------------------------------------------------------------------------------------------

-- TODO: delete?

injren∋ : ∀ {Γ Γ′ A} {ϱ : Γ ⊑ Γ′} {i i′ : Γ ∋ A} → ren∋ ϱ i ≡ ren∋ ϱ i′ → i ≡ i′
injren∋ {ϱ = stop}    {i}     {i′}     eq   = eq
injren∋ {ϱ = wk⊑ ϱ}   {i}     {i′}     eq   = injren∋ (injwk∋ eq)
injren∋ {ϱ = lift⊑ ϱ} {zero}  {zero}   refl = refl
injren∋ {ϱ = lift⊑ ϱ} {wk∋ i} {wk∋ i′} eq   = wk∋ & (injren∋ (injwk∋ eq))

unren∋ : ∀ {Γ Γ′ A} (ϱ : Γ ⊑ Γ′) (i′ : Γ′ ∋ A) → Dec (Σ (Γ ∋ A) λ i → i′ ≡ ren∋ ϱ i)
unren∋ stop      i′       = yes (i′ , refl)
unren∋ (wk⊑ ϱ)   zero     = no λ ()
unren∋ (wk⊑ ϱ)   (wk∋ i′) with unren∋ ϱ i′
... | no ¬p                 = no λ { (i , refl) → (i , refl) ↯ ¬p }
... | yes (i , refl)        = yes (i , refl)
unren∋ (lift⊑ ϱ) zero     = yes (zero , refl)
unren∋ (lift⊑ ϱ) (wk∋ i′) with unren∋ ϱ i′
... | no ¬p                 = no λ { (wk∋ i , refl) → (i , refl) ↯ ¬p }
... | yes (i , refl)        = yes (wk∋ i , refl)


----------------------------------------------------------------------------------------------------
