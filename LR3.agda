module LR3 where

open import Prelude
open import Category
open import Fin
open import FinLemmas
open import Vec
open import VecLemmas
open import AllVec
open import LR0
open import LR0Lemmas
open import LR1
open import LR2


--------------------------------------------------------------------------------


-- TODO: Improve naming for all `id-cons-*` lemmas and this one.
-- TODO: Move to LR0Lemmas.

lem-cons-SUBS : ∀ {g n m} → (τ : Terms g n) (M : Term g) (υ : Terms n m)
                          → (SUBS (τ , M) ∘ LIFTS) υ ≡ SUBS τ υ , M
lem-cons-SUBS τ M υ = (_, M) & id-cons-WKS-SUBS τ M υ


comp-CUT-SUB-LIFTS : ∀ {g n} → (N : Term g) (τ : Terms g n) (M : Term (suc n))
                             → SUB (τ , N) M ≡ (CUT N ∘ SUB (LIFTS τ)) M
comp-CUT-SUB-LIFTS N τ M = (\ τ′ → SUB τ′ M) & ( (_, N) & lid-SUBS τ ⁻¹
                                                ⋮ lem-cons-SUBS IDS N τ ⁻¹
                                                )
                         ⋮ comp-SUB (IDS , N) (LIFTS τ) M


--------------------------------------------------------------------------------


-- uniq↦ : ∀ {g} → {M M′₁ M′₂ : Term g}
--                → M ↦ M′₁ → M ↦ M′₂
--                → M′₁ ≡ M′₂
-- uniq↦ red-APP-LAM                 red-APP-LAM                 = refl
-- uniq↦ red-APP-LAM                 (red-cong E₂ M↦M′₂ {{p₂}}) = {!!}
-- uniq↦ red-IF-TRUE                 red-IF-TRUE                 = refl
-- uniq↦ red-IF-TRUE                 (red-cong E₂ M↦M′₂ {{p₂}}) = {!!}
-- uniq↦ red-IF-FALSE                red-IF-FALSE                = refl
-- uniq↦ red-IF-FALSE                (red-cong E₂ M↦M′₂ {{p₂}}) = {!!}
-- uniq↦ (red-cong E₁ M↦M′₁ {{p₁}}) red-APP-LAM                 = {!!}
-- uniq↦ (red-cong E₁ M↦M′₁ {{p₁}}) red-IF-TRUE                 = {!!}
-- uniq↦ (red-cong E₁ M↦M′₁ {{p₁}}) red-IF-FALSE                = {!!}
-- uniq↦ (red-cong E₁ M↦M′₁ {{p₁}}) (red-cong E₂ M↦M′₂ {{p₂}}) = {!!}


postulate
  oops : ∀ {g} → {M M′ M″ : Term g}
               → M ↦ M′ → M ⤅ M″
               → M′ ⤅ M″
-- oops M↦M′ done                = {!!}
-- oops M↦M′ (step M↦M° M°⤅M″) = {!!}


--------------------------------------------------------------------------------


SN : Term 0 → Type → Set
SN M 𝔹       = ∙ ⊢ M ⦂ 𝔹 × M ⇓
SN M (A ⊃ B) = ∙ ⊢ M ⦂ A ⊃ B × M ⇓ × (∀ {N} → SN N A → SN (APP M N) B)


derp : ∀ {A M} → SN M A
               → ∙ ⊢ M ⦂ A
derp {𝔹}     (𝒟 , M⇓)     = 𝒟
derp {A ⊃ B} (𝒟 , M⇓ , f) = 𝒟


--------------------------------------------------------------------------------


-- Small-step reduction preserves SN.
snp↦ : ∀ {A M M′} → M ↦ M′ → ∙ ⊢ M ⦂ A → SN M′ A
                   → SN M A
snp↦ {𝔹}     M↦M′ 𝒟 (𝒟′ , (M″ , (iv-M″ , M′⤅M″)))     = 𝒟 , (M″ , (iv-M″ , step M↦M′ M′⤅M″))
snp↦ {A ⊃ B} M↦M′ 𝒟 (𝒟′ , (M″ , (iv-M″ , M′⤅M″)) , f) = 𝒟 , (M″ , (iv-M″ , step M↦M′ M′⤅M″)) , (\ s →
                                                             snp↦ (red-fun-APP M↦M′) (app 𝒟 (derp s)) (f s))


-- Big-step reduction preserves SN.
snp⤅ : ∀ {A M M′} → M ⤅ M′ → ∙ ⊢ M ⦂ A → SN M′ A
                   → SN M A
snp⤅ done                𝒟 s = s
snp⤅ (step M↦M″ M″⤅M′) 𝒟 s = snp↦ M↦M″ 𝒟 (snp⤅ M″⤅M′ (tp↦ M↦M″ 𝒟) s)


-- IF `M` reduces to `TRUE`, and `N` is SN, then `IF M N O` is SN.
sn-IF-TRUE : ∀ {C M N O} → M ⤅ TRUE → ∙ ⊢ M ⦂ 𝔹 → SN N C → ∙ ⊢ O ⦂ C
                         → SN (IF M N O) C
sn-IF-TRUE {𝔹}     M⤅TRUE 𝒟 (ℰ , N⇓)     ℱ = if 𝒟 ℰ ℱ , halt-IF-TRUE M⤅TRUE N⇓
sn-IF-TRUE {A ⊃ B} M⤅TRUE 𝒟 (ℰ , N⇓ , f) ℱ = if 𝒟 ℰ ℱ , halt-IF-TRUE M⤅TRUE N⇓ , (\ s →
                                                snp⤅ (step-fun-APP (step-IF-TRUE M⤅TRUE done)) (app (if 𝒟 ℰ ℱ) (derp s)) (f s))


-- IF `M` reduces to `FALSE`, and `O` is SN, then `IF M N O` is SN.
sn-IF-FALSE : ∀ {C M N O} → M ⤅ FALSE → ∙ ⊢ M ⦂ 𝔹 → ∙ ⊢ N ⦂ C → SN O C
                          → SN (IF M N O) C
sn-IF-FALSE {𝔹}     M⤅FALSE 𝒟 ℰ (ℱ , O⇓)     = if 𝒟 ℰ ℱ , halt-IF-FALSE M⤅FALSE O⇓
sn-IF-FALSE {A ⊃ B} M⤅FALSE 𝒟 ℰ (ℱ , O⇓ , f) = if 𝒟 ℰ ℱ , halt-IF-FALSE M⤅FALSE O⇓ , (\ s →
                                                  snp⤅ (step-fun-APP (step-IF-FALSE M⤅FALSE done)) (app (if 𝒟 ℰ ℱ) (derp s)) (f s))


--------------------------------------------------------------------------------


-- Small-step reduction preserves SN in reverse.
rsnp↦ : ∀ {A M M′} → M ↦ M′ → ∙ ⊢ M ⦂ A → SN M A
                    → SN M′ A
rsnp↦ {𝔹}     M↦M′ 𝒟 (_ , (M″ , (iv-M″ , M⤅M″)))     = tp↦ M↦M′ 𝒟 , (M″ , (iv-M″ , oops M↦M′ M⤅M″))
rsnp↦ {A ⊃ B} M↦M′ 𝒟 (_ , (M″ , (iv-M″ , M⤅M″)) , f) = tp↦ M↦M′ 𝒟 , (M″ , (iv-M″ , oops M↦M′ M⤅M″)) , (\ s →
                                                            rsnp↦ (red-fun-APP M↦M′) (app 𝒟 (derp s)) (f s))


-- Big-step reduction preserves SN in reverse.
rsnp⤅ : ∀ {A M M′} → M ⤅ M′ → ∙ ⊢ M ⦂ A → SN M A
                    → SN M′ A
rsnp⤅ done                𝒟 s = s
rsnp⤅ (step M↦M″ M″⤅M′) 𝒟 s = rsnp⤅ M″⤅M′ (tp↦ M↦M″ 𝒟) (rsnp↦ M↦M″ 𝒟 s)


--------------------------------------------------------------------------------


SNs : ∀ {g} → (τ : Terms 0 g) → Types g → {{_ : AreVals τ}} → Set
SNs τ Γ = All (\ { (M , A) → SN M A }) (zip τ Γ)


derps : ∀ {g} → {τ : Terms 0 g} {Γ : Types g} → {{_ : AreVals τ}}
              → SNs τ Γ
              → ∙ ⊢ τ ⦂ Γ all
derps σ = maps derp σ


--------------------------------------------------------------------------------


-- Substitution is type-preserving.
tp-SUB : ∀ {g M A} → {τ : Terms 0 g} {Γ : Types g} → {{_ : AreVals τ}}
                   → SNs τ Γ → Γ ⊢ M ⦂ A
                   → ∙ ⊢ SUB τ M ⦂ A
tp-SUB σ 𝒟 = sub (derps σ) 𝒟


red-APP-LAM-SUB : ∀ {g M N} → {τ : Terms 0 g} → {{_ : IsVal N}}
                            → APP (LAM (SUB (LIFTS τ) M)) N ↦ SUB (τ , N) M
red-APP-LAM-SUB {M = M} {N} {τ} rewrite comp-CUT-SUB-LIFTS N τ M = red-APP-LAM


halt-APP-LAM-SUB : ∀ {g M N} → {τ : Terms 0 g} → {{_ : AreVals τ}} {{_ : IsVal N}}
                             → SUB (τ , N) M ⇓
                             → APP (LAM (SUB (LIFTS τ) M)) N ⇓
halt-APP-LAM-SUB {M = M} (M′ , (iv-M′ , SUB-M⤅M′)) = M′ , (iv-M′ , step (red-APP-LAM-SUB {M = M}) SUB-M⤅M′)


sn-APP-LAM-SUB : ∀ {B g M N A} → {τ : Terms 0 g} → {{_ : AreVals τ}} {{_ : IsVal N}}
                               → ∙ ⊢ SUB τ (LAM M) ⦂ A ⊃ B → ∙ ⊢ N ⦂ A → SN (SUB (τ , N) M) B
                               → SN (APP (LAM (SUB (LIFTS τ) M)) N) B
sn-APP-LAM-SUB {𝔹}       {M = M} 𝒟 ℰ (𝒟′ , SUB-M⇓)     = app 𝒟 ℰ , halt-APP-LAM-SUB {M = M} SUB-M⇓
sn-APP-LAM-SUB {B₁ ⊃ B₂} {M = M} 𝒟 ℰ (𝒟′ , SUB-M⇓ , f) = app 𝒟 ℰ , halt-APP-LAM-SUB {M = M} SUB-M⇓ , (\ s →
                                                           snp↦ (red-fun-APP (red-APP-LAM-SUB {M = M})) (app (app 𝒟 ℰ) (derp s)) (f s))


--------------------------------------------------------------------------------


bump : ∀ {A M} → SN M A
               → Σ (Term 0) (\ M′ → ∙ ⊢ M ⦂ A × M ⇓ M′ × SN M′ A)
bump {𝔹}     s@(𝒟 , (M′ , M⇓M′@(iv-M′ , M⤅M′)))     = M′ , (𝒟 , M⇓M′ , rsnp⤅ M⤅M′ 𝒟 s)
bump {A ⊃ B} s@(𝒟 , (M′ , M⇓M′@(iv-M′ , M⤅M′)) , f) = M′ , (𝒟 , M⇓M′ , rsnp⤅ M⤅M′ 𝒟 s)


sn-SUB : ∀ {g M A} → {τ : Terms 0 g} {Γ : Types g} → {{_ : AreVals τ}}
                   → SNs τ Γ → Γ ⊢ M ⦂ A
                   → SN (SUB τ M) A
sn-SUB          σ (var i)             = get σ (zip∋₂ i)
sn-SUB {{av-τ}} σ (lam {A} {M = M} 𝒟) = let 𝒟′ = tp-SUB σ (lam 𝒟) in 𝒟′ , (LAM _ , (iv-LAM , done)) , (\ s →
                                          case bump {A} s of (\ { (N′ , (ℰ , (iv-N′ , N⤅N′) , s′)) →
                                            snp⤅ (step-APP-arg N⤅N′)
                                                  (app 𝒟′ ℰ)
                                                  (sn-APP-LAM-SUB {M = M} {{av-τ}} {{iv-N′}} 𝒟′ (derp s′) (sn-SUB {{av-τ , iv-N′}} (σ , s′) 𝒟))}))
sn-SUB          σ (app 𝒟 ℰ)           with sn-SUB σ 𝒟
sn-SUB          σ (app 𝒟 ℰ)           | 𝒟′ , (M′ , SUB-M⤅M′) , f = f (sn-SUB σ ℰ)
sn-SUB          σ true                = true , (TRUE , (iv-TRUE , done))
sn-SUB          σ false               = false , (FALSE , (iv-FALSE , done))
sn-SUB          σ (if 𝒟 ℰ ℱ)          with sn-SUB σ 𝒟
sn-SUB          σ (if 𝒟 ℰ ℱ)          | 𝒟′ , (M′     , (iv-M′    , SUB-M⤅M′))     with tp⤅ SUB-M⤅M′ 𝒟′
sn-SUB          σ (if 𝒟 ℰ ℱ)          | 𝒟′ , (LAM M″ , (iv-LAM   , SUB-M⤅LAM-M″)) | ()
sn-SUB          σ (if 𝒟 ℰ ℱ)          | 𝒟′ , (TRUE   , (iv-TRUE  , SUB-M⤅TRUE))   | true  = sn-IF-TRUE SUB-M⤅TRUE 𝒟′ (sn-SUB σ ℰ) (tp-SUB σ ℱ)
sn-SUB          σ (if 𝒟 ℰ ℱ)          | 𝒟′ , (FALSE  , (iv-FALSE , SUB-M⤅FALSE))  | false = sn-IF-FALSE SUB-M⤅FALSE 𝒟′ (tp-SUB σ ℰ) (sn-SUB σ ℱ)


--------------------------------------------------------------------------------


sn : ∀ {M A} → ∙ ⊢ M ⦂ A
             → SN M A
sn {M} {A} 𝒟 = subst (\ M′ → SN M′ A) (id-SUB M) (sn-SUB ∙ 𝒟)


halt-sn : ∀ {A M} → SN M A
                  → M ⇓
halt-sn {𝔹}     (𝒟 , M⇓)     = M⇓
halt-sn {A ⊃ B} (𝒟 , M⇓ , f) = M⇓


halt : ∀ {A M} → ∙ ⊢ M ⦂ A
               → M ⇓
halt {A} 𝒟 = halt-sn {A} (sn 𝒟)


--------------------------------------------------------------------------------
