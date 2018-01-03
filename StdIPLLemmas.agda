module StdIPLLemmas where

open import Prelude
open import List
open import StdIPL


--------------------------------------------------------------------------------


idren : ∀ {Γ A} → (𝒟 : Γ ⊢ A true)
                → ren id⊇ 𝒟 ≡ 𝒟
idren (var 𝒾)   = var & idren∋ 𝒾
idren (lam 𝒟)   = lam & idren 𝒟
idren (app 𝒟 ℰ) = app & idren 𝒟 ⊗ idren ℰ

assocren : ∀ {Γ Γ′ Γ″ A} → (η₁ : Γ′ ⊇ Γ) (η₂ : Γ″ ⊇ Γ′) (𝒟 : Γ ⊢ A true)
                         → ren η₂ (ren η₁ 𝒟) ≡ ren (η₁ ∘⊇ η₂) 𝒟
assocren η₁ η₂ (var 𝒾)   = var & assocren∋ η₁ η₂ 𝒾
assocren η₁ η₂ (lam 𝒟)   = lam & assocren (keep η₁) (keep η₂) 𝒟
assocren η₁ η₂ (app 𝒟 ℰ) = app & assocren η₁ η₂ 𝒟 ⊗ assocren η₁ η₂ ℰ


--------------------------------------------------------------------------------


idlookups : ∀ {Γ Ξ} → (ξ : Γ ⊢⋆ Ξ)
                    → lookups ξ id⊇ ≡ ξ
idlookups ∙       = refl
idlookups (ξ , 𝒟) = (_, 𝒟) & idlookups ξ


sublookups : ∀ {Γ Ξ Ξ′ A} → (ξ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (𝒟 : Ξ ⊢ A true)
                          → sub ξ (ren η 𝒟) ≡ sub (lookups ξ η) 𝒟
sublookups ξ η 𝒟 = {!!}


--------------------------------------------------------------------------------


zapsubs : ∀ {Γ Ξ Ψ A} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ) (𝒟 : Γ ⊢ A true)
                      → subs (ξ , 𝒟) (wks ψ) ≡ subs ξ ψ
zapsubs ξ ∙       𝒟 = refl
zapsubs ξ (ψ , ℰ) 𝒟 = _,_ & zapsubs ξ ψ 𝒟 ⊗ ( sublookups (ξ , 𝒟) (drop id⊇) ℰ
                                            ⦙ (\ ξ′ → sub ξ′ ℰ) & idlookups ξ
                                            )


--------------------------------------------------------------------------------


lookuprens : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ) (𝒾 : Ξ ∋ A true)
                          → lookup (rens η ξ) 𝒾 ≡ ren η (lookup ξ 𝒾)
lookuprens η (ξ , 𝒟) zero    = refl
lookuprens η (ξ , 𝒟) (suc 𝒾) = lookuprens η ξ 𝒾
lookupwks : ∀ {Γ Ξ A B} → (ξ : Γ ⊢⋆ Ξ) (𝒾 : Ξ ∋ A true)
                        → lookup (wks {B} ξ) 𝒾 ≡ wk (lookup ξ 𝒾)
lookupwks ξ 𝒾 = lookuprens (drop id⊇) ξ 𝒾

lookupids : ∀ {Γ A} → (𝒾 : Γ ∋ A true)
                    → lookup ids 𝒾 ≡ var 𝒾
lookupids zero    = refl
lookupids (suc 𝒾) = lookupwks ids 𝒾
                  ⦙ wk & lookupids 𝒾
                  ⦙ var & (suc & idren∋ 𝒾)

idsub : ∀ {Γ A} → (𝒟 : Γ ⊢ A true)
                → sub ids 𝒟 ≡ 𝒟
idsub (var 𝒾)   = lookupids 𝒾
idsub (lam 𝒟)   = lam & idsub 𝒟
idsub (app 𝒟 ℰ) = app & idsub 𝒟 ⊗ idsub ℰ


--------------------------------------------------------------------------------


wksrens : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ)
                       → rens (drop η) ξ ≡ wks {A} (rens η ξ)
wksrens η ∙       = refl
wksrens η (ξ , 𝒟) = _,_ & wksrens η ξ ⊗ ( (\ η′ → ren (drop η′) 𝒟) & rid∘⊇ η ⁻¹
                                        ⦙ assocren η (drop id⊇) 𝒟 ⁻¹
                                        )

wksrens′ : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ)
                        → rens (keep η) (wks ξ) ≡ wks {A} (rens η ξ)
wksrens′ η ∙       = refl
wksrens′ η (ξ , 𝒟) = _,_ & wksrens′ η ξ ⊗ ( assocren (drop id⊇) (keep η) 𝒟
                                          ⦙ (\ η′ → ren (drop η′) 𝒟) & (lid∘⊇ η ⦙ rid∘⊇ η ⁻¹)
                                          ⦙ assocren η (drop id⊇) 𝒟 ⁻¹
                                          )

liftsrens : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ)
                         → rens (keep η) (lifts ξ) ≡ lifts {A} (rens η ξ)
liftsrens η ξ = (_, vz) & wksrens′ η ξ

mutual
  subrens : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ) (𝒟 : Ξ ⊢ A true)
                         → ren η (sub ξ 𝒟) ≡ sub (rens η ξ) 𝒟
  subrens η ξ (var 𝒾)   = lookuprens η ξ 𝒾 ⁻¹
  subrens η ξ (lam 𝒟)   = lam & subliftsrens η ξ 𝒟
  subrens η ξ (app 𝒟 ℰ) = app & subrens η ξ 𝒟 ⊗ subrens η ξ ℰ

  subliftsrens : ∀ {Γ Γ′ Ξ A B} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ) (𝒟 : Ξ , B true ⊢ A true)
                                → ren (keep η) (sub (lifts ξ) 𝒟) ≡ sub (lifts {B} (rens η ξ)) 𝒟
  subliftsrens η ξ 𝒟 = subrens (keep η) (lifts ξ) 𝒟
                     ⦙ (\ ξ′ → sub ξ′ 𝒟) & liftsrens η ξ


--------------------------------------------------------------------------------


lookupsubs : ∀ {Γ Ξ Ψ A} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ) (𝒾 : Ψ ∋ A true)
                         → lookup (subs ξ ψ) 𝒾 ≡ sub ξ (lookup ψ 𝒾)
lookupsubs ξ (ψ , 𝒟) zero    = refl
lookupsubs ξ (ψ , ℰ) (suc 𝒾) = lookupsubs ξ ψ 𝒾

wkssubs : ∀ {Γ Ξ Ψ A} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ)
                      → subs (wks ξ) ψ ≡ wks {A} (subs ξ ψ)
wkssubs ξ ∙       = refl
wkssubs ξ (ψ , 𝒟) = _,_ & wkssubs ξ ψ ⊗ subrens (drop id⊇) ξ 𝒟 ⁻¹

liftssubs : ∀ {Γ Ξ Ψ A} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ)
                        → subs (lifts ξ) (lifts ψ) ≡ lifts {A} (subs ξ ψ)
liftssubs ξ ψ = (_, vz) & ( zapsubs (wks ξ) ψ vz
                          ⦙ wkssubs ξ ψ
                          )

mutual
  assocsub : ∀ {Γ Ξ Ψ A} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ) (𝒟 : Ψ ⊢ A true)
                         → sub ξ (sub ψ 𝒟) ≡ sub (subs ξ ψ) 𝒟
  assocsub ξ ψ (var 𝒾)   = lookupsubs ξ ψ 𝒾 ⁻¹
  assocsub ξ ψ (lam 𝒟)   = lam & subliftssubs ξ ψ 𝒟
  assocsub ξ ψ (app 𝒟 ℰ) = app & assocsub ξ ψ 𝒟 ⊗ assocsub ξ ψ ℰ

  subliftssubs : ∀ {Γ Ξ Ψ A B} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ) (𝒟 : Ψ , B true ⊢ A true)
                               → sub (lifts ξ) (sub (lifts ψ) 𝒟) ≡ sub (lifts {B} (subs ξ ψ)) 𝒟
  subliftssubs ξ ψ 𝒟 = assocsub (lifts ξ) (lifts ψ) 𝒟
                     ⦙ (\ ξ′ → sub ξ′ 𝒟) & liftssubs ξ ψ





--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

_∋⋆_ = _⊇_

-- putᵣ

getᵣ = ren∋

pattern wkᵣ = _⊇_.drop

pattern liftᵣ = _⊇_.keep

idᵣ = id⊇

ren′ = ren

wk′ = wk

_○_ = _∘⊇_

--------------------------------------------------------------------------------

-- natgetᵣ

idgetᵣ = idren∋

idren′ = idren

--------------------------------------------------------------------------------

-- postulate
--   nope : ∀ {X A} → {Γ Γ′ : List X}
--                  → Γ′ ⊇ Γ → Γ′ ∋ A
--                  → Γ′ ⊇ Γ , A

-- postulate
--   zap○ : ∀ {X A} → {Γ Γ′ Γ″ : List X}
--                  → (η₁ : Γ′ ⊇ Γ) (η₂ : Γ″ ⊇ Γ′) (𝒾 : Γ″ ∋ A)
--                  → drop η₁ ∘⊇ nope η₂ 𝒾 ≡ η₁ ∘⊇ η₂

lid○ = lid∘⊇

rid○ = rid∘⊇

--------------------------------------------------------------------------------

get○ = assocren∋

-- wk○

-- lift○

-- wklid○

-- wkrid○

-- liftwkrid○

ren○ = assocren

-- renlift○

-- renwk○

-- renliftwk○

--------------------------------------------------------------------------------

assoc○ = assoc∘⊇

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------




--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

_⊢⋆′_ = _⊢⋆_

-- putₛ

getₛ = lookup

wkₛ = wks

liftₛ = lifts

idₛ = ids

sub′ = sub

cut′ = cut

_●_ : ∀ {Γ Ξ Ψ} → Ξ ⊢⋆ Ψ → Γ ⊢⋆ Ξ
                → Γ ⊢⋆ Ψ
ψ ● ξ = subs ξ ψ

--------------------------------------------------------------------------------

natgetₛ = lookupwks

idgetₛ = lookupids

idsub′ = idsub

--------------------------------------------------------------------------------

⌊_⌋ = hyps

_◐_ : ∀ {Γ Ξ Ξ′} → Γ ⊢⋆ Ξ′ → Ξ′ ⊇ Ξ
                 → Γ ⊢⋆ Ξ
ξ ◐ η = lookups ξ η

_◑_ : ∀ {Γ Γ′ Ξ} → Γ′ ⊇ Γ → Γ ⊢⋆ Ξ
                 → Γ′ ⊢⋆ Ξ
η ◑ ξ = rens η ξ

-- ⌊get⌋
-- ⌊wk⌋
-- ⌊lift⌋
-- ⌊id⌋
-- ⌊sub⌋
-- ⌊○⌋

--------------------------------------------------------------------------------

postulate
  zap◐ : ∀ {Γ Ξ Ξ′ A} → (ξ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (𝒟 : Γ ⊢ A true)
                      → lookups (ξ , 𝒟) (drop η) ≡ lookups ξ η

rid◐ : ∀ {Γ Ξ} → (ξ : Γ ⊢⋆ Ξ)
               → lookups ξ id⊇ ≡ ξ
rid◐ ξ = idlookups ξ

--------------------------------------------------------------------------------

postulate
  get◐ : ∀ {Γ Ξ Ξ′ A} → (ξ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (𝒾 : Ξ ∋ A true)
                      → lookup (lookups ξ η) 𝒾 ≡ lookup ξ (ren∋ η 𝒾)

postulate
  wk◐ : ∀ {Γ Ξ Ξ′ A} → (ξ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ)
                     → wks {A} (lookups ξ η) ≡ lookups (wks ξ) η

postulate
  lift◐ : ∀ {Γ Ξ Ξ′ A} → (ξ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ)
                       → lifts {A} (lookups ξ η) ≡ lookups (lifts ξ) (keep η)

postulate
  wkrid◐ : ∀ {Γ Ξ A} → (ξ : Γ ⊢⋆ Ξ)
                     → lookups (wks {A} ξ) id⊇ ≡ wks ξ

postulate
  liftwkrid◐ : ∀ {Γ Ξ A} → (ξ : Γ ⊢⋆ Ξ)
                         → lookups (lifts {A} ξ) (drop id⊇) ≡ wks ξ

sub◐ : ∀ {Γ Ξ Ξ′ A} → (ξ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (𝒟 : Ξ ⊢ A true)
                    → sub (lookups ξ η) 𝒟 ≡ sub ξ (ren η 𝒟)
sub◐ ξ η 𝒟 = sublookups ξ η 𝒟 ⁻¹

postulate
  sublift◐ : ∀ {Γ Ξ Ξ′ A B} → (ξ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (𝒟 : Ξ , B true ⊢ A true)
                            → sub (lifts {B} (lookups ξ η)) 𝒟 ≡ sub (lifts ξ) (ren (keep η) 𝒟)

postulate
  subwk◐ : ∀ {Γ Ξ Ξ′ A B} → (ξ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (𝒟 : Ξ ⊢ A true)
                          → sub (wks {B} (lookups ξ η)) 𝒟 ≡ sub (wks ξ) (ren η 𝒟)

postulate
  subliftwk◐ : ∀ {Γ Ξ Ξ′ A B} → (ξ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (𝒟 : Ξ ⊢ A true)
                              → sub (wks {B} (lookups ξ η)) 𝒟 ≡ sub (lifts ξ) (ren (drop η) 𝒟)

--------------------------------------------------------------------------------

-- postulate
--   zap◑ : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ) (𝒾 : Γ′ ∋ A true)
--                       → rens (nope η 𝒾) (wks ξ) ≡ rens η ξ

postulate
  lid◑ : ∀ {Γ Ξ} → (ξ : Γ ⊢⋆ Ξ)
                 → rens id⊇ ξ ≡ ξ

--------------------------------------------------------------------------------

zap● : ∀ {Γ Ξ Ψ A} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ) (𝒟 : Γ ⊢ A true)
                   → subs (ξ , 𝒟) (wks ψ) ≡ subs ξ ψ
zap● = zapsubs

postulate
  lid● : ∀ {Γ Ξ} → (ξ : Γ ⊢⋆ Ξ)
                 → subs ids ξ ≡ ξ

postulate
  rid● : ∀ {Γ Ξ} → (ξ : Γ ⊢⋆ Ξ)
                 → subs ξ ids ≡ ξ

--------------------------------------------------------------------------------

get◑ : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ) (𝒾 : Ξ ∋ A true)
                    → lookup (rens η ξ) 𝒾 ≡ ren η (lookup ξ 𝒾)
get◑ = lookuprens

wk◑ : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ)
                   → wks {A} (rens η ξ) ≡ rens (drop η) ξ
wk◑ η ξ = wksrens η ξ ⁻¹

lift◑ : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ)
                     → lifts {A} (rens η ξ) ≡ rens (keep η) (lifts ξ)
lift◑ η ξ = liftsrens η ξ ⁻¹

postulate
  wklid◑ : ∀ {Γ Ξ A} → (ξ : Γ ⊢⋆ Ξ)
                     → rens (drop {A = A} id⊇) ξ ≡ wks ξ

postulate
  liftwklid◑ : ∀ {Γ Ξ A} → (ξ : Γ ⊢⋆ Ξ)
                         → rens (keep {A = A} id⊇) (wks ξ) ≡ wks ξ

sub◑ : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ) (𝒟 : Ξ ⊢ A true)
                    → sub (rens η ξ) 𝒟 ≡ ren η (sub ξ 𝒟)
sub◑ η ξ 𝒟 = subrens η ξ 𝒟 ⁻¹

sublift◑ : ∀ {Γ Γ′ Ξ A B} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ) (𝒟 : Ξ , B true ⊢ A true)
                          → sub (lifts {B} (rens η ξ)) 𝒟 ≡ ren (keep η) (sub (lifts ξ) 𝒟)
sublift◑ η ξ 𝒟 = subliftsrens η ξ 𝒟 ⁻¹

postulate
  subwk◑ : ∀ {Γ Γ′ Ξ A B} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ) (𝒟 : Ξ ⊢ A true)
                          → sub (wks {B} (rens η ξ)) 𝒟 ≡ ren (drop η) (sub ξ 𝒟)

postulate
  subliftwk◑ : ∀ {Γ Γ′ Ξ A B} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ) (𝒟 : Ξ ⊢ A true)
                              → sub (wks {B} (rens η ξ)) 𝒟 ≡ ren (keep η) (sub (wks ξ) 𝒟)

--------------------------------------------------------------------------------

get● : ∀ {Γ Ξ Ψ A} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ) (𝒾 : Ψ ∋ A true)
                   → lookup (subs ξ ψ) 𝒾 ≡ sub ξ (lookup ψ 𝒾)
get● = lookupsubs

wk● : ∀ {Γ Ξ Ψ A} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ)
                  → wks {A} (subs ξ ψ) ≡ subs (wks ξ) ψ
wk● ξ ψ = wkssubs ξ ψ ⁻¹

lift● : ∀ {Γ Ξ Ψ A} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ)
                    → lifts {A} (subs ξ ψ) ≡ subs (lifts ξ) (lifts ψ)
lift● ξ ψ = liftssubs ξ ψ ⁻¹

postulate
  wklid● : ∀ {Γ Ξ A} → (ξ : Γ ⊢⋆ Ξ)
                     → subs (wks {A} ids) ξ ≡ wks ξ

postulate
  wkrid● : ∀ {Γ Ξ A} → (ξ : Γ ⊢⋆ Ξ)
                     → subs (wks {A} ξ) ids ≡ wks ξ

postulate
  liftwkrid● : ∀ {Γ Ξ A} → (ξ : Γ ⊢⋆ Ξ)
                         → subs (lifts {A} ξ) (wks ids) ≡ wks ξ

sub● : ∀ {Γ Ξ Ψ A} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ) (𝒟 : Ψ ⊢ A true)
                   → sub (subs ξ ψ) 𝒟 ≡ sub ξ (sub ψ 𝒟)
sub● ξ ψ 𝒟 = assocsub ξ ψ 𝒟 ⁻¹

sublift● : ∀ {Γ Ξ Ψ A B} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ) (𝒟 : Ψ , B true ⊢ A true)
                         → sub (lifts {B} (subs ξ ψ)) 𝒟 ≡ sub (lifts ξ) (sub (lifts ψ) 𝒟)
sublift● ξ ψ 𝒟 = subliftssubs ξ ψ 𝒟 ⁻¹

postulate
  subwk● : ∀ {Γ Ξ Ψ A B} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ) (𝒟 : Ψ ⊢ A true)
                         → sub (wks {B} (subs ξ ψ)) 𝒟 ≡ sub (wks ξ) (sub ψ 𝒟)

postulate
  subliftwk● : ∀ {Γ Ξ Ψ A B} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ) (𝒟 : Ψ ⊢ A true)
                             → sub (wks {B} (subs ξ ψ)) 𝒟 ≡ sub (lifts ξ) (sub (wks ψ) 𝒟)

--------------------------------------------------------------------------------

postulate
  comp◐○ : ∀ {Γ Ξ Ξ′ Ξ″} → (ξ : Γ ⊢⋆ Ξ″) (η₁ : Ξ′ ⊇ Ξ) (η₂ : Ξ″ ⊇ Ξ′)
                         → lookups ξ (η₁ ∘⊇ η₂) ≡ lookups (lookups ξ η₂) η₁

postulate
  comp◑○ : ∀ {Γ Γ′ Γ″ Ξ} → (η₁ : Γ′ ⊇ Γ) (η₂ : Γ″ ⊇ Γ′) (ξ : Γ ⊢⋆ Ξ)
                         → rens η₂ (rens η₁ ξ) ≡ rens (η₁ ∘⊇ η₂) ξ

postulate
  comp◑◐ : ∀ {Γ Γ′ Ξ Ξ′} → (η₁ : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ′) (η₂ : Ξ′ ⊇ Ξ)
                         → rens η₁ (lookups ξ η₂) ≡ lookups (rens η₁ ξ) η₂

postulate
  comp◑● : ∀ {Γ Γ′ Ξ Ψ} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ)
                        → rens η (subs ξ ψ) ≡ subs (rens η ξ) ψ

postulate
  comp●◐ : ∀ {Γ Ξ Ψ Ψ′} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ′) (η : Ψ′ ⊇ Ψ)
                        → subs ξ (lookups ψ η) ≡ lookups (subs ξ ψ) η

postulate
  comp●◑ : ∀ {Γ Ξ Ξ′ Ψ} → (ξ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (ψ : Ξ ⊢⋆ Ψ)
                        → subs ξ (rens η ψ) ≡ subs (lookups ξ η) ψ

--------------------------------------------------------------------------------

postulate
  assoc● : ∀ {Γ Ξ Ψ Φ} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ) (φ : Ψ ⊢⋆ Φ)
                       → subs ξ (subs ψ φ) ≡ subs (subs ξ ψ) φ
