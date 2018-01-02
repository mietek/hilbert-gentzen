module StdLPTT where

open import Prelude
open import Fin
open import Vec


-- -- --

-- data Tele (F : Nat → Set) : Nat → Set
--   where
--     ∙ : Tele F zero
--
--     _,_∵_ : ∀ {n n′} → Tele F n′ → F n → n′ ≥ n
--                      → Tele F (suc n′)

-- infix 4 _⊇⟪_⟫_
-- data _⊇⟪_⟫_ {F} : ∀ {n n′} → Tele F n′ → n′ ≥ n → Tele F n → Set
--   where
--     done : ∙ ⊇⟪ done ⟫ ∙
--
--     drop : ∀ {n n′ e} → {Ξ : Tele F n} {Ξ′ : Tele F n′} {A : F n′}
--                       → Ξ′ ⊇⟪ e ⟫ Ξ
--                       → Ξ′ , A ∵ id≥ ⊇⟪ drop e ⟫ Ξ
--
--     keep : ∀ {n n′ e} → {Ξ : Tele F n} {Ξ′ : Tele F n′} {A : F n}
--                       → Ξ′ ⊇⟪ e ⟫ Ξ
--                       → Ξ′ , A ∵ e ⊇⟪ keep e ⟫ Ξ , A ∵ id≥

-- infix 4 _∋⟪_⟫_∵_
-- data _∋⟪_⟫_∵_ {F} : ∀ {n n′} → Tele F n′ → Fin n′ → F n → n′ ≥ n → Set
--   where
--     zero : ∀ {n} → {Ξ : Tele F n} {A : F n}
--                  → Ξ , A ∵ id≥ ∋⟪ zero ⟫ A ∵ drop id≥
--
--     suc : ∀ {n′ n i} → {Ξ : Tele F n′} {A : F n} {B : F n′} {e : n′ ≥ n}
--                      → Ξ ∋⟪ i ⟫ A ∵ e
--                      → Ξ , B ∵ id≥ ∋⟪ suc i ⟫ A ∵ drop e


-- -- --


data Term : Nat → Nat → Set
  where
    VAR    : ∀ {d g} → Fin g → Term d g
    LAM    : ∀ {d g} → Term d (suc g) → Term d g
    APP    : ∀ {d g} → Term d g → Term d g → Term d g
    MVAR   : ∀ {d g} → Fin d → Term d g
    BOX    : ∀ {d g} → Term d zero → Term d g
    LETBOX : ∀ {d g} → Term d g → Term (suc d) g → Term d g


REN : ∀ {d g g′} → g′ ≥ g → Term d g
                 → Term d g′
REN e (VAR i)      = VAR (renFin e i)
REN e (LAM M)      = LAM (REN (keep e) M)
REN e (APP M N)    = APP (REN e M) (REN e N)
REN e (MVAR i)     = MVAR i
REN e (BOX M)      = BOX M
REN e (LETBOX M N) = LETBOX (REN e M) (REN e N)

WK : ∀ {d g} → Term d g
             → Term d (suc g)
WK M = REN (drop id≥) M

VZ : ∀ {d g} → Term d (suc g)
VZ = VAR zero


MREN : ∀ {d d′ g} → d′ ≥ d → Term d g
                  → Term d′ g
MREN e (VAR i)      = VAR i
MREN e (LAM M)      = LAM (MREN e M)
MREN e (APP M N)    = APP (MREN e M) (MREN e N)
MREN e (MVAR i)     = MVAR (renFin e i)
MREN e (BOX M)      = BOX (MREN e M)
MREN e (LETBOX M N) = LETBOX (MREN e M) (MREN (keep e) N)

MWK : ∀ {d g} → Term d g
              → Term (suc d) g
MWK M = MREN (drop id≥) M

MVZ : ∀ {d g} → Term (suc d) g
MVZ = MVAR zero

idMREN : ∀ {d g} → (M : Term d g)
                 → MREN id≥ M ≡ M
idMREN (VAR i)      = refl
idMREN (LAM M)      = LAM & idMREN M
idMREN (APP M N)    = APP & idMREN M ⊗ idMREN N
idMREN (MVAR i)     = MVAR & idrenFin i
idMREN (BOX M)      = BOX & idMREN M
idMREN (LETBOX M N) = LETBOX & idMREN M ⊗ idMREN N

assocMREN : ∀ {d d′ d″ g} → (e₁ : d′ ≥ d) (e₂ : d″ ≥ d′) (M : Term d g)
                          → MREN e₂ (MREN e₁ M) ≡ MREN (e₁ ∘≥ e₂) M
assocMREN e₁ e₂ (VAR i)      = refl
assocMREN e₁ e₂ (LAM M)      = LAM & assocMREN e₁ e₂ M
assocMREN e₁ e₂ (APP M N)    = APP & assocMREN e₁ e₂ M ⊗ assocMREN e₁ e₂ N
assocMREN e₁ e₂ (MVAR i)     = MVAR & assocrenFin e₁ e₂ i
assocMREN e₁ e₂ (BOX M)      = BOX & assocMREN e₁ e₂ M
assocMREN e₁ e₂ (LETBOX M N) = LETBOX & assocMREN e₁ e₂ M ⊗ assocMREN (keep e₁) (keep e₂) N


Terms : Nat → Nat → Nat → Set
Terms d g x = Vec (Term d g) x


RENS : ∀ {d g g′ x} → g′ ≥ g → Terms d g x
                    → Terms d g′ x
RENS e ζ = map (REN e) ζ

WKS : ∀ {d g x} → Terms d g x
                → Terms d (suc g) x
WKS ζ = RENS (drop id≥) ζ

LIFTS : ∀ {d g x} → Terms d g x
                  → Terms d (suc g) (suc x)
LIFTS ζ = WKS ζ , VZ

IDS : ∀ {g d} → Terms d g g
IDS {zero}  = ∙
IDS {suc g} = LIFTS IDS


MRENS : ∀ {d d′ g x} → d′ ≥ d → Terms d g x
                     → Terms d′ g x
MRENS e ζ = map (MREN e) ζ

MWKS : ∀ {d g x} → Terms d g x
                 → Terms (suc d) g x
MWKS ζ = MRENS (drop id≥) ζ

idMRENS : ∀ {d g x} → (ζ : Terms d g x)
                    → MRENS id≥ ζ ≡ ζ
idMRENS ∙       = refl
idMRENS (ζ , M) = _,_ & idMRENS ζ ⊗ idMREN M

assocMRENS : ∀ {d d′ d″ g x} → (e₁ : d′ ≥ d) (e₂ : d″ ≥ d′) (ζ : Terms d g x)
                             → MRENS e₂ (MRENS e₁ ζ) ≡ MRENS (e₁ ∘≥ e₂) ζ
assocMRENS e₁ e₂ ∙       = refl
assocMRENS e₁ e₂ (ζ , M) = _,_ & assocMRENS e₁ e₂ ζ ⊗ assocMREN e₁ e₂ M


SUB : ∀ {d g x} → Terms d g x → Term d x
                → Term d g
SUB ζ (VAR i)      = get ζ i
SUB ζ (LAM M)      = LAM (SUB (LIFTS ζ) M)
SUB ζ (APP M N)    = APP (SUB ζ M) (SUB ζ N)
SUB ζ (MVAR i)     = MVAR i
SUB ζ (BOX M)      = BOX M
SUB ζ (LETBOX M N) = LETBOX (SUB ζ M) (SUB (MWKS ζ) N)

CUT : ∀ {d g} → Term d g → Term d (suc g)
              → Term d g
CUT M N = SUB (IDS , M) N


Term₁ : Nat → Set
Term₁ d = Term d zero

Terms₁ : Nat → Nat → Set
Terms₁ d x = Vec (Term₁ d) x


MRENS₁ : ∀ {d d′ x} → d′ ≥ d → Terms₁ d x
                    → Terms₁ d′ x
MRENS₁ e ζ = map (MREN e) ζ

MWKS₁ : ∀ {d x} → Terms₁ d x
                → Terms₁ (suc d) x
MWKS₁ ζ = MRENS₁ (drop id≥) ζ

MLIFTS₁ : ∀ {d x} → Terms₁ d x
                  → Terms₁ (suc d) (suc x)
MLIFTS₁ ζ = MWKS₁ ζ , MVZ

MIDS₁ : ∀ {d} → Terms₁ d d
MIDS₁ {zero}  = ∙
MIDS₁ {suc d} = MLIFTS₁ MIDS₁

idMRENS₁ : ∀ {d x} → (ζ : Terms₁ d x)
                   → MRENS₁ id≥ ζ ≡ ζ
idMRENS₁ ζ = idMRENS ζ

assocMRENS₁ : ∀ {d d′ d″ x} → (e₁ : d′ ≥ d) (e₂ : d″ ≥ d′) (ζ : Terms₁ d x)
                            → MRENS₁ e₂ (MRENS₁ e₁ ζ) ≡ MRENS₁ (e₁ ∘≥ e₂) ζ
assocMRENS₁ e₁ e₂ ζ = assocMRENS e₁ e₂ ζ


MSUB : ∀ {d g x} → Terms₁ d x → Term x g
                 → Term d g
MSUB ζ (VAR i)      = VAR i
MSUB ζ (LAM M)      = LAM (MSUB ζ M)
MSUB ζ (APP M N)    = APP (MSUB ζ M) (MSUB ζ N)
MSUB ζ (MVAR i)     = SUB ∙ (get ζ i)
MSUB ζ (BOX M)      = BOX (MSUB ζ M)
MSUB ζ (LETBOX M N) = LETBOX (MSUB ζ M) (MSUB (MLIFTS₁ ζ) N)

MCUT : ∀ {d g} → Term₁ d → Term (suc d) g
               → Term d g
MCUT M N = MSUB (MIDS₁ , M) N


UNLAM : ∀ {d g} → Term d g
                → Term d (suc g)
UNLAM M = APP (WK M) VZ

SHL : ∀ {d g} → Term d (suc g)
              → Term (suc d) g
SHL M = APP (LAM (MWK M)) (BOX MVZ)

SHR : ∀ {d g} → Term (suc d) g
              → Term d (suc g)
SHR M = LETBOX VZ (WK M)

EX : ∀ {d g} → Term d (suc (suc g))
             → Term d (suc (suc g))
EX M = APP (APP (WK (WK (LAM (LAM M)))) VZ) (WK VZ)

MEX : ∀ {d g} → Term (suc (suc d)) g
              → Term (suc (suc d)) g
MEX M = SHL (SHL (EX (SHR (SHR M))))


infixr 8 _⊃_
data Prop : Nat → Set
  where
    BASE : ∀ {d} → Prop d
    _⊃_  : ∀ {d} → Prop d → Prop d → Prop d
    [_]_ : ∀ {d} → Term₁ d → Prop d → Prop d


MRENₚ : ∀ {d d′} → d′ ≥ d → Prop d
                 → Prop d′
MRENₚ e BASE      = BASE
MRENₚ e (A ⊃ B)   = MRENₚ e A ⊃ MRENₚ e B
MRENₚ e ([ M ] A) = [ MREN e M ] MRENₚ e A

MWKₚ : ∀ {d} → Prop d
             → Prop (suc d)
MWKₚ A = MRENₚ (drop id≥) A

MSUBₚ : ∀ {d x} → Terms₁ d x → Prop x
                → Prop d
MSUBₚ ζ BASE      = BASE
MSUBₚ ζ (A ⊃ B)   = MSUBₚ ζ A ⊃ MSUBₚ ζ B
MSUBₚ ζ ([ M ] A) = [ MSUB ζ M ] MSUBₚ ζ A

MCUTₚ : ∀ {d} → Term₁ d → Prop (suc d)
              → Prop d
MCUTₚ M A = MSUBₚ (MIDS₁ , M) A

idMRENₚ : ∀ {d} → (A : Prop d)
                → MRENₚ id≥ A ≡ A
idMRENₚ BASE      = refl
idMRENₚ (A ⊃ B)   = _⊃_ & idMRENₚ A ⊗ idMRENₚ B
idMRENₚ ([ M ] A) = [_]_ & idMREN M ⊗ idMRENₚ A

assocMRENₚ : ∀ {d d′ d″} → (e₁ : d′ ≥ d) (e₂ : d″ ≥ d′) (A : Prop d)
                         → MRENₚ e₂ (MRENₚ e₁ A) ≡ MRENₚ (e₁ ∘≥ e₂) A
assocMRENₚ e₁ e₂ BASE      = refl
assocMRENₚ e₁ e₂ (A ⊃ B)   = _⊃_ & assocMRENₚ e₁ e₂ A ⊗ assocMRENₚ e₁ e₂ B
assocMRENₚ e₁ e₂ ([ M ] A) = [_]_ & assocMREN e₁ e₂ M ⊗ assocMRENₚ e₁ e₂ A


infix 7 _true
record Truth (d : Nat) : Set
  where
    constructor _true
    field
      A : Prop d


MRENₜ : ∀ {d d′} → d′ ≥ d → Truth d
                 → Truth d′
MRENₜ e (A true) = MRENₚ e A true

MWKₜ : ∀ {d} → Truth d
             → Truth (suc d)
MWKₜ (A true) = MWKₚ A true

MSUBₜ : ∀ {d x} → Terms₁ d x → Truth x
                → Truth d
MSUBₜ ζ (A true) = MSUBₚ ζ A true

MCUTₜ : ∀ {d} → Term₁ d → Truth (suc d)
              → Truth d
MCUTₜ M (A true) = MCUTₚ M A true

idMRENₜ : ∀ {d} → (Aₜ : Truth d)
                → MRENₜ id≥ Aₜ ≡ Aₜ
idMRENₜ (A true) = _true & idMRENₚ A

assocMRENₜ : ∀ {d d′ d″} → (e₁ : d′ ≥ d) (e₂ : d″ ≥ d′) (Aₜ : Truth d)
                         → MRENₜ e₂ (MRENₜ e₁ Aₜ) ≡ MRENₜ (e₁ ∘≥ e₂) Aₜ
assocMRENₜ e₁ e₂ (A true) = _true & assocMRENₚ e₁ e₂ A


Truths : Nat → Nat → Set
Truths d g = Vec (Truth d) g

MRENSₜ : ∀ {d d′ g} → d′ ≥ d → Truths d g
                    → Truths d′ g
MRENSₜ e Γ = map (MRENₜ e) Γ

MWKSₜ : ∀ {d g} → Truths d g
                → Truths (suc d) g
MWKSₜ Γ = map MWKₜ Γ

idMRENSₜ : ∀ {d g} → (Γ : Truths d g)
                   → MRENSₜ id≥ Γ ≡ Γ
idMRENSₜ ∙        = refl
idMRENSₜ (Γ , Aₜ) = _,_ & idMRENSₜ Γ ⊗ idMRENₜ Aₜ

assocMRENSₜ : ∀ {d d′ d″ g} → (e₁ : d′ ≥ d) (e₂ : d″ ≥ d′) (Γ : Truths d g)
                            → MRENSₜ e₂ (MRENSₜ e₁ Γ) ≡ MRENSₜ (e₁ ∘≥ e₂) Γ
assocMRENSₜ e₁ e₂ ∙        = refl
assocMRENSₜ e₁ e₂ (Γ , Aₜ) = _,_ & assocMRENSₜ e₁ e₂ Γ ⊗ assocMRENₜ e₁ e₂ Aₜ


infix 7 _valid
record Validity (d : Nat) : Set
  where
    constructor _valid
    field
      A : Prop d


MRENᵥ : ∀ {d d′} → d′ ≥ d → Validity d
                 → Validity d′
MRENᵥ e (A valid) = MRENₚ e A valid

MWKᵥ : ∀ {d} → Validity d
             → Validity (suc d)
MWKᵥ (A valid) = MWKₚ A valid

MSUBᵥ : ∀ {d x} → Terms₁ d x → Validity x
                → Validity d
MSUBᵥ ζ (A valid) = MSUBₚ ζ A valid

MCUTᵥ : ∀ {d} → Term₁ d → Validity (suc d)
              → Validity d
MCUTᵥ M (A valid) = MCUTₚ M A valid

idMRENᵥ : ∀ {d} → (Aᵥ : Validity d)
                → MRENᵥ id≥ Aᵥ ≡ Aᵥ
idMRENᵥ (A valid) = _valid & idMRENₚ A

assocMRENᵥ : ∀ {d d′ d″} → (e₁ : d′ ≥ d) (e₂ : d″ ≥ d′) (Aᵥ : Validity d)
                         → MRENᵥ e₂ (MRENᵥ e₁ Aᵥ) ≡ MRENᵥ (e₁ ∘≥ e₂) Aᵥ
assocMRENᵥ e₁ e₂ (A valid) = _valid & assocMRENₚ e₁ e₂ A


data Validities : Nat → Set
  where
    ∙ : Validities zero

    _,_ : ∀ {d} → Validities d → Validity d
                → Validities (suc d)

infix 4 _⊇⟪_⟫_
data _⊇⟪_⟫_ : ∀ {d d′} → Validities d′ → d′ ≥ d → Validities d → Set
  where
    done : ∙ ⊇⟪ done ⟫ ∙

    drop : ∀ {d d′ e} → {Δ : Validities d} {Δ′ : Validities d′} {Aᵥ : Validity d′}
                      → Δ′ ⊇⟪ e ⟫ Δ
                      → Δ′ , Aᵥ ⊇⟪ drop e ⟫ Δ

    keep : ∀ {d d′ e} → {Δ : Validities d} {Δ′ : Validities d′} {Aᵥ : Validity d}
                      → Δ′ ⊇⟪ e ⟫ Δ
                      → Δ′ , MRENᵥ e Aᵥ ⊇⟪ keep e ⟫ Δ , Aᵥ


id⊇◈ : ∀ {d} → {Δ : Validities d}
             → Δ ⊇⟪ id≥ ⟫ Δ
id⊇◈ {Δ = ∙}      = done
id⊇◈ {Δ = Δ , Aᵥ} = {!keep id⊇◈!}


infix 4 _∋⟪_⟫_
data _∋⟪_⟫_ : ∀ {d} → Validities d → Fin d → Validity d → Set
  where
    zero : ∀ {d} → {Δ : Validities d} {Aᵥ : Validity d}
                 → Δ , Aᵥ ∋⟪ zero ⟫ MWKᵥ Aᵥ

    suc : ∀ {d i} → {Δ : Validities d} {Aᵥ : Validity d} {Bᵥ : Validity d}
                  → Δ ∋⟪ i ⟫ Aᵥ
                  → Δ , Bᵥ ∋⟪ suc i ⟫ MWKᵥ Aᵥ


ren∋◈ : ∀ {d d′ e i} → {Δ : Validities d} {Δ′ : Validities d′} {Aᵥ : Validity d}
                     → Δ′ ⊇⟪ e ⟫ Δ → Δ ∋⟪ i ⟫ Aᵥ
                     → Δ′ ∋⟪ renFin e i ⟫ MRENᵥ e Aᵥ
ren∋◈         {Aᵥ = Aᵥ} done     𝒾 rewrite idMRENᵥ Aᵥ = 𝒾
ren∋◈ {e = e} {Aᵥ = Aᵥ} (drop η) 𝒾 rewrite assocMRENᵥ e (drop id≥) Aᵥ ⁻¹ = {!_∋⟪_⟫_.suc (ren∋◈ η 𝒾)!}
ren∋◈                   (keep η) 𝒾 = {!!}


record Derivation (d : Nat) : Set
  where
    constructor [_⊢_⦂_]
    field
      {g} : Nat
      Γ   : Truths d g
      M   : Term d g
      Aₜ  : Truth d


infix 3 _⋙_
data _⋙_ : ∀ {d} → Validities d → Derivation d → Set
  where
    var : ∀ {d g i} → {Δ : Validities d} {Γ : Truths d g}
                       {A : Prop d}
                    → Γ ∋⟨ i ⟩ A true
                    → Δ ⋙ [ Γ ⊢ VAR i ⦂ A true ]

    lam : ∀ {d g M} → {Δ : Validities d} {Γ : Truths d g}
                       {A B : Prop d}
                    → Δ ⋙ [ Γ , A true ⊢ M ⦂ B true ]
                    → Δ ⋙ [ Γ ⊢ LAM M ⦂ A ⊃ B true ]

    app : ∀ {d g M N} → {Δ : Validities d} {Γ : Truths d g}
                         {A B : Prop d}
                      → Δ ⋙ [ Γ ⊢ M ⦂ A ⊃ B true ] → Δ ⋙ [ Γ ⊢ N ⦂ A true ]
                      → Δ ⋙ [ Γ ⊢ APP M N ⦂ B true ]

    mvar : ∀ {d g i} → {Δ : Validities d} {Γ : Truths d g}
                        {A : Prop d}
                     → Δ ∋⟪ i ⟫ A valid
                     → Δ ⋙ [ Γ ⊢ MVAR i ⦂ A true ]

    box : ∀ {d g M} → {Δ : Validities d} {Γ : Truths d g}
                       {A : Prop d}
                    → Δ ⋙ [ ∙ ⊢ M ⦂ A true ]
                    → Δ ⋙ [ Γ ⊢ BOX M ⦂ [ M ] A true ]

    letbox : ∀ {d g M N O} → {Δ : Validities d} {Γ : Truths d g}
                              {A : Prop d} {B : Prop (suc d)}
                           → Δ ⋙ [ Γ ⊢ M ⦂ [ O ] A true ]
                           → Δ , A valid ⋙ [ MWKSₜ Γ ⊢ N ⦂ B true ]
                           → Δ ⋙ [ Γ ⊢ LETBOX M N ⦂ MCUTₚ O B true ]



MRENSₜ⊇ : ∀ {d d′ g g′ e} → {Γ : Truths d g} {Γ′ : Truths d g′}
                          → (f : d′ ≥ d) → Γ′ ⊇⟨ e ⟩ Γ
                          → MRENSₜ f Γ′ ⊇⟨ e ⟩ MRENSₜ f Γ
MRENSₜ⊇         f done     = done
MRENSₜ⊇ {e = e} f (drop η) rewrite rid∘≥ e ⁻¹ = MRENSₜ⊇ f η ∘⊇ drop id⊇
MRENSₜ⊇         f (keep η) = keep (MRENSₜ⊇ f η)

MWKSₜ⊇ : ∀ {d g g′ e} → {Γ : Truths d g} {Γ′ : Truths d g′}
                      → Γ′ ⊇⟨ e ⟩ Γ
                      → MWKSₜ Γ′ ⊇⟨ e ⟩ MWKSₜ Γ
MWKSₜ⊇ η = MRENSₜ⊇ (drop id≥) η


MRENSₜ∋ : ∀ {d d′ g i} → {Γ : Truths d g} {A : Prop d}
                       → (f : d′ ≥ d) → Γ ∋⟨ i ⟩ A true
                       → MRENSₜ f Γ ∋⟨ i ⟩ MRENₚ f A true
MRENSₜ∋ f zero    = zero
MRENSₜ∋ f (suc 𝒾) = suc (MRENSₜ∋ f 𝒾)

MWKSₜ∋ : ∀ {d g i} → {Γ : Truths d g} {A : Prop d}
                   → Γ ∋⟨ i ⟩ A true
                   → MWKSₜ Γ ∋⟨ i ⟩ MWKₚ A true
MWKSₜ∋ 𝒾 = MRENSₜ∋ (drop id≥) 𝒾


ren : ∀ {d g g′ e M} → {Δ : Validities d} {Γ : Truths d g} {Γ′ : Truths d g′}
                        {A : Prop d}
                     → Γ′ ⊇⟨ e ⟩ Γ → Δ ⋙ [ Γ ⊢ M ⦂ A true ]
                     → Δ ⋙ [ Γ′ ⊢ REN e M ⦂ A true ]
ren η (var 𝒾)      = var (ren∋ η 𝒾)
ren η (lam 𝒟)      = lam (ren (keep η) 𝒟)
ren η (app 𝒟 ℰ)    = app (ren η 𝒟) (ren η ℰ)
ren η (mvar 𝒾)     = mvar 𝒾
ren η (box 𝒟)      = box 𝒟
ren η (letbox 𝒟 ℰ) = letbox (ren η 𝒟) (ren (MWKSₜ⊇ η) ℰ)

wk : ∀ {d g M} → {Δ : Validities d} {Γ : Truths d g}
                  {A B : Prop d}
               → Δ ⋙ [ Γ ⊢ M ⦂ A true ]
               → Δ ⋙ [ Γ , B true ⊢ WK M ⦂ A true ]
wk 𝒟 = ren (drop id⊇) 𝒟

vz : ∀ {d g} → {Δ : Validities d} {Γ : Truths d g}
                {A : Prop d}
             → Δ ⋙ [ Γ , A true ⊢ VZ ⦂ A true ]
vz = var zero


mren : ∀ {d d′ g e M} → {Δ : Validities d} {Δ′ : Validities d′} {Γ : Truths d g}
                         {A : Prop d}
                      → Δ′ ⊇⟪ e ⟫ Δ → Δ ⋙ [ Γ ⊢ M ⦂ A true ]
                      → Δ′ ⋙ [ MRENSₜ e Γ ⊢ MREN e M ⦂ MRENₚ e A true ]
mren {e = e} η (var 𝒾)      = var (MRENSₜ∋ e 𝒾)
mren         η (lam 𝒟)      = lam (mren η 𝒟)
mren         η (app 𝒟 ℰ)    = app (mren η 𝒟) (mren η ℰ)
mren         η (mvar 𝒾)     = mvar (ren∋◈ η 𝒾)
mren         η (box 𝒟)      = box (mren η 𝒟)
mren         η (letbox 𝒟 ℰ) = letbox (mren η 𝒟) {!mren (keep η) ℰ!}

mwk : ∀ {d g M} → {Δ : Validities d} {Γ : Truths d g}
                   {A B : Prop d}
                → Δ ⋙ [ Γ ⊢ M ⦂ A true ]
                → Δ , B valid ⋙ [ MWKSₜ Γ ⊢ MWK M ⦂ MWKₚ A true ]
mwk 𝒟 = mren (drop id⊇◈) 𝒟

mvz : ∀ {d g} → {Δ : Validities d} {Γ : Truths d g}
                 {A : Prop d}
              → Δ , A valid ⋙ [ MWKSₜ Γ ⊢ MVZ ⦂ MWKₚ A true ]
mvz = mvar zero


-- -- -- record Derivations (d : Nat) : Set
-- -- --   where
-- -- --     constructor [_⊢⋆_⦂_]
-- -- --     field
-- -- --       {g} : Nat
-- -- --       {x} : Nat
-- -- --       Γ   : Truths g
-- -- --       ζ   : Terms d g x
-- -- --       Ξ   : Truths x


-- -- -- zap : ∀ {d g x} → Truths g → Terms d g x → Truths x
-- -- --                 → Vec (Derivation d) x
-- -- -- zap Γ ∙       ∙            = ∙
-- -- -- zap Γ (ζ , M) (Ξ , A true) = zap Γ ζ Ξ , [ Γ ⊢ M ⦂ A true ]

-- -- -- zap∋ : ∀ {d g x i A} → {Γ : Truths g}
-- -- --                         {ζ : Terms d g x} {Ξ : Truths x}
-- -- --                      → Ξ ∋⟨ i ⟩ A true
-- -- --                      → zap Γ ζ Ξ ∋⟨ i ⟩ [ Γ ⊢ get ζ i ⦂ A true ]
-- -- -- zap∋ {ζ = ζ , M} {Ξ , A true} zero    = zero
-- -- -- zap∋ {ζ = ζ , N} {Ξ , B true} (suc 𝒾) = suc (zap∋ 𝒾)


-- -- -- infix 3 _⋙⋆_
-- -- -- _⋙⋆_ : ∀ {d} → Validities d → Derivations d → Set
-- -- -- Δ ⋙⋆ [ Γ ⊢⋆ ζ ⦂ Ξ ] = All (Δ ⋙_) (zap Γ ζ Ξ)


-- -- -- rens : ∀ {d g g′ e x} → {Δ : Validities d} {Γ : Truths g} {Γ′ : Truths g′}
-- -- --                          {ζ : Terms d g x} {Ξ : Truths x}
-- -- --                       → Γ′ ⊇⟨ e ⟩ Γ → Δ ⋙⋆ [ Γ ⊢⋆ ζ ⦂ Ξ ]
-- -- --                       → Δ ⋙⋆ [ Γ′ ⊢⋆ RENS e ζ ⦂ Ξ ]
-- -- -- rens {ζ = ∙}     {∙}          η ∙       = ∙
-- -- -- rens {ζ = ζ , M} {Ξ , A true} η (ξ , 𝒟) = rens η ξ , ren η 𝒟
-- -- -- -- NOTE: Equivalent to
-- -- -- -- rens η ξ = mapAll (ren η) ξ

-- -- -- wks : ∀ {d g x A} → {Δ : Validities d} {Γ : Truths g}
-- -- --                      {ζ : Terms d g x} {Ξ : Truths x}
-- -- --                   → Δ ⋙⋆ [ Γ ⊢⋆ ζ ⦂ Ξ ]
-- -- --                   → Δ ⋙⋆ [ Γ , A true ⊢⋆ WKS ζ ⦂ Ξ ]
-- -- -- wks ξ = rens (drop id⊇) ξ

-- -- -- lifts : ∀ {d g x A} → {Δ : Validities d} {Γ : Truths g}
-- -- --                        {ζ : Terms d g x} {Ξ : Truths x}
-- -- --                     → Δ ⋙⋆ [ Γ ⊢⋆ ζ ⦂ Ξ ]
-- -- --                     → Δ ⋙⋆ [ Γ , A true ⊢⋆ LIFTS ζ ⦂ Ξ , A true ]
-- -- -- lifts ξ = wks ξ , vz

-- -- -- ids : ∀ {d g} → {Δ : Validities d} {Γ : Truths g}
-- -- --               → Δ ⋙⋆ [ Γ ⊢⋆ IDS ⦂ Γ ]
-- -- -- ids {Γ = ∙}          = ∙
-- -- -- ids {Γ = Γ , A true} = lifts ids


-- -- -- mrens : ∀ {d d′ g e x} → {Δ : Validities d} {Δ′ : Validities d′} {Γ : Truths g}
-- -- --                           {ζ : Terms d g x} {Ξ : Truths x}
-- -- --                        → Δ′ ⊇⟨ e ⟩ Δ → Δ ⋙⋆ [ Γ ⊢⋆ ζ ⦂ Ξ ]
-- -- --                        → Δ′ ⋙⋆ [ Γ ⊢⋆ MRENS e ζ ⦂ Ξ ]
-- -- -- mrens {ζ = ∙}     {∙}          η ∙       = ∙
-- -- -- mrens {ζ = ζ , M} {Ξ , A true} η (ξ , 𝒟) = mrens η ξ , mren η 𝒟
-- -- -- -- NOTE: Equivalent to
-- -- -- -- mrens η ξ = mapAll (mren η) ξ

-- -- -- mwks : ∀ {d g x A} → {Δ : Validities d} {Γ : Truths g}
-- -- --                       {ζ : Terms d g x} {Ξ : Truths x}
-- -- --                    → Δ ⋙⋆ [ Γ ⊢⋆ ζ ⦂ Ξ ]
-- -- --                    → Δ , A valid ⋙⋆ [ Γ ⊢⋆ MWKS ζ ⦂ Ξ ]
-- -- -- mwks ξ = mrens (drop id⊇) ξ


-- -- -- sub : ∀ {d g x M A} → {Δ : Validities d} {Γ : Truths g}
-- -- --                        {ζ : Terms d g x} {Ξ : Truths x}
-- -- --                     → Δ ⋙⋆ [ Γ ⊢⋆ ζ ⦂ Ξ ] → Δ ⋙ [ Ξ ⊢ M ⦂ A true ]
-- -- --                     → Δ ⋙ [ Γ ⊢ SUB ζ M ⦂ A true ]
-- -- -- sub ξ (var 𝒾)      = lookup ξ (zap∋ 𝒾)
-- -- -- sub ξ (lam 𝒟)      = lam (sub (lifts ξ) 𝒟)
-- -- -- sub ξ (app 𝒟 ℰ)    = app (sub ξ 𝒟) (sub ξ ℰ)
-- -- -- sub ξ (mvar 𝒾)     = mvar 𝒾
-- -- -- sub ξ (box 𝒟)      = box 𝒟
-- -- -- sub ξ (letbox 𝒟 ℰ) = letbox (sub ξ 𝒟) (sub (mwks ξ) ℰ)

-- -- -- cut : ∀ {d g M N A B} → {Δ : Validities d} {Γ : Truths g}
-- -- --                       → Δ ⋙ [ Γ ⊢ M ⦂ A true ] → Δ ⋙ [ Γ , A true ⊢ N ⦂ B true ]
-- -- --                       → Δ ⋙ [ Γ ⊢ CUT M N ⦂ B true ]
-- -- -- cut 𝒟 ℰ = sub (ids , 𝒟) ℰ


-- -- -- record Derivation₁ (d : Nat) : Set
-- -- --   where
-- -- --     constructor [∙⊢₁_⦂_]
-- -- --     field
-- -- --       M  : Term₁ d
-- -- --       Aᵥ : Validity

-- -- -- record Derivations₁ (d : Nat) : Set
-- -- --   where
-- -- --     constructor [∙⊢⋆₁_⦂_]
-- -- --     field
-- -- --       {x} : Nat
-- -- --       ζ   : Terms₁ d x
-- -- --       Ξ   : Validities x


-- -- -- zap₁ : ∀ {d x} → Terms₁ d x → Validities x
-- -- --                → Vec (Derivation₁ d) x
-- -- -- zap₁ ∙       ∙             = ∙
-- -- -- zap₁ (ζ , M) (Ξ , A valid) = zap₁ ζ Ξ , [∙⊢₁ M ⦂ A valid ]

-- -- -- zap∋₁ : ∀ {d x i A} → {ζ : Terms₁ d x} {Ξ : Validities x}
-- -- --                     → Ξ ∋⟨ i ⟩ A valid
-- -- --                     → zap₁ ζ Ξ ∋⟨ i ⟩ [∙⊢₁ get ζ i ⦂ A valid ]
-- -- -- zap∋₁ {ζ = ζ , M} {Ξ , A valid} zero    = zero
-- -- -- zap∋₁ {ζ = ζ , N} {Ξ , B valid} (suc 𝒾) = suc (zap∋₁ 𝒾)


-- -- -- infix 3 _⋙₁_
-- -- -- _⋙₁_ : ∀ {d} → Validities d → Derivation₁ d → Set
-- -- -- Δ ⋙₁ [∙⊢₁ M ⦂ A valid ] = Δ ⋙ [ ∙ ⊢ M ⦂ A true ]

-- -- -- infix 3 _⋙⋆₁_
-- -- -- _⋙⋆₁_ : ∀ {d} → Validities d → Derivations₁ d → Set
-- -- -- Δ ⋙⋆₁ [∙⊢⋆₁ ζ ⦂ Ξ ] = All (Δ ⋙₁_) (zap₁ ζ Ξ)


-- -- -- mrens₁ : ∀ {d d′ e x} → {Δ : Validities d} {Δ′ : Validities d′} {ζ : Terms₁ d x} {Ξ : Validities x}
-- -- --                       → Δ′ ⊇⟨ e ⟩ Δ → Δ ⋙⋆₁ [∙⊢⋆₁ ζ ⦂ Ξ ]
-- -- --                       → Δ′ ⋙⋆₁ [∙⊢⋆₁ MRENS₁ e ζ ⦂ Ξ ]
-- -- -- mrens₁ {ζ = ∙}     {∙}           η ∙       = ∙
-- -- -- mrens₁ {ζ = ζ , M} {Ξ , A valid} η (ξ , 𝒟) = mrens₁ η ξ , mren η 𝒟
-- -- -- -- NOTE: Equivalent to
-- -- -- -- mrens₁ η ξ = mapAll (mren η) ξ

-- -- -- mwks₁ : ∀ {d x A} → {Δ : Validities d} {ζ : Terms₁ d x} {Ξ : Validities x}
-- -- --                   → Δ ⋙⋆₁ [∙⊢⋆₁ ζ ⦂ Ξ ]
-- -- --                   → Δ , A valid ⋙⋆₁ [∙⊢⋆₁ MWKS₁ ζ ⦂ Ξ ]
-- -- -- mwks₁ ξ = mrens₁ (drop id⊇) ξ

-- -- -- mlifts₁ : ∀ {d x A} → {Δ : Validities d} {ζ : Terms₁ d x} {Ξ : Validities x}
-- -- --                     → Δ ⋙⋆₁ [∙⊢⋆₁ ζ ⦂ Ξ ]
-- -- --                     → Δ , A valid ⋙⋆₁ [∙⊢⋆₁ MLIFTS₁ ζ ⦂ Ξ , A valid ]
-- -- -- mlifts₁ ξ = mwks₁ ξ , mvz

-- -- -- mids₁ : ∀ {d} → {Δ : Validities d}
-- -- --               → Δ ⋙⋆₁ [∙⊢⋆₁ MIDS₁ ⦂ Δ ]
-- -- -- mids₁ {Δ = ∙}           = ∙
-- -- -- mids₁ {Δ = Δ , A valid} = mlifts₁ mids₁


-- -- -- msub : ∀ {d g x M A} → {Δ : Validities d} {Γ : Truths g}
-- -- --                         {ζ : Terms₁ d x} {Ξ : Validities x}
-- -- --                      → Δ ⋙⋆₁ [∙⊢⋆₁ ζ ⦂ Ξ ] → Ξ ⋙ [ Γ ⊢ M ⦂ A true ]
-- -- --                      → Δ ⋙ [ Γ ⊢ MSUB ζ M ⦂ A true ]
-- -- -- msub ξ (var 𝒾)      = var 𝒾
-- -- -- msub ξ (lam 𝒟)      = lam (msub ξ 𝒟)
-- -- -- msub ξ (app 𝒟 ℰ)    = app (msub ξ 𝒟) (msub ξ ℰ)
-- -- -- msub ξ (mvar 𝒾)     = sub ∙ (lookup ξ (zap∋₁ 𝒾))
-- -- -- msub ξ (box 𝒟)      = box (msub ξ 𝒟)
-- -- -- msub ξ (letbox 𝒟 ℰ) = letbox (msub ξ 𝒟) (msub (mlifts₁ ξ) ℰ)

-- -- -- mcut : ∀ {d g M N A B} → {Δ : Validities d} {Γ : Truths g}
-- -- --                        → Δ ⋙₁ [∙⊢₁ M ⦂ A valid ] → Δ , A valid ⋙ [ Γ ⊢ N ⦂ B true ]
-- -- --                        → Δ ⋙ [ Γ ⊢ MCUT M N ⦂ B true ]
-- -- -- mcut 𝒟 ℰ = msub (mids₁ , 𝒟) ℰ


-- -- -- unlam : ∀ {d g M A B} → {Δ : Validities d} {Γ : Truths g}
-- -- --                       → Δ ⋙ [ Γ ⊢ M ⦂ A ⊃ B true ]
-- -- --                       → Δ ⋙ [ Γ , A true ⊢ UNLAM M ⦂ B true ]
-- -- -- unlam 𝒟 = app (wk 𝒟) vz

-- -- -- -- shl : ∀ {d g M A B} → {Δ : Validities d} {Γ : Truths g}
-- -- -- --                     → Δ ⋙ [ Γ , □ A true ⊢ M ⦂ B true ]
-- -- -- --                     → Δ , A valid ⋙ [ Γ ⊢ SHL M ⦂ B true ]
-- -- -- -- shl 𝒟 = app (lam (mwk 𝒟)) (box mvz)

-- -- -- -- shr : ∀ {d g M A B} → {Δ : Validities d} {Γ : Truths g}
-- -- -- --                     → Δ , A valid ⋙ [ Γ ⊢ M ⦂ B true ]
-- -- -- --                     → Δ ⋙ [ Γ , □ A true ⊢ SHR M ⦂ B true ]
-- -- -- -- shr 𝒟 = letbox vz (wk 𝒟)

-- -- -- -- ex : ∀ {d g M A B C} → {Δ : Validities d} {Γ : Truths g}
-- -- -- --                      → Δ ⋙ [ Γ , A true , B true ⊢ M ⦂ C true ]
-- -- -- --                      → Δ ⋙ [ Γ , B true , A true ⊢ EX M ⦂ C true ]
-- -- -- -- ex 𝒟 = app (app (wk (wk (lam (lam 𝒟)))) vz) (wk vz)

-- -- -- -- mex : ∀ {d g M A B C} → {Δ : Validities d} {Γ : Truths g}
-- -- -- --                       → Δ , A valid , B valid ⋙ [ Γ ⊢ M ⦂ C true ]
-- -- -- --                       → Δ , B valid , A valid ⋙ [ Γ ⊢ MEX M ⦂ C true ]
-- -- -- -- mex 𝒟 = shl (shl (ex (shr (shr 𝒟))))
