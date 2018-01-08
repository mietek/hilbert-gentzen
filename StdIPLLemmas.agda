module StdIPLLemmas where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open GetAllList
open import AllListLemmas
open GetsAllList
open import StdIPL


--------------------------------------------------------------------------------
{-
                             ren id⊇ 𝒟 ≡ 𝒟                                      id-ren
                      ren (η₁ ∘⊇ η₂) 𝒟 ≡ (ren η₂ ∘ ren η₁) 𝒟                    comp-ren
                        ren (drop η) 𝒟 ≡ (wk ∘ ren η) 𝒟                         -- comp-wk-ren-drop
                 (ren (keep η) ∘ wk) 𝒟 ≡ (wk ∘ ren η) 𝒟                         comp-wk-ren-keep

                            rens id⊇ ξ ≡ ξ                                      id-rens
                     rens (η₁ ∘⊇ η₂) ξ ≡ (rens η₂ ∘ rens η₁) ξ                  comp-rens
                       rens (drop η) ξ ≡ (wks ∘ rens η) ξ                       -- comp-wks-rens-drop
               (rens (keep η) ∘ wks) ξ ≡ (wks ∘ rens η) ξ                       comp-wks-rens-keep
             (rens (keep η) ∘ lifts) ξ ≡ (lifts ∘ rens η) ξ                     comp-lifts-rens

                      get (rens η ξ) 𝒾 ≡ (ren η ∘ get ξ) 𝒾                      comp-ren-get
                             get ids 𝒾 ≡ var 𝒾                                  var-id-get

                   gets (rens η₁ ξ) η₂ ≡ (rens η₁ ∘ gets ξ) η₂                  comp-rens-gets
               gets (lifts ξ) (keep η) ≡ (lifts ∘ gets ξ) η                     comp-lifts-gets

                      get (subs ξ ψ) 𝒾 ≡ (sub ξ ∘ get ψ) 𝒾                      comp-sub-get
                     gets (subs ξ ψ) η ≡ (subs ξ ∘ gets ψ) η                    -- comp-subs-gets

                      sub (gets ξ η) 𝒟 ≡ (sub ξ ∘ ren η) 𝒟                      comp-sub-ren
                     subs (gets ξ η) ψ ≡ (subs ξ ∘ rens η) ψ                    -- comp-subs-rens

                  subs (ξ , 𝒟) (wks ψ) ≡ subs ξ ψ                               expand-subs

                      sub (rens η ξ) 𝒟 ≡ (ren η ∘ sub ξ) 𝒟                      comp-ren-sub
                     subs (rens η ξ) ψ = (rens η ∘ subs ξ) ψ                    comp-rens-subs
              subs (lifts ξ) (lifts ψ) ≡ (lifts ∘ subs ξ) ψ                     comp-lifts-subs

                             sub ids 𝒟 ≡ 𝒟                                      id-sub
                      sub (subs ξ ψ) 𝒟 ≡ (sub ξ ∘ sub ψ) 𝒟                      comp-sub
                            subs ids ξ ≡ ξ                                      lid-subs
                            subs ξ ids ≡ ξ                                      rid-subs
                     subs (subs ξ ψ) φ ≡ subs ξ (subs ψ φ)                      assoc-subs
-}
--------------------------------------------------------------------------------


id-ren : ∀ {Γ A} → (𝒟 : Γ ⊢ A true)
                 → ren id⊇ 𝒟 ≡ 𝒟
id-ren (var 𝒾)   = var & id-ren∋ 𝒾
id-ren (lam 𝒟)   = lam & id-ren 𝒟
id-ren (app 𝒟 ℰ) = app & id-ren 𝒟 ⊗ id-ren ℰ


comp-ren : ∀ {Γ Γ′ Γ″ A} → (η₁ : Γ′ ⊇ Γ) (η₂ : Γ″ ⊇ Γ′) (𝒟 : Γ ⊢ A true)
                         → ren (η₁ ∘⊇ η₂) 𝒟 ≡ (ren η₂ ∘ ren η₁) 𝒟
comp-ren η₁ η₂ (var 𝒾)   = var & comp-ren∋ η₁ η₂ 𝒾
comp-ren η₁ η₂ (lam 𝒟)   = lam & comp-ren (keep η₁) (keep η₂) 𝒟
comp-ren η₁ η₂ (app 𝒟 ℰ) = app & comp-ren η₁ η₂ 𝒟 ⊗ comp-ren η₁ η₂ ℰ


Ren : ∀ {A} → Presheaf (_⊢ A true) ren
Ren = record
        { idℱ   = funext! id-ren
        ; compℱ = \ η₁ η₂ → funext! (comp-ren η₁ η₂)
        }


-- NOTE: Unused.

-- comp-wk-ren-drop : ∀ {Γ Γ′ A B} → (η : Γ′ ⊇ Γ) (𝒟 : Γ ⊢ A true)
--                                 → ren (drop {A = B} η) 𝒟 ≡ (wk ∘ ren η) 𝒟
-- comp-wk-ren-drop η 𝒟 = (\ η′ → ren (drop η′) 𝒟) & rid∘⊇ η ⁻¹
--                      ⋮ comp-ren η (drop id⊇) 𝒟


comp-wk-ren-keep : ∀ {Γ Γ′ A B} → (η : Γ′ ⊇ Γ) (𝒟 : Γ ⊢ A true)
                                → (ren (keep {A = B} η) ∘ wk) 𝒟 ≡ (wk ∘ ren η) 𝒟
comp-wk-ren-keep η 𝒟 = comp-ren (drop id⊇) (keep η) 𝒟 ⁻¹
                     ⋮ (\ η′ → ren (drop η′) 𝒟) & (lid∘⊇ η ⋮ rid∘⊇ η ⁻¹)
                     ⋮ comp-ren η (drop id⊇) 𝒟


--------------------------------------------------------------------------------


id-rens : ∀ {Γ Ξ} → (ξ : Γ ⊢⋆ Ξ)
                  → rens id⊇ ξ ≡ ξ
id-rens ∙       = refl
id-rens (ξ , 𝒟) = _,_ & id-rens ξ ⊗ id-ren 𝒟


comp-rens : ∀ {Γ Γ′ Γ″ Ξ} → (η₁ : Γ′ ⊇ Γ) (η₂ : Γ″ ⊇ Γ′) (ξ : Γ ⊢⋆ Ξ)
                          → rens (η₁ ∘⊇ η₂) ξ ≡ (rens η₂ ∘ rens η₁) ξ
comp-rens η₁ η₂ ∙       = refl
comp-rens η₁ η₂ (ξ , 𝒟) = _,_ & comp-rens η₁ η₂ ξ ⊗ comp-ren η₁ η₂ 𝒟


Rens : ∀ {Ξ} → Presheaf (_⊢⋆ Ξ) rens
Rens = record
         { idℱ   = funext! id-rens
         ; compℱ = \ η₁ η₂ → funext! (comp-rens η₁ η₂)
         }


-- NOTE: Unused.

-- comp-wks-rens-drop : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ)
--                                   → rens (drop {A = A} η) ξ ≡ (wks ∘ rens η) ξ
-- comp-wks-rens-drop η ∙       = refl
-- comp-wks-rens-drop η (ξ , 𝒟) = _,_ & comp-wks-rens-drop η ξ ⊗ comp-wk-ren-drop η 𝒟


comp-wks-rens-keep : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ)
                                  → (rens (keep {A = A} η) ∘ wks) ξ ≡ (wks ∘ rens η) ξ
comp-wks-rens-keep η ∙       = refl
comp-wks-rens-keep η (ξ , 𝒟) = _,_ & comp-wks-rens-keep η ξ ⊗ comp-wk-ren-keep η 𝒟


comp-lifts-rens : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ)
                               → (rens (keep {A = A} η) ∘ lifts) ξ ≡ (lifts ∘ rens η) ξ
comp-lifts-rens η ξ = (_, vz) & comp-wks-rens-keep η ξ


--------------------------------------------------------------------------------


comp-ren-get : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ) (𝒾 : Ξ ∋ A true)
                            → get (rens η ξ) 𝒾 ≡ (ren η ∘ get ξ) 𝒾
comp-ren-get η (ξ , 𝒟) zero    = refl
comp-ren-get η (ξ , 𝒟) (suc 𝒾) = comp-ren-get η ξ 𝒾


var-id-get : ∀ {Γ A} → (𝒾 : Γ ∋ A true)
                     → get ids 𝒾 ≡ var 𝒾
var-id-get zero    = refl
var-id-get (suc 𝒾) = comp-ren-get (drop id⊇) ids 𝒾
                   ⋮ wk & var-id-get 𝒾
                   ⋮ (\ 𝒾′ → var (suc 𝒾′)) & id-ren∋ 𝒾


--------------------------------------------------------------------------------


comp-rens-gets : ∀ {Γ Γ′ Ξ Ξ′} → (η₁ : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ′) (η₂ : Ξ′ ⊇ Ξ)
                               → gets (rens η₁ ξ) η₂ ≡ (rens η₁ ∘ gets ξ) η₂
comp-rens-gets η₁ ∙       done      = refl
comp-rens-gets η₁ (ξ , 𝒟) (drop η₂) = comp-rens-gets η₁ ξ η₂
comp-rens-gets η₁ (ξ , 𝒟) (keep η₂) = (_, ren η₁ 𝒟) & comp-rens-gets η₁ ξ η₂


comp-lifts-gets : ∀ {Γ Ξ Ξ′ A} → (ξ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ)
                               → gets (lifts {A} ξ) (keep η) ≡ (lifts ∘ gets ξ) η
comp-lifts-gets ξ η = (_, vz) & comp-rens-gets (drop id⊇) ξ η


--------------------------------------------------------------------------------


comp-sub-get : ∀ {Γ Ξ Ψ A} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ) (𝒾 : Ψ ∋ A true)
                           → get (subs ξ ψ) 𝒾 ≡ (sub ξ ∘ get ψ) 𝒾
comp-sub-get ξ (ψ , 𝒟) zero    = refl
comp-sub-get ξ (ψ , ℰ) (suc 𝒾) = comp-sub-get ξ ψ 𝒾


-- NOTE: Unused.

-- comp-subs-gets : ∀ {Γ Ξ Ψ Ψ′} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ′) (η : Ψ′ ⊇ Ψ)
--                               → gets (subs ξ ψ) η ≡ (subs ξ ∘ gets ψ) η
-- comp-subs-gets ξ ∙       done     = refl
-- comp-subs-gets ξ (ψ , 𝒟) (drop η) = comp-subs-gets ξ ψ η
-- comp-subs-gets ξ (ψ , 𝒟) (keep η) = (_, sub ξ 𝒟) & comp-subs-gets ξ ψ η


--------------------------------------------------------------------------------


comp-sub-ren : ∀ {Γ Ξ Ξ′ A} → (ξ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (𝒟 : Ξ ⊢ A true)
                            → sub (gets ξ η) 𝒟 ≡ (sub ξ ∘ ren η) 𝒟
comp-sub-ren ξ η (var 𝒾)   = comp-get-ren∋ ξ η 𝒾
comp-sub-ren ξ η (lam 𝒟)   = lam & ( (\ ξ′ → sub ξ′ 𝒟) & comp-lifts-gets ξ η ⁻¹
                                   ⋮ comp-sub-ren (lifts ξ) (keep η) 𝒟
                                   )
comp-sub-ren ξ η (app 𝒟 ℰ) = app & comp-sub-ren ξ η 𝒟 ⊗ comp-sub-ren ξ η ℰ


-- NOTE: Unused.

-- comp-subs-rens : ∀ {Γ Ξ Ξ′ Ψ} → (ξ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (ψ : Ξ ⊢⋆ Ψ)
--                               → subs (gets ξ η) ψ ≡ (subs ξ ∘ rens η) ψ
-- comp-subs-rens ξ η ∙       = refl
-- comp-subs-rens ξ η (ψ , 𝒟) = _,_ & comp-subs-rens ξ η ψ ⊗ comp-sub-ren ξ η 𝒟


--------------------------------------------------------------------------------


-- TODO: Better name?

expand-subs : ∀ {Γ Ξ Ψ A} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ) (𝒟 : Γ ⊢ A true)
                          → subs (ξ , 𝒟) (wks ψ) ≡ subs ξ ψ
expand-subs ξ ∙       𝒟 = refl
expand-subs ξ (ψ , ℰ) 𝒟 = _,_ & expand-subs ξ ψ 𝒟
                              ⊗ ( comp-sub-ren (ξ , 𝒟) (drop id⊇) ℰ ⁻¹
                                ⋮ (\ ξ′ → sub ξ′ ℰ) & id-gets ξ
                                )


--------------------------------------------------------------------------------


comp-ren-sub : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ) (𝒟 : Ξ ⊢ A true)
                            → sub (rens η ξ) 𝒟 ≡ (ren η ∘ sub ξ) 𝒟
comp-ren-sub η ξ (var 𝒾)   = comp-ren-get η ξ 𝒾
comp-ren-sub η ξ (lam 𝒟)   = lam & ( (\ ξ′ → sub ξ′ 𝒟) & comp-lifts-rens η ξ ⁻¹
                                   ⋮ comp-ren-sub (keep η) (lifts ξ) 𝒟
                                   )
comp-ren-sub η ξ (app 𝒟 ℰ) = app & comp-ren-sub η ξ 𝒟 ⊗ comp-ren-sub η ξ ℰ


comp-rens-subs : ∀ {Γ Γ′ Ξ Ψ} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ)
                              → subs (rens η ξ) ψ ≡ (rens η ∘ subs ξ) ψ
comp-rens-subs η ξ ∙       = refl
comp-rens-subs η ξ (ψ , 𝒟) = _,_ & comp-rens-subs η ξ ψ ⊗ comp-ren-sub η ξ 𝒟


comp-lifts-subs : ∀ {Γ Ξ Ψ A} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ)
                              → subs (lifts {A} ξ) (lifts ψ) ≡ (lifts ∘ subs ξ) ψ
comp-lifts-subs ξ ψ = (_, vz) & ( expand-subs (wks ξ) ψ vz
                                ⋮ comp-rens-subs (drop id⊇) ξ ψ
                                )


--------------------------------------------------------------------------------


id-sub : ∀ {Γ A} → (𝒟 : Γ ⊢ A true)
                 → sub ids 𝒟 ≡ 𝒟
id-sub (var 𝒾)   = var-id-get 𝒾
id-sub (lam 𝒟)   = lam & id-sub 𝒟
id-sub (app 𝒟 ℰ) = app & id-sub 𝒟 ⊗ id-sub ℰ


comp-sub : ∀ {Γ Ξ Ψ A} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ) (𝒟 : Ψ ⊢ A true)
                       → sub (subs ξ ψ) 𝒟 ≡ (sub ξ ∘ sub ψ) 𝒟
comp-sub ξ ψ (var 𝒾)   = comp-sub-get ξ ψ 𝒾
comp-sub ξ ψ (lam 𝒟)   = lam & ( (\ ξ′ → sub ξ′ 𝒟) & comp-lifts-subs ξ ψ ⁻¹
                               ⋮ comp-sub (lifts ξ) (lifts ψ) 𝒟
                               )
comp-sub ξ ψ (app 𝒟 ℰ) = app & comp-sub ξ ψ 𝒟 ⊗ comp-sub ξ ψ ℰ


lid-subs : ∀ {Γ Ξ} → (ξ : Γ ⊢⋆ Ξ)
                   → subs ids ξ ≡ ξ
lid-subs ∙       = refl
lid-subs (ξ , 𝒟) = _,_ & lid-subs ξ ⊗ id-sub 𝒟


rid-subs : ∀ {Γ Ξ} → (ξ : Γ ⊢⋆ Ξ)
                   → subs ξ ids ≡ ξ
rid-subs ∙       = refl
rid-subs (ξ , 𝒟) = (_, 𝒟) & ( expand-subs ξ ids 𝒟
                            ⋮ rid-subs ξ
                            )


assoc-subs : ∀ {Γ Ξ Ψ Φ} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ) (φ : Ψ ⊢⋆ Φ)
                         → subs (subs ξ ψ) φ ≡ subs ξ (subs ψ φ)
assoc-subs ξ ψ ∙       = refl
assoc-subs ξ ψ (φ , 𝒟) = _,_ & assoc-subs ξ ψ φ ⊗ comp-sub ξ ψ 𝒟


instance
  IPL : Category Context _⊢⋆_
  IPL = record
          { id     = ids
          ; _∘_    = flip subs
          ; lid∘   = rid-subs
          ; rid∘   = lid-subs
          ; assoc∘ = \ ξ₁ ξ₂ ξ₃ → assoc-subs ξ₃ ξ₂ ξ₁ ⁻¹
          }


Sub : ∀ {A} → Presheaf (_⊢ A true) sub
Sub = record
        { idℱ   = funext! id-sub
        ; compℱ = \ ξ₁ ξ₂ → funext! (comp-sub ξ₂ ξ₁)
        }


--------------------------------------------------------------------------------
