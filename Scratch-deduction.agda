
-- --------------------------------------------------------------------------

-- Deduction theorem

ded⊃ⁿ : ∀{A B n m} {𝐱 : Vars n} {𝐭 : Tms n} {Γ : Cx m}
      → Γ , 𝑣ⁿ 𝐱 ∶ A ⊢ *ⁿ 𝐭 ∶ B
      → Γ ⊢ 𝜆ⁿ 𝐱 · 𝐭 ∶ (A ⊃ B)
ded⊃ⁿ {𝐱 = 𝐱} {𝐭 = 𝐭} = M𝜆ⁿ {𝐱 = 𝐱} {𝐭 = 𝐭}


ded⊂⁰ : ∀{A B m} {Γ : Cx m}
      → Γ ⊢ A ⊃ B
      → Γ , A ⊢ B
ded⊂⁰ D = M∘⁰ (wk⊢ (drop Γ≲Γ) D) (M𝑣⁰ Z)


{-
foo¹ : ∀{A B x t m} {Γ : Cx m}
     → Γ ⊢ 𝜆 x · t ∶ (A ⊃ B)
     → Γ , 𝑣 x ∶ A ⊢ 𝜆 x · t ∶ (A ⊃ B)
foo¹ D = wk⊢ (drop Γ≲Γ) D


bar¹ : ∀{A x m} {Γ : Cx m}
     → Γ , 𝑣 x ∶ A ⊢ 𝑣 x ∶ A
bar¹ = M𝑣 Z


ded⊂¹ : ∀{A B x t m} {Γ : Cx m}
      → Γ ⊢ 𝜆 x · t ∶ (A ⊃ B)
      → Γ , 𝑣 x ∶ A ⊢ t ∶ B
ded⊂¹ D = M∘ (foo¹ D) bar¹


fooⁿ : ∀{A B n m} {𝐱 : Vars n} {𝐭 : Tms n} {Γ : Cx m}
     → Γ ⊢ 𝜆ⁿ 𝐱 · 𝐭 ∶ (A ⊃ B)
     → Γ , 𝑣ⁿ 𝐱 ∶ A ⊢ 𝜆ⁿ 𝐱 · 𝐭 ∶ (A ⊃ B)
fooⁿ {𝐭 = 𝐭} D = wk⊢ (drop Γ≲Γ) D


barⁿ : ∀{A n m} {𝐱 : Vars n} {Γ : Cx m}
     → Γ , 𝑣ⁿ 𝐱 ∶ A ⊢ 𝑣ⁿ 𝐱 ∶ A
barⁿ {𝐱 = 𝐱} = M𝑣ⁿ {𝐱 = 𝐱} Z


ded⊂ⁿ : ∀{A B n m} {𝐱 : Vars n} {𝐭 : Tms n} {Γ : Cx m}
      → Γ ⊢ 𝜆ⁿ 𝐱 · 𝐭 ∶ (A ⊃ B)
      → Γ , 𝑣ⁿ 𝐱 ∶ A ⊢ *ⁿ 𝐭 ∶ B
ded⊂ⁿ {𝐱 = 𝐱} {𝐭 = 𝐭} D = M∘ⁿ (fooⁿ {𝐱 = 𝐱} {𝐭 = 𝐭} D) (barⁿ {𝐱 = 𝐱})  -- XXX: Prove this!
-}
