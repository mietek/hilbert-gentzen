module A201602.Scratch-encodings2 where

{-

-- --------------------------------------------------------------------------
--
-- Church encoding of true and false (macros/schemas)


⌜Bool⌝ : Ty → Ty
⌜Bool⌝ A = A ⊃ A ⊃ A


⌜true⌝ : ∀{A} → ⊩ ⌜Bool⌝ A
⌜true⌝ = 𝝀 𝝀 𝒗 𝟏

⌜false⌝ : ∀{A} → ⊩ ⌜Bool⌝ A
⌜false⌝ = 𝝀 𝝀 𝒗 𝟎


-- --------------------------------------------------------------------------
--
-- Church encoding of natural numbers (macros/schemas)


⌜ℕ⌝ : Ty → Ty
⌜ℕ⌝ A = (A ⊃ A) ⊃ A ⊃ A


⌜zero⌝ : ∀{A} → ⊩ ⌜ℕ⌝ A
⌜zero⌝ = 𝝀 𝝀 𝒗 𝟎

⌜suc⌝ : ∀{A} → ⊩ ⌜ℕ⌝ A ⊃ ⌜ℕ⌝ A
⌜suc⌝ = 𝝀 𝝀 𝝀 𝒗 𝟏 ∙ (𝒗 𝟐 ∙ 𝒗 𝟏 ∙ 𝒗 𝟎)


⌜1⌝ : ∀{A} → ⊩ ⌜ℕ⌝ A
⌜1⌝ = 𝝀 𝝀 𝒗 𝟏 ∙ 𝒗 𝟎

⌜2⌝ : ∀{A} → ⊩ ⌜ℕ⌝ A
⌜2⌝ = 𝝀 𝝀 𝒗 𝟏 ∙ (𝒗 𝟏 ∙ 𝒗 𝟎)

⌜3⌝ : ∀{A} → ⊩ ⌜ℕ⌝ A
⌜3⌝ = 𝝀 𝝀 𝒗 𝟏 ∙ (𝒗 𝟏 ∙ (𝒗 𝟏 ∙ 𝒗 𝟎))


⌜suc∘zero⌝ : ∀{A} → ⊩ ⌜ℕ⌝ A
⌜suc∘zero⌝ = ⌜suc⌝ ∙ ⌜zero⌝

⌜suc∘suc∘zero⌝ : ∀{A} → ⊩ ⌜ℕ⌝ A
⌜suc∘suc∘zero⌝ = ⌜suc⌝ ∙ ⌜suc∘zero⌝

⌜suc∘suc∘suc∘zero⌝ : ∀{A} → ⊩ ⌜ℕ⌝ A
⌜suc∘suc∘suc∘zero⌝ = ⌜suc⌝ ∙ ⌜suc∘suc∘zero⌝


module `Bool where
  -- A ⊃ A ⊃ A

  `true : ∀{A t f}
      → ⊩ 𝜆 𝜆 𝑣 1
          ∶ (t ∶ A ⊃ f ∶ A ⊃ t ∶ A)
  `true = 𝝀² 𝝀² 𝒗 𝟏

  `false : ∀{A t f}
      → ⊩ 𝜆 𝜆 𝑣 0
          ∶ (t ∶ A ⊃ f ∶ A ⊃ f ∶ A)
  `false = 𝝀² 𝝀² 𝒗 𝟎

  `ifThenElse : ∀{A b t f}
      → ⊩ 𝜆 𝜆 𝜆 𝑣 2 ∘² 𝑣 1 ∘² 𝑣 0
          ∶ (b ∶ (A ⊃ A ⊃ A) ⊃ t ∶ A ⊃ f ∶ A ⊃ (b ∘ t ∘ f) ∶ A)
  `ifThenElse = 𝝀² 𝝀² 𝝀² 𝒗 𝟐 ∙³ 𝒗 𝟏 ∙³ 𝒗 𝟎


module `Maybe where
  -- (A ⊃ B) ⊃ B ⊃ B

  `just : ∀{A B a j n}
      → ⊩ 𝜆 𝜆 𝜆 𝑣 1 ∘² 𝑣 2
          ∶ (a ∶ A ⊃ j ∶ (A ⊃ B) ⊃ n ∶ B ⊃ (j ∘ a) ∶ B)
  `just = 𝝀² 𝝀² 𝝀² 𝒗 𝟏 ∙³ 𝒗 𝟐

  `nothing : ∀{A B j n}
      → ⊩ 𝜆 𝜆 𝑣 0
          ∶ (j ∶ (A ⊃ B) ⊃ n ∶ B ⊃ n ∶ B)
  `nothing = 𝝀² 𝝀² 𝒗 𝟎

  `maybe : ∀{A B m j n}
      → ⊩ 𝜆 𝜆 𝜆 𝑣 2 ∘² 𝑣 1 ∘² 𝑣 0
          ∶ (m ∶ ((A ⊃ B) ⊃ B ⊃ B) ⊃ j ∶ (A ⊃ B) ⊃ n ∶ B ⊃ (m ∘ j ∘ n) ∶ B)
  `maybe = 𝝀² 𝝀² 𝝀² 𝒗 𝟐 ∙³ 𝒗 𝟏 ∙³ 𝒗 𝟎


module `Either where
  -- (A ⊃ C) ⊃ (B ⊃ C) ⊃ C

  `left : ∀{A B C a l r}
      → ⊩ 𝜆 𝜆 𝜆 𝑣 1 ∘² 𝑣 2
          ∶ (a ∶ A ⊃ l ∶ (A ⊃ C) ⊃ r ∶ (B ⊃ C) ⊃ (l ∘ a) ∶ C)
  `left = 𝝀² 𝝀² 𝝀² 𝒗 𝟏 ∙³ 𝒗 𝟐

  `right : ∀{A B C b l r}
      → ⊩ 𝜆 𝜆 𝜆 𝑣 0 ∘² 𝑣 2
          ∶ (b ∶ B ⊃ l ∶ (A ⊃ C) ⊃ r ∶ (B ⊃ C) ⊃ (r ∘ b) ∶ C)
  `right = 𝝀² 𝝀² 𝝀² 𝒗 𝟎 ∙³ 𝒗 𝟐

  `either : ∀{A B C e l r}
      → ⊩ 𝜆 𝜆 𝜆 𝑣 2 ∘² 𝑣 1 ∘² 𝑣 0
          ∶ (e ∶ ((A ⊃ C) ⊃ (B ⊃ C) ⊃ C) ⊃ l ∶ (A ⊃ C) ⊃ r ∶ (B ⊃ C) ⊃ (e ∘ l ∘ r) ∶ C)
  `either = 𝝀² 𝝀² 𝝀² 𝒗 𝟐 ∙³ 𝒗 𝟏 ∙³ 𝒗 𝟎


module `ℕ where
  -- (A ⊃ A) ⊃ A ⊃ A

  Tsuc : Tm
  Tsuc = 𝜆 𝜆 𝜆 𝑣 1 ∘² (𝑣 2 ∘² 𝑣 1 ∘² 𝑣 0)

  Tsuc² : Tm
  Tsuc² = 𝜆² 𝜆² 𝜆² 𝑣 1 ∘³ (𝑣 2 ∘³ 𝑣 1 ∘³ 𝑣 0)

  `suc : ∀{A n s z}
      → ⊩ Tsuc
          ∶ (n ∶ ((A ⊃ A) ⊃ A ⊃ A) ⊃ s ∶ (A ⊃ A) ⊃ z ∶ A ⊃ (s ∘ (n ∘ s ∘ z)) ∶ A)
  `suc = 𝝀² 𝝀² 𝝀² 𝒗 𝟏 ∙³ (𝒗 𝟐 ∙³ 𝒗 𝟏 ∙³ 𝒗 𝟎)

  Tzero : Tm
  Tzero = 𝜆 𝜆 𝑣 0

  Tzero² : Tm
  Tzero² = 𝜆² 𝜆² 𝑣 0

  `zero : ∀{A s z}
      → ⊩ Tzero
          ∶ (s ∶ (A ⊃ A) ⊃ z ∶ A ⊃ z ∶ A)
  `zero = 𝝀² 𝝀² 𝒗 𝟎

  Titer : Tm
  Titer = 𝜆 𝜆 𝜆 𝑣 2 ∘² 𝑣 1 ∘² 𝑣 0

  Titer² : Tm
  Titer² = 𝜆² 𝜆² 𝜆² 𝑣 2 ∘³ 𝑣 1 ∘³ 𝑣 0

  `iter : ∀{m A n s z} {Γ : Cx m}
      → Γ ⊢ Titer
          ∶ (n ∶ ((A ⊃ A) ⊃ A ⊃ A) ⊃ s ∶ (A ⊃ A) ⊃ z ∶ A ⊃ (n ∘ s ∘ z) ∶ A)
  `iter = 𝝀² 𝝀² 𝝀² 𝒗 𝟐 ∙³ 𝒗 𝟏 ∙³ 𝒗 𝟎

  `iter² : ∀{m A n s z} {Γ : Cx m}
      → Γ ⊢ Titer²
          ∶ Titer
          ∶ (n ∶ ((A ⊃ A) ⊃ A ⊃ A) ⊃ s ∶ (A ⊃ A) ⊃ z ∶ A ⊃ (n ∘ s ∘ z) ∶ A)
  `iter² = 𝝀³ 𝝀³ 𝝀³ 𝒗 𝟐 ∙⁴ 𝒗 𝟏 ∙⁴ 𝒗 𝟎

  `rec : ∀{A n f z}
      → ⊩ 𝜆 𝜆 𝜆 𝜋₁² (𝑣 2 ∘² (𝜆² 𝑝²⟨ Tsuc² ∘² 𝜋₀² 𝑣 0 , 𝑣 2 ∘² 𝜋₀² 𝑣 0 ∘² 𝜋₁² 𝑣 0 ⟩) ∘² 𝑝²⟨ Tzero² , 𝑣 0 ⟩)
          ∶ (n ∶ ((A ⊃ A) ⊃ A ⊃ A) ⊃ f ∶ (((A ⊃ A) ⊃ A ⊃ A) ⊃ A ⊃ A) ⊃ z ∶ A
              ⊃ (𝜋₁ (n ∘ (𝜆 𝑝⟨ Tsuc ∘ 𝜋₀ 𝑣 0 , 𝑣 2 ∘ 𝜋₀ 𝑣 0 ∘ 𝜋₁ 𝑣 0 ⟩) ∘ 𝑝⟨ Tzero , z ⟩)) ∶ A)
  `rec = 𝝀² 𝝀² 𝝀² 𝝅₁³ ({!𝒗 𝟐!} ∙³ {!!} ∙³ {!!})




wtf : {TX TA : Ty} {X A x a : Tm} → ⊩  𝜆 𝜆 ⇑ 𝑝³⟨ 𝑣 1 , 𝑣 0 ⟩  ∶  (x ∶ X ∶ TX ⊃ a ∶ A ∘ x ∶ TA ⊃ ! 𝑝²⟨ x , a ⟩ ∶ 𝑝²⟨ x , a ⟩ ∶ 𝑝⟨ X , A ∘ x ⟩ ∶ (TX ∧ TA))
wtf = 𝝀² 𝝀² ⬆² 𝒑⁴⟨ 𝒗 𝟏 , 𝒗 𝟎 ⟩

-}
