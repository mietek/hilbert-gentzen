module A201602.Scratch-encodings where

{-

 -- Theorems
 ⊩_  : Ty → Set
-⊩ A = ∅ ⊢ A
+⊩ A = ∀{m} {Γ : Cx m} → Γ ⊢ A



+wtf : {TX TA : Ty} {X A x a : Tm} → ⊩  𝜆 𝜆 ⇑ 𝑝³⟨ 𝑣 1 , 𝑣 0 ⟩  ∶  (x ∶ X ∶ TX ⊃ a ∶ A ∘ x ∶ TA ⊃ ! 𝑝²⟨ x , a ⟩ ∶ 𝑝²⟨ x , a ⟩ ∶ 𝑝⟨ X , A ∘ x ⟩ ∶ (TX ∧ TA))
+wtf = 𝝀² 𝝀² ⬆² 𝒑⁴⟨ 𝒗 𝟏 , 𝒗 𝟎 ⟩
+
+


 -- ⊩ B  →  ⊩ t ∶ B
-nec : ∀{B}
-    → ⊩ B
-    → Σ Tm λ t → ⊩ t ∶ B
-nec = int⊢
+postulate
+  nec : ∀{B}
+      → ⊩ B
+      → Σ Tm (λ t → ⊩ t ∶ B)
+  -- nec = int⊢  -- XXX: Needs weakening


 -- --------------------------------------------------------------------------
@@ -727,26 +759,109 @@ nec = int⊢
 -- Example necessitated terms at levels 2, 3, and 4


+record R (A B C : Ty) : Set where
+  field
+    I     : Ty
+    id    : ⊩ I
+    K     : Ty
+    const : ⊩ K
+    S     : Ty
+    ap    : ⊩ S
+
+r1 : ∀{A B C} → R A B C
+r1 {A} {B} {C} =
+  record
+    { I     = A ⊃ A
+    ; id    = 𝝀 𝒗 𝟎
+    ; K     = A ⊃ B ⊃ A
+    ; const = 𝝀 𝝀 𝒗 𝟏
+    ; S     = (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
+    ; ap    = 𝝀 𝝀 𝝀 (𝒗 𝟐 ∙ 𝒗 𝟎) ∙ (𝒗 𝟏 ∙ 𝒗 𝟎)
+    }
+
+r2 : ∀{A B C} → R A B C
+r2 {A} {B} {C} =
+  record
+    { I     = 𝜆 𝑣 0 ∶ (A ⊃ A)
+    ; id    = 𝝀² 𝒗 𝟎
+    ; K     = 𝜆 𝜆 𝑣 1 ∶ (A ⊃ B ⊃ A)
+    ; const = 𝝀² 𝝀² 𝒗 𝟏
+    ; S     = 𝜆 𝜆 𝜆 (𝑣 2 ∘ 𝑣 0) ∘ (𝑣 1 ∘ 𝑣 0) ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
+    ; ap    = 𝝀² 𝝀² 𝝀² (𝒗 𝟐 ∙² 𝒗 𝟎) ∙² (𝒗 𝟏 ∙² 𝒗 𝟎)
+    }
+
+r3 : ∀{A B C} → R A B C
+r3 {A} {B} {C} =
+  record
+    { I     = 𝜆² 𝑣 0 ∶ 𝜆 𝑣 0 ∶ (A ⊃ A)
+    ; id    = 𝝀³ 𝒗 𝟎
+    ; K     = 𝜆² 𝜆² 𝑣 1 ∶ 𝜆 𝜆 𝑣 1 ∶ (A ⊃ B ⊃ A)
+    ; const = 𝝀³ 𝝀³ 𝒗 𝟏
+    ; S     = 𝜆² 𝜆² 𝜆² (𝑣 2 ∘² 𝑣 0) ∘² (𝑣 1 ∘² 𝑣 0) ∶ 𝜆 𝜆 𝜆 (𝑣 2 ∘ 𝑣 0) ∘ (𝑣 1 ∘ 𝑣 0) ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
+    ; ap    = 𝝀³ 𝝀³ 𝝀³ (𝒗 𝟐 ∙³ 𝒗 𝟎) ∙³ (𝒗 𝟏 ∙³ 𝒗 𝟎)
+    }
+
+rsuc : ∀{A B C} → R A B C → R A B C
+rsuc {A} {B} {C} l1 =
+  record
+    { I     = π₀ (nec (R.id l1)) ∶ (R.I l1)
+    ; id    = π₁ (nec (R.id l1))
+    ; K     = π₀ (nec (R.const l1)) ∶ (R.K l1)
+    ; const = π₁ (nec (R.const l1))
+    ; S     = π₀ (nec (R.ap l1)) ∶ (R.S l1)
+    ; ap    = π₁ (nec (R.ap l1))
+    }
+
+{- XXX: Broken by postulate
+r2≡rsuc-r1 : ∀{A B C} → r2 {A} {B} {C} ≡ rsuc r1
+r2≡rsuc-r1 = refl
+
+r3≡rsuc-rsuc-r1 : ∀{A B C} → r3 {A} {B} {C} ≡ rsuc (rsuc r1)
+r3≡rsuc-rsuc-r1 = refl
+-}
+
+
+
+
+
+
+⌜I⌝ : Ty → Ty
+⌜I⌝ A = A ⊃ A
+
+⌜id⌝ : (A : Ty) → ⊩ ⌜I⌝ A
+⌜id⌝ A = 𝝀 𝒗 𝟎
+
+⌜I²⌝ : Ty → Ty
+⌜I²⌝ A = 𝜆 𝑣 0 ∶ (⌜I⌝ A)
+
+⌜I²⌝′ : Ty → Ty
+⌜I²⌝′ A = π₀ (nec (⌜id⌝ A)) ∶ (⌜I⌝ A)
+
+⌜id²⌝ : (A : Ty) → ⊩ ⌜I²⌝ A
+⌜id²⌝ A = 𝝀² 𝒗 𝟎
+
+⌜id²⌝′ : (A : Ty) → ⊩ ⌜I²⌝′ A
+⌜id²⌝′ A = π₁ (nec (⌜id⌝ A))
+
+
 -- A ⊃ A
 tI′ : ∀{A}
     → ⊩  A ⊃ A
 tI′ = tI

 -- 𝜆 𝑣 0  ∶  (A ⊃ A)
-tI²′ : ∀{A} → Σ Tm λ t
-    → ⊩  t  ∶  (A ⊃ A)
+tI²′ : ∀{A} → Σ Tm (λ t → ⊩ t ∶ (A ⊃ A))
 tI²′ = nec tI

+{- XXX: Broken by postulate
 -- 𝜆² 𝑣 0  ∶  𝜆 𝑣 0  ∶  (A ⊃ A)
-tI³′ : ∀{A} → Σ Tm λ t
-    → ⊩  t  ∶  𝜆 𝑣 0  ∶  (A ⊃ A)
-tI³′ = nec (proj₂ tI²′)
+tI³′ : ∀{A} → Σ Tm (λ t → ⊩ t ∶ 𝜆 𝑣 0 ∶ (A ⊃ A))
+tI³′ = nec (π₁ tI²′)

 -- 𝜆³ 𝑣 0  ∶  𝜆² v 0  ∶  𝜆 𝑣 0  ∶  (A ⊃ A)
-tI⁴′ : ∀{A} → Σ Tm λ t
-    → ⊩  t  ∶  𝜆² 𝑣 0  ∶  𝜆 𝑣 0  ∶  (A ⊃ A)
-tI⁴′ = nec (proj₂ tI³′)
-
+tI⁴′ : ∀{A} → Σ Tm (λ t → ⊩ t ∶ 𝜆² 𝑣 0 ∶ 𝜆 𝑣 0 ∶ (A ⊃ A))
+tI⁴′ = nec (π₁ tI³′)
+-}

 -- A ⊃ B ⊃ A
 tK′ : ∀{A B}
@@ -754,20 +869,18 @@ tK′ : ∀{A B}
 tK′ = tK

 -- 𝜆 𝜆 𝑣 1  ∶  (A ⊃ B ⊃ A)
-tK²′ : ∀{A B} → Σ Tm λ t
-    → ⊩  t  ∶  (A ⊃ B ⊃ A)
+tK²′ : ∀{A B} → Σ Tm (λ t → ⊩ t ∶ (A ⊃ B ⊃ A))
 tK²′ = nec tK

+{- XXX: Broken by postulate
 -- 𝜆² 𝜆² 𝑣 1  ∶  𝜆 𝜆 𝑣 1  ∶  (A ⊃ B ⊃ A)
-tK³′ : ∀{A B} → Σ Tm λ t
-    → ⊩  t  ∶  𝜆 𝜆 𝑣 1  ∶  (A ⊃ B ⊃ A)
-tK³′ = nec (proj₂ tK²′)
+tK³′ : ∀{A B} → Σ Tm (λ t → ⊩ t ∶ 𝜆 𝜆 𝑣 1 ∶ (A ⊃ B ⊃ A))
+tK³′ = nec (π₁ tK²′)

 -- 𝜆³ 𝜆³ 𝑣 1  ∶  𝜆² 𝜆² 𝑣 1  ∶  𝜆 𝜆 𝑣 1  ∶  (A ⊃ B ⊃ A)
-tK⁴′ : ∀{A B} → Σ Tm λ t
-    → ⊩  t  ∶  𝜆² 𝜆² 𝑣 1  ∶  𝜆 𝜆 𝑣 1  ∶  (A ⊃ B ⊃ A)
-tK⁴′ = nec (proj₂ tK³′)
-
+tK⁴′ : ∀{A B} → Σ Tm (λ t → ⊩ t ∶ 𝜆² 𝜆² 𝑣 1 ∶ 𝜆 𝜆 𝑣 1 ∶ (A ⊃ B ⊃ A))
+tK⁴′ = nec (π₁ tK³′)
+-}

 -- (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
 tS′ : ∀{A B C}
@@ -775,68 +888,141 @@ tS′ : ∀{A B C}
 tS′ = tS

 -- 𝜆 𝜆 𝜆 (𝑣 2 ∘ 𝑣 0) ∘ (𝑣 1 ∘ 𝑣 0)  ∶  ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
-tS²′ : ∀{A B C} → Σ Tm λ t
-    → ⊩  t  ∶  ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
+tS²′ : ∀{A B C} → Σ Tm (λ t → ⊩ t ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C))
 tS²′ = nec tS

+{- XXX: Broken by postulate
 -- 𝜆² 𝜆² 𝜆² (𝑣 2 ∘² 𝑣 0) ∘² (𝑣 1 ∘² 𝑣 0)  ∶  𝜆 𝜆 𝜆 (𝑣 2 ∘ 𝑣 0) ∘ (𝑣 1 ∘ 𝑣 0)  ∶  ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
-tS³′ : ∀{A B C} → Σ Tm λ t
-    → ⊩  t  ∶  𝜆 𝜆 𝜆 (𝑣 2 ∘ 𝑣 0) ∘ (𝑣 1 ∘ 𝑣 0)  ∶  ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
-tS³′ = nec (proj₂ tS²′)
+tS³′ : ∀{A B C} → Σ Tm (λ t → ⊩ t ∶ 𝜆 𝜆 𝜆 (𝑣 2 ∘ 𝑣 0) ∘ (𝑣 1 ∘ 𝑣 0) ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C))
+tS³′ = nec (π₁ tS²′)

 -- 𝜆³ 𝜆³ 𝜆³ (𝑣 2 ∘³ 𝑣 0) ∘³ (𝑣 1 ∘³ 𝑣 0)  ∶  𝜆² 𝜆² 𝜆² (𝑣 2 ∘² 𝑣 0) ∘² (𝑣 1 ∘² 𝑣 0)  ∶  𝜆 𝜆 𝜆 (𝑣 2 ∘ 𝑣 0) ∘ (𝑣 1 ∘ 𝑣 0)  ∶  ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
-tS⁴′ : ∀{A B C} → Σ Tm λ t
-    → ⊩  t  ∶  𝜆² 𝜆² 𝜆² (𝑣 2 ∘² 𝑣 0) ∘² (𝑣 1 ∘² 𝑣 0)  ∶  𝜆 𝜆 𝜆 (𝑣 2 ∘ 𝑣 0) ∘ (𝑣 1 ∘ 𝑣 0)  ∶  ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
-tS⁴′ = nec (proj₂ tS³′)
+tS⁴′ : ∀{A B C} → Σ Tm (λ t → ⊩ t ∶ 𝜆² 𝜆² 𝜆² (𝑣 2 ∘² 𝑣 0) ∘² (𝑣 1 ∘² 𝑣 0) ∶ 𝜆 𝜆 𝜆 (𝑣 2 ∘ 𝑣 0) ∘ (𝑣 1 ∘ 𝑣 0) ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C))
+tS⁴′ = nec (π₁ tS³′)
+-}


 -- --------------------------------------------------------------------------
 --
--- Church encoding of true and false
+-- Church encodings


-⌜Bool⌝ : Ty → Ty
-⌜Bool⌝ A = A ⊃ A ⊃ A
+module Church where
+  `Bool : Ty → Ty
+  `Bool T = T ⊃ T ⊃ T

+  `true : ∀{T} → ⊩ `Bool T
+  `true = 𝝀 𝝀 𝒗 𝟏

-⌜true⌝ : ∀{A} → ⊩ ⌜Bool⌝ A
-⌜true⌝ = 𝝀 𝝀 𝒗 𝟏
+  `false : ∀{T} → ⊩ `Bool T
+  `false = 𝝀 𝝀 𝒗 𝟎

-⌜false⌝ : ∀{A} → ⊩ ⌜Bool⌝ A
-⌜false⌝ = 𝝀 𝝀 𝒗 𝟎
+  `ifThenElse : ∀{T} → ⊩ `Bool T ⊃ T ⊃ T ⊃ T
+  `ifThenElse = 𝝀 𝝀 𝝀 𝒗 𝟐 ∙ 𝒗 𝟏 ∙ 𝒗 𝟎


--- --------------------------------------------------------------------------
---
--- Church encoding of natural numbers
+  `Maybe : Ty → Ty → Ty
+  `Maybe T A = (A ⊃ T) ⊃ T ⊃ T
+
+  `nothing : ∀{T A} → ⊩ `Maybe T A
+  `nothing = 𝝀 𝝀 𝒗 𝟎
+
+  `just : ∀{T A} → ⊩ A ⊃ `Maybe T A
+  `just = 𝝀 𝝀 𝝀 𝒗 𝟏 ∙ 𝒗 𝟐
+
+  `maybe : ∀{T A} → ⊩ `Maybe T A ⊃ (A ⊃ T) ⊃ T ⊃ T
+  `maybe = 𝝀 𝝀 𝝀 𝒗 𝟐 ∙ 𝒗 𝟏 ∙ 𝒗 𝟎
+
+
+  `Either : Ty → Ty → Ty → Ty
+  `Either T A B = (A ⊃ T) ⊃ (B ⊃ T) ⊃ T
+
+  `left : ∀{T A B} → ⊩ A ⊃ `Either T A B
+  `left = 𝝀 𝝀 𝝀 𝒗 𝟏 ∙ 𝒗 𝟐
+
+  `right : ∀{T A B} → ⊩ B ⊃ `Either T A B
+  `right = 𝝀 𝝀 𝝀 𝒗 𝟎 ∙ 𝒗 𝟐
+
+  `either : ∀{T A B} → ⊩ `Either T A B ⊃ (A ⊃ T) ⊃ (B ⊃ T) ⊃ T
+  `either = 𝝀 𝝀 𝝀 𝒗 𝟐 ∙ 𝒗 𝟏 ∙ 𝒗 𝟎
+
+
+  `ℕ : Ty → Ty
+  `ℕ T = (T ⊃ T) ⊃ T ⊃ T
+
+  `zero : ∀{T} → ⊩ `ℕ T
+  `zero = 𝝀 𝝀 𝒗 𝟎
+
+  `suc : ∀{T} → ⊩ `ℕ T ⊃ `ℕ T
+  `suc = 𝝀 𝝀 𝝀 𝒗 𝟏 ∙ (𝒗 𝟐 ∙ 𝒗 𝟏 ∙ 𝒗 𝟎)
+
+  -- Iterator
+  `iterℕ : ∀{T} → ⊩ `ℕ T ⊃ (T ⊃ T) ⊃ T ⊃ T
+  `iterℕ = 𝝀 𝝀 𝝀 𝒗 𝟐 ∙ 𝒗 𝟏 ∙ 𝒗 𝟎
+
+  -- Recursor
+  `recℕ : ∀{T A} → ⊩ `ℕ (`ℕ T ∧ A) ⊃ (`ℕ T ⊃ A ⊃ A) ⊃ A ⊃ A
+  `recℕ = 𝝀 𝝀 𝝀 𝝅₁ (`iterℕ ∙ 𝒗 𝟐 ∙ (𝝀 𝒑⟨ `suc ∙ 𝝅₀ 𝒗 𝟎 , 𝒗 𝟐 ∙ 𝝅₀ 𝒗 𝟎 ∙ 𝝅₁ 𝒗 𝟎 ⟩) ∙ 𝒑⟨ `zero , 𝒗 𝟎 ⟩)
+
+  -- Kleene’s predecessor
+  `iterPred : ∀{T} → ⊩ `ℕ (`ℕ T ∧ `ℕ T) ⊃ `ℕ T
+  `iterPred = 𝝀 𝝅₁ (`iterℕ ∙ 𝒗 𝟎 ∙ (𝝀 𝒑⟨ `suc ∙ 𝝅₀ 𝒗 𝟎 , 𝝅₀ 𝒗 𝟎 ⟩) ∙ 𝒑⟨ `zero , `zero ⟩)
+
+  -- Predecessor
+  `pred : ∀{T} → ⊩ `ℕ (`ℕ T ∧ `ℕ T) ⊃ `ℕ T
+  `pred = 𝝀 `recℕ ∙ 𝒗 𝟎 ∙ (𝝀 𝝀 𝒗 𝟏) ∙ `zero
+
+
+  `List : Ty → Ty → Ty
+  `List T A = (A ⊃ T ⊃ T) ⊃ T ⊃ T
+
+  `nil : ∀{T A} → ⊩ `List T A
+  `nil = 𝝀 𝝀 𝒗 𝟎
+
+  `cons : ∀{T A} → ⊩ A ⊃ `List T A ⊃ `List T A
+  `cons = 𝝀 𝝀 𝝀 𝝀 𝒗 𝟏 ∙ 𝒗 𝟑 ∙ (𝒗 𝟐 ∙ 𝒗 𝟏 ∙ 𝒗 𝟎)
+
+  -- Iterator
+  `iterList : ∀{T A} → ⊩ `List T A ⊃ (A ⊃ T ⊃ T) ⊃ T ⊃ T
+  `iterList = 𝝀 𝝀 𝝀 𝒗 𝟐 ∙ 𝒗 𝟏 ∙ 𝒗 𝟎
+
+  -- Recursor
+  `recList : ∀{T A B} → ⊩ `List (`List T A ∧ B) A ⊃ (A ⊃ `List T A ⊃ B ⊃ B) ⊃ B ⊃ B
+  `recList = 𝝀 𝝀 𝝀 𝝅₁ (`iterList ∙ 𝒗 𝟐 ∙ (𝝀 𝝀 𝒑⟨ `cons ∙ 𝒗 𝟏 ∙ 𝝅₀ 𝒗 𝟎 , 𝒗 𝟑 ∙ 𝒗 𝟏 ∙ 𝝅₀ 𝒗 𝟎 ∙ 𝝅₁ 𝒗 𝟎 ⟩) ∙ 𝒑⟨ `nil , 𝒗 𝟎 ⟩)


-⌜Nat⌝ : Ty → Ty
-⌜Nat⌝ A = (A ⊃ A) ⊃ A ⊃ A
+  -- `Stream : Ty → Ty
+  -- `Stream A = Σ Ty (λ T → T ∧ (T ⊃ A ∧ T))

+  -- `hd : ∀{T A} → ⊩ `Stream T A ⊃ A
+  -- `hd = 𝝀 {!!}

-⌜zero⌝ : ∀{A} → ⊩ ⌜Nat⌝ A
-⌜zero⌝ = 𝝀 𝝀 𝒗 𝟎
+  -- `tl : ∀{T A} → ⊩ `Stream T A ⊃ `Stream T A
+  -- `tl = 𝝀 𝝀 𝝀 𝒑⟨ 𝝅₀ (𝒗 𝟏 ∙ 𝝅₁ (𝒗 𝟐 ∙ 𝒗 𝟏 ∙ 𝒗 𝟎))
+  --              , 𝝅₁ (𝒗 𝟏 ∙ 𝝅₁ (𝒗 𝟐 ∙ 𝒗 𝟏 ∙ 𝒗 𝟎)) ⟩

-⌜suc⌝ : ∀{A} → ⊩ ⌜Nat⌝ A ⊃ ⌜Nat⌝ A
-⌜suc⌝ = 𝝀 𝝀 𝝀 𝒗 𝟏 ∙ (𝒗 𝟐 ∙ 𝒗 𝟏 ∙ 𝒗 𝟎)
+  -- `coiter : ∀{T A B} → ⊩ (B ⊃ A) ⊃ (B ⊃ B) ⊃ B ⊃ `Stream T A
+  -- `coiter = {!!}

+  -- `corec : ∀{T A B} → ⊩ (B ⊃ A) ⊃ (B ⊃ `Either T (`Stream T A) B) ⊃ B ⊃ `Stream T A
+  -- `corec = {!!}

-⌜1⌝ : ∀{A} → ⊩ ⌜Nat⌝ A
-⌜1⌝ = 𝝀 𝝀 𝒗 𝟏 ∙ 𝒗 𝟎

-⌜2⌝ : ∀{A} → ⊩ ⌜Nat⌝ A
-⌜2⌝ = 𝝀 𝝀 𝒗 𝟏 ∙ (𝒗 𝟏 ∙ 𝒗 𝟎)
+module Hm where
+  List : Set → Set → Set
+  List A B = (A → B → B) → B → B

-⌜3⌝ : ∀{A} → ⊩ ⌜Nat⌝ A
-⌜3⌝ = 𝝀 𝝀 𝒗 𝟏 ∙ (𝒗 𝟏 ∙ (𝒗 𝟏 ∙ 𝒗 𝟎))
+  nil : ∀{A B} → List A B
+  nil = λ f b₀ → b₀

+  cons : ∀{A B} → A → List A B → List A B
+  cons a it = λ f b₀ → f a (it f b₀)

-⌜suc∘zero⌝ : ∀{A} → ⊩ ⌜Nat⌝ A
-⌜suc∘zero⌝ = ⌜suc⌝ ∙ ⌜zero⌝
+  iterList : ∀{A B} → List A B → (A → B → B) → B → B
+  iterList it f b₀ = it f b₀

-⌜suc∘suc∘zero⌝ : ∀{A} → ⊩ ⌜Nat⌝ A
-⌜suc∘suc∘zero⌝ = ⌜suc⌝ ∙ ⌜suc∘zero⌝
+  recList : ∀{A B C} → List A (List A C × B) → (A → List A C → B → B) → B → B
+  recList it f b₀ = π₁ (iterList it (λ a p → ⟨ cons a (π₀ p) , f a (π₀ p) (π₁ p) ⟩) ⟨ nil , b₀ ⟩)

-⌜suc∘suc∘suc∘zero⌝ : ∀{A} → ⊩ ⌜Nat⌝ A
-⌜suc∘suc∘suc∘zero⌝ = ⌜suc⌝ ∙ ⌜suc∘suc∘zero⌝
+  tl : ∀{A B} → List A (List A B × List A B) → List A B
+  tl it = recList it (λ aᵢ asᵢ bᵢ → asᵢ) nil

-}
