  data Con : Set              -- Contexts of typed assumptions.
  data Sub : Con → Con → Set  -- Sub Γ Δ replaces Δ-variables in Γ.
  data Ty : Con → Nat → Set   -- Ty Γ r: types A : U_r in Γ.
  data Tm : Con → Set         -- Tm Γ: terms; tyOf computes their type.

  RankedTy : Con → Set
  RankedTy Γ = Σ Nat (Ty Γ)

  tyOf : ∀ {Γ} → Tm Γ → RankedTy Γ
