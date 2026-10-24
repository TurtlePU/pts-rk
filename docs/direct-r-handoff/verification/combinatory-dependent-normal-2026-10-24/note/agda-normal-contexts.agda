mutual
  data Con : Set where
    ε : Con
    ext : (Γ : Con) {r : Nat} → TyNF (context Γ) r → Con

  length : Con → Nat
  length ε = zero
  length (ext Γ A) = suc (length Γ)

  context : (Γ : Con) → Context (length Γ)
  context ε = empty
  context (ext Γ A) = extend (context Γ) (term A)

Ty : Con → Nat → Set
Ty Γ r = TyNF (context Γ) r

Tm : (Γ : Con) {r : Nat} → Ty Γ r → Set
Tm Γ A = NfAt (context Γ) (term A)

Sub : Con → Con → Set
Sub Γ Δ = SubNF (context Γ) (context Δ)
