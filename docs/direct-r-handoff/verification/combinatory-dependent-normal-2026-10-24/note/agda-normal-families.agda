record NfAt (Γ : Context n) (A : Term n) : Set where
  constructor normal-at
  field
    term : Term n
    normal : Normal term
    typed : ∥ Typ Γ term A ∥₁
open NfAt public

TyNF : Context n → Nat → Set
TyNF Γ r = NfAt Γ (U r)
