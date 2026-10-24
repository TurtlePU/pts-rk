record Inferred (Γ : Context n) (t : Term n) : Set where
  constructor inferred
  field
    inferred-type : Term n
    type-normal : Normal inferred-type
    type-rank : Nat
    type-sorted : Typ Γ inferred-type (U type-rank)
    subject-typed : Typ Γ t inferred-type
open Inferred public

data Result (Γ : Context n) (t : Term n) : Set where
  accepts : Inferred Γ t → Result Γ t
  rejects : (∀ {A} → Typ Γ t A → ⊥) → Result Γ t
