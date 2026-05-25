Class Levels_sig (L: Type) :=
  { axiom: L -> L -> Prop
  ; rule: L -> L -> L -> Prop
  }.

Generalizable Variable L.

Class Levels_functional_sig `(Levels_sig L) :=
  { axiom_f {ℓ₁ ℓ₂} ℓ:
      axiom ℓ ℓ₁ -> axiom ℓ ℓ₂ -> ℓ₁ = ℓ₂
  ; rule_f {ℓ₁ ℓ₂} ℓₜ ℓᵤ:
      rule ℓₜ ℓᵤ ℓ₁ -> rule ℓₜ ℓᵤ ℓ₂ -> ℓ₁ = ℓ₂
  }.

Class Levels_total_sig `(Levels_sig L) :=
  { axiom_t ℓ: exists ℓ', axiom ℓ ℓ'
  ; rule_t ℓₜ ℓᵤ: exists ℓ, rule ℓₜ ℓᵤ ℓ
  }.
