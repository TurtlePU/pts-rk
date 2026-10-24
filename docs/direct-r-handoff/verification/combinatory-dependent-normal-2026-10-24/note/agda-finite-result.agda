-- The output is a bounded IIR normal form, not a raw term with an opaque tag.
-- Truncation counts represented terms, rather than their reduction proofs.
ApplicationResult : (d : Nat) (f y : Nf (Fin a) 0) → Set
ApplicationResult {a} d f y =
  Σ (SizedNf a 0 (tower d (inputSize f y)))
    (λ v → ∥ BoundedSteps (tower d (inputSize f y))
      (application f y) (erase (Fin a) (fst v)) ∥₁)

application-result-bound : (d : Nat) (f y : Nf (Fin a) 0)
  → a ≤ inputSize f y
  → AtMost (ApplicationResult d f y)
      (tetration (4 · inputSize f y + 4) (d + 3))
application-result-bound {a} d f y labelsBound =
  subtype-finite (λ v → ∥ BoundedSteps (tower d (inputSize f y))
      (application f y) (erase (Fin a) (fst v)) ∥₁)
    (λ _ → isPropPropTrunc)
    (closed-normal-bound a d (inputSize f y) labelsBound)
