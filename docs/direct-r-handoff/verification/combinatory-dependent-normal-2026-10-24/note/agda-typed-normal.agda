-- labels names the fixed alphabet; A is an original closed annotated type.
-- Length is exactly N; d bounds the rank of A, not just redexes (there are none).
TypedNormal : ∀ {a} → (labels : Fin a → Nat) → (N d : Nat) → Term 0 → Set
TypedNormal {a} labels N d A = Σ (ExactNf a 0 N)
  (λ t → NormalAt labels N d A (erase (Fin a) (fst t)))

typed-normal-bound : ∀ {a} (labels : Fin a → Nat) (N d : Nat) (A : Term 0)
  → a ≤ N → AtMost (TypedNormal labels N d A)
      (tetration (4 · N + 4) (d + 3))
typed-normal-bound {a} labels N d A p = subtype-finite
  (λ t → NormalAt labels N d A (erase (Fin a) (fst t)))
  (λ t → normalAt-isProp labels N d A (erase (Fin a) (fst t)))
  (closed-exact-normal-bound a d N p)
