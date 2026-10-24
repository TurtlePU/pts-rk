data FiniteWalk (a n s : Nat) : State a n s → State a n s → Set where
  finished : ∀ {i} → FiniteWalk a n s i i
  move : ∀ {i j k} → IndexedStep {a} {n} {s} i j
    → FiniteWalk a n s j k → FiniteWalk a n s i k
