apply-and-normalize : Canonical (A SK.⇒ D) → Canonical A → Canonical D
apply-and-normalize f x = canonical (fst f SK.· fst x)

apply-sound : (f : Canonical (A SK.⇒ D)) (x : Canonical A)
  → Beta (B.expand {zero} (fst (apply-and-normalize f x)))
      (B.expand (fst f SK.· fst x))
apply-sound f x = sound (fst f SK.· fst x)
