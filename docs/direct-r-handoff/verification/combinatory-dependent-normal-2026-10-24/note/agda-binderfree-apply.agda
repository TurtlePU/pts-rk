record Result {A : Ty} (t : Tm A) : Set where
  constructor result
  field
    normal : Nf A
    sound : t ↠ erase normal
open Result public

apply-normal : (f : Nf (A ⇒ D)) (x : Nf A)
             → Σ (Nf D) (λ y → (f ∙ x ⇓ y) × Good D y)
apply-normal f x = good f x (good x)

normalize-apply : (f : Nf (A ⇒ D)) (x : Nf A)
                → Result (erase f · erase x)
normalize-apply f x with apply-normal f x
... | y , p , py = result y (application-sound p)
