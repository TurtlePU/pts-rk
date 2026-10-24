normalize : SK.Tm SK.ι → SK.Tm SK.ι
normalize = Direct.direct

agrees : (t : SK.Tm SK.ι) → normalize t ≡ Canonical.normalize t
agrees t = sym (Direct.canonical-after-direct t ∙ ground-normal-canonical (Weak.nf t))

canonical : SK.Tm SK.ι → Canonical.Canonical SK.ι
canonical t = normalize t , ground-normal-canonical (Weak.nf t)

apply-and-normalize : Canonical.Canonical (A SK.⇒ SK.ι)
  → Canonical.Canonical A → Canonical.Canonical SK.ι
apply-and-normalize f x = canonical (fst f SK.· fst x)

application-agrees : (f : Canonical.Canonical (A SK.⇒ SK.ι))
  (x : Canonical.Canonical A)
  → apply-and-normalize f x ≡ Canonical.apply-and-normalize f x
application-agrees f x = Canonical.canonical-path (agrees (fst f SK.· fst x))
