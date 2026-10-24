normalize : SK.Tm A → SK.Tm A
normalize t = C.compile (SN.normalize (C.expand-source t))

sound : (t : SK.Tm A) → Beta (B.expand {zero} (normalize t)) (B.expand t)
sound t = beta-trans (steps-beta (C.compile-steps (SN.normalize (C.expand-source t))))
  (beta-trans (beta-sym (steps-beta (SN.reduces (C.expand-source t))))
    (beta-path (C.erase-expand t)))

coherent : (t u : SK.Tm A)
  → Beta (B.expand {zero} t) (B.expand u) → normalize t ≡ normalize u
coherent t u e = cong C.compile (SN.coherent (C.expand-source t) (C.expand-source u)
  (beta-trans (beta-path (C.erase-expand t))
    (beta-trans e (beta-sym (beta-path (C.erase-expand u))))))

idempotent : (t : SK.Tm A) → normalize (normalize t) ≡ normalize t
idempotent t = coherent (normalize t) t (sound t)

reflects : (t u : SK.Tm A)
  → normalize t ≡ normalize u → Beta (B.expand {zero} t) (B.expand u)
reflects t u e = beta-trans (beta-sym (sound t))
  (beta-trans (beta-path (cong B.expand e)) (sound u))
