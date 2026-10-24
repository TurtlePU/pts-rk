appNF : {Γ : Context n} (wf : WellFormed Γ) (A : TyNF Γ a)
  (B : TyNF (extend Γ (term A)) b)
  → NfAt Γ (term (piNF A B)) → (x : NfAt Γ (term A))
  → NfAt Γ (term (appType wf A B x))
appNF wf A B f x = convertNF (appType wf A B x) (appType-sound wf A B x)
  (normalizeProof {t = app (term f) (term x)} {A = substitute (term B) (term x)}
    wf (PT.rec2 squash₁
    (λ hf hx → ∣ application hf hx ∣₁) (typed f) (typed x)))
