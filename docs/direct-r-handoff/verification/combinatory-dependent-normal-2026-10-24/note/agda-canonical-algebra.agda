Term : Set
Term = Σ SK.Ty C.Canonical

tyOf : Term → SK.Ty
tyOf = fst

TmAt : SK.Ty → Set
TmAt A = Σ Term (λ t → tyOf t ≡ A)

embed : C.Canonical A → TmAt A
embed {A} t = (A , t) , refl

at : TmAt A → C.Canonical A
at ((B , t) , p) = subst C.Canonical p t

app : TmAt (A SK.⇒ D) → TmAt A → TmAt D
app f x = embed (C.apply-and-normalize (at f) (at x))
