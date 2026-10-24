  data TyExact where
    ty : {r : Nat} (A : Raw) → Typ A (Uraw r) → TyExact r
    tyBeta : {r : Nat} (A B : Raw)
           (dA : Typ A (Uraw r)) (dB : Typ B (Uraw r))
           → Beta A B → ty A dA ≡ ty B dB
    setTyExact : {r : Nat} → isSet (TyExact r)

  rankedSetExact : isSet RankedTyExact
  rankedSetExact = isSetΣ isSetℕ (λ _ → setTyExact)

  data TmExact where
    tm : {r : Nat} (A : Raw) (dA : Typ A (Uraw r))
       (p : Code) → Typ (expand p) A → TmExact
    tmBeta : {r : Nat} (A B : Raw)
           (dA : Typ A (Uraw r)) (dB : Typ B (Uraw r))
           (p q : Code) (h : Typ (expand p) A) (k : Typ (expand q) B)
           → Beta A B → Beta (expand p) (expand q)
           → tm A dA p h ≡ tm B dB q k
    setTmExact : isSet TmExact

  tyOfExact (tm {r} A dA p h) = r , ty A dA
  tyOfExact (tmBeta {r} A B dA dB p q h k e v i)
    = r , tyBeta A B dA dB e i
  tyOfExact (setTmExact t u p q i j)
    = rankedSetExact (tyOfExact t) (tyOfExact u)
        (cong tyOfExact p) (cong tyOfExact q) i j
