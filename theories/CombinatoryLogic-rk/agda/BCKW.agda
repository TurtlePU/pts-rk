{-# OPTIONS --cubical --safe --guardedness #-}
module BCKW where

open import PTSPrelude

-- Natural-model syntax: types are indexed by rank, terms compute their type.
-- Forward declarations allow constructors and their recursive clauses to
-- be checked together, following Chen--Nordvall Forsberg--Tsai (CPP 2026).
module _ where
  -- BEGINHEADSIGNATURE
  data Con : Set              -- Contexts of typed assumptions.
  data Sub : Con → Con → Set  -- Sub Γ Δ replaces Δ-variables in Γ.
  data Ty : Con → Nat → Set   -- Ty Γ r: types A : U_r in Γ.
  data Tm : Con → Set         -- Tm Γ: terms; tyOf computes their type.

  RankedTy : Con → Set
  RankedTy Γ = Σ Nat (Ty Γ)

  tyOf : ∀ {Γ} → Tm Γ → RankedTy Γ
  -- ENDHEADSIGNATURE
  -- Auxiliary finite application certificates, not additional object terms.
  record Ap {Γ : Con} (f x : Tm Γ) : Set
  data Spine {Γ : Con} (head : Tm Γ) : Nat → Set
  runAp : ∀ {Γ} {f x : Tm Γ} → Ap f x → Tm Γ
  apTy : ∀ {Γ} {f x : Tm Γ} → Ap f x → RankedTy Γ
  run : ∀ {Γ n} {h : Tm Γ} → Spine h n → Tm Γ

  private
    variable
      Γ Δ Θ Ξ : Con
      a b r : Nat
      A : Ty Γ a
      B : Ty Γ b

  empty : Con
  ext : (Γ : Con) → Ty Γ r → Con
  subTy : Ty Δ r → Sub Γ Δ → Ty Γ r
  subTm : Tm Δ → Sub Γ Δ → Tm Γ
  subRanked : RankedTy Δ → Sub Γ Δ → RankedTy Γ
  subRanked X σ = fst X , subTy (snd X) σ
  id : Sub Γ Γ
  comp : Sub Δ Θ → Sub Γ Δ → Sub Γ Θ
  eps : Sub Γ empty
  pair : {A : Ty Δ r} (σ : Sub Γ Δ) (t : Tm Γ)
       → tyOf t ≡ (r , subTy A σ) → Sub Γ (ext Δ A)
  fstS : {A : Ty Δ r} → Sub Γ (ext Δ A) → Sub Γ Δ
  sndS : {A : Ty Δ r} → Sub Γ (ext Δ A) → Tm Γ
  sndType : {A : Ty Δ r} (σ : Sub Γ (ext Δ A))
          → tyOf (sndS σ) ≡ (r , subTy A (fstS σ))

  ty-id : (A : Ty Γ r) → subTy A id ≡ A
  ty-comp : (A : Ty Θ r) (σ : Sub Δ Θ) (τ : Sub Γ Δ)
          → subTy (subTy A σ) τ ≡ subTy A (comp σ τ)
  beta-fst : {A : Ty Δ r} (σ : Sub Γ Δ) (t : Tm Γ)
             (p : tyOf t ≡ (r , subTy A σ)) → fstS (pair σ t p) ≡ σ

  single : (A : Ty Γ r) (t : Tm Γ) → tyOf t ≡ (r , subTy A id)
         → Sub Γ (ext Γ A)
  single A t p = pair id t p

  liftType : (σ : Sub Γ Δ) (A : Ty Δ r)
           → tyOf (sndS {A = subTy A σ} id)
             ≡ (r , subTy A (comp σ (fstS id)))
  lift : (σ : Sub Γ Δ) (A : Ty Δ r)
       → Sub (ext Γ (subTy A σ)) (ext Δ A)
  lift {r = r} σ A = pair (comp σ (fstS id)) (sndS id)
    (liftType σ A)

  U : Nat → Ty Γ zero
  univ : Nat → Tm Γ
  El : (r : Nat) (t : Tm Γ) → tyOf t ≡ (zero , U r) → Ty Γ r
  Pi : (A : Ty Γ a) → Ty (ext Γ A) b → Ty Γ (max (suc a) b)
  app-guarded : (A : Ty Γ a) (B : Ty (ext Γ A) b) (f x : Tm Γ)
      → tyOf f ≡ (max (suc a) b , Pi A B)
      → (px : tyOf x ≡ (a , subTy A id)) → Tm Γ
  univType : (i : Nat) → tyOf (univ {Γ = Γ} i) ≡ (zero , U zero)

  varUType : (r : Nat)
           → tyOf (sndS {A = U {Γ = Γ} r} id) ≡ (zero , U r)
  varEl : (r : Nat) → Ty (ext Γ (U r)) r
  varEl r = El r (sndS id) (varUType r)

  iRank : Nat → Nat
  iRank a = max (suc zero) (max (suc a) a)
  kRank : Nat → Nat → Nat
  kRank a b = max (suc zero)
    (max (suc zero) (max (suc a) (max (suc b) a)))

  IType : (a : Nat) → Ty empty (iRank a)
  IType a = Pi (U a) (Pi (varEl a) (subTy (varEl a) (fstS id)))

  KType : (a b : Nat) → Ty empty (kRank a b)
  KType a b = Pi (U a) (Pi (U b)
    (Pi A₁ (Pi B₂ (subTy (subTy A₁ (fstS id)) (fstS id)))))
    where
    ΓA = ext empty (U a)
    ΓAB = ext ΓA (U b)
    A₁ : Ty ΓAB a
    A₁ = subTy (varEl a) (fstS id)
    B₂ : Ty (ext ΓAB A₁) b
    B₂ = subTy (varEl b) (fstS id)

  arrowRank : Nat → Nat → Nat
  arrowRank a b = max (suc a) b

  Arrow : Ty Γ a → Ty Γ b → Ty Γ (arrowRank a b)
  Arrow A B = Pi A (subTy B (fstS id))

  bRank cRank : Nat → Nat → Nat → Nat
  bRank a b c = max 1 (max 1 (max 1
    (arrowRank (arrowRank b c)
      (arrowRank (arrowRank a b) (arrowRank a c)))))
  cRank a b c = max 1 (max 1 (max 1
    (arrowRank (arrowRank a (arrowRank b c))
      (arrowRank b (arrowRank a c)))))

  wRank : Nat → Nat → Nat
  wRank a b = max 1 (max 1
    (arrowRank (arrowRank a (arrowRank a b)) (arrowRank a b)))

  -- The type parameters are ordinary universe-valued arguments.
  -- Only their three ranks index these closed combinator families.
  module ThreeTypes (a b c : Nat) where
    ΓA = ext empty (U a)
    ΓAB = ext ΓA (U b)
    ΓABC = ext ΓAB (U c)
    TA : Ty ΓABC a
    TA = subTy (subTy (varEl a) (fstS id)) (fstS id)
    TB : Ty ΓABC b
    TB = subTy (varEl b) (fstS id)
    TC : Ty ΓABC c
    TC = varEl c

  -- BEGINBCKWTYPES
  BType : (a b c : Nat) → Ty empty (bRank a b c)
  BType a b c = Pi (U a) (Pi (U b) (Pi (U c)
    (Arrow (Arrow TB TC) (Arrow (Arrow TA TB) (Arrow TA TC)))))
    where open ThreeTypes a b c

  CType : (a b c : Nat) → Ty empty (cRank a b c)
  CType a b c = Pi (U a) (Pi (U b) (Pi (U c)
    (Arrow (Arrow TA (Arrow TB TC)) (Arrow TB (Arrow TA TC)))))
    where open ThreeTypes a b c

  WType : (a b : Nat) → Ty empty (wRank a b)
  WType a b = Pi (U a) (Pi (U b)
    (Arrow (Arrow TA (Arrow TA TB)) (Arrow TA TB)))
    where
    ΓA = ext empty (U a)
    ΓAB = ext ΓA (U b)
    TA : Ty ΓAB a
    TA = subTy (varEl a) (fstS id)
    TB : Ty ΓAB b
    TB = varEl b
  -- ENDBCKWTYPES

  PType : (a b : Nat) → Ty empty (suc (suc a))
  PType a b = Pi (U a) (Pi (Pi (varEl a) (U b)) (U (max (suc a) b)))
  P : Nat → Nat → Tm empty
  ElApp : {f x : Tm Γ} (d : Ap f x) (r : Nat)
        → apTy d ≡ (zero , U r) → Ty Γ r

  wk : (A : Ty Γ r) → Sub (ext Γ A) Γ
  wk A = fstS id
  q : (A : Ty Γ r) → Tm (ext Γ A)
  q A = sndS id
  qGuard : (A : Ty Γ r)
         → tyOf (q A) ≡ (r , subTy (subTy A (wk A)) id)
  appUType : (A : Ty Γ a) (r : Nat) (f x : Tm Γ)
             (pf : tyOf f ≡ (suc a , Pi A (U r)))
             (px : tyOf x ≡ (a , subTy A id))
           → tyOf (app-guarded A (U r) f x pf px) ≡ (zero , U r)
  appIdGuard : (A : Ty Γ a) (B : Ty (ext Γ A) b) (f x : Tm Γ)
               (pf : tyOf f ≡ (max (suc a) b , Pi A B))
               (px : tyOf x ≡ (a , subTy A id))
             → tyOf (app-guarded A B f x pf px)
               ≡ (b , subTy (subTy B (single A x px)) id)

  data Con where
    empty' : Con
    ext' : (Γ : Con) → Ty Γ r → Con
    setCon : isSet Con

  data Sub where
    id' : Sub Γ Γ
    comp' : Sub Δ Θ → Sub Γ Δ → Sub Γ Θ
    eps' : Sub Γ empty
    pair' : {A : Ty Δ r} (σ : Sub Γ Δ) (t : Tm Γ)
          → tyOf t ≡ (r , subTy A σ) → Sub Γ (ext Δ A)
    fstS' : {A : Ty Δ r} → Sub Γ (ext Δ A) → Sub Γ Δ
    id-left : (σ : Sub Γ Δ) → comp id σ ≡ σ
    id-right : (σ : Sub Γ Δ) → comp σ id ≡ σ
    assoc : (σ : Sub Θ Ξ) (τ : Sub Δ Θ) (ν : Sub Γ Δ)
          → comp (comp σ τ) ν ≡ comp σ (comp τ ν)
    eta-empty : (σ : Sub Γ empty) → σ ≡ eps
    beta-fst' : {A : Ty Δ r} (σ : Sub Γ Δ) (t : Tm Γ)
               (p : tyOf t ≡ (r , subTy A σ)) → fstS (pair σ t p) ≡ σ
    eta-pair : {A : Ty Δ r} (σ : Sub Γ (ext Δ A))
             → pair (fstS σ) (sndS σ) (sndType σ) ≡ σ
    pair-comp : {A : Ty Θ r} (σ : Sub Δ Θ) (t : Tm Δ)
                (p : tyOf t ≡ (r , subTy A σ)) (τ : Sub Γ Δ)
                (q : tyOf (subTm t τ) ≡ (r , subTy A (comp σ τ)))
              → comp (pair σ t p) τ ≡ pair (comp σ τ) (subTm t τ) q
    setSub : isSet (Sub Γ Δ)

  data Ty where
    subTy' : Ty Δ r → Sub Γ Δ → Ty Γ r
    ty-id' : (A : Ty Γ r) → subTy A id ≡ A
    ty-comp' : (A : Ty Θ r) (σ : Sub Δ Θ) (τ : Sub Γ Δ)
             → subTy (subTy A σ) τ ≡ subTy A (comp σ τ)
    U' : Nat → Ty Γ zero
    U-sub : (i : Nat) (σ : Sub Γ Δ) → subTy (U i) σ ≡ U i
    El' : (r : Nat) (t : Tm Γ) → tyOf t ≡ (zero , U r) → Ty Γ r
    El-sub : (r : Nat) (t : Tm Δ) (p : tyOf t ≡ (zero , U r))
             (σ : Sub Γ Δ) (q : tyOf (subTm t σ) ≡ (zero , U r))
           → subTy (El r t p) σ ≡ El r (subTm t σ) q
    El-univ : (i : Nat) → El zero (univ {Γ = Γ} i) (univType i) ≡ U i
    Pi' : (A : Ty Γ a) → Ty (ext Γ A) b → Ty Γ (max (suc a) b)
    Pi-sub : (A : Ty Δ a) (B : Ty (ext Δ A) b) (σ : Sub Γ Δ)
           → subTy (Pi A B) σ ≡ Pi (subTy A σ) (subTy B (lift σ A))
    beta-P : (a b : Nat) (A B : Tm Γ)
             (dA : Ap (subTm (P a b) eps) A) (dB : Ap (runAp dA) B)
             (pA : tyOf A ≡ (zero , U a))
             (dBx : Ap (subTm B (fstS {A = El a A pA} id)) (sndS id))
             (pBx : apTy dBx ≡ (zero , U b))
             (pP : apTy dB ≡ (zero , U (max (suc a) b)))
           → ElApp dB (max (suc a) b) pP
             ≡ Pi (El a A pA) (ElApp dBx b pBx)
    setTy : isSet (Ty Γ r)

  data Tm where
    subTm' : Tm Δ → Sub Γ Δ → Tm Γ
    sndS' : {A : Ty Δ r} → Sub Γ (ext Δ A) → Tm Γ
    tm-id : (t : Tm Γ) → subTm t id ≡ t
    tm-comp : (t : Tm Θ) (σ : Sub Δ Θ) (τ : Sub Γ Δ)
            → subTm (subTm t σ) τ ≡ subTm t (comp σ τ)
    beta-snd : {A : Ty Δ r} (σ : Sub Γ Δ) (t : Tm Γ)
               (p : tyOf t ≡ (r , subTy A σ))
               (q : (r , subTy A (fstS (pair σ t p))) ≡ tyOf t)
             → sndS (pair σ t p) ≡ t
    univ' : Nat → Tm Γ
    univ-sub : (i : Nat) (σ : Sub Γ Δ) → subTm (univ i) σ ≡ univ i
    app' : (A : Ty Γ a) (B : Ty (ext Γ A) b) (f x : Tm Γ)
         → tyOf f ≡ (max (suc a) b , Pi A B)
         → (px : tyOf x ≡ (a , subTy A id)) → Tm Γ
    I-atom : Nat → Tm empty
    K-atom P-atom : Nat → Nat → Tm empty
    B-atom C-atom : Nat → Nat → Nat → Tm empty
    W-atom : Nat → Nat → Tm empty
    -- These laws have fixed heads and fixed saturation arities.
    beta-I : (a : Nat) (sp : Spine (subTm (I-atom a) (eps {Γ = Γ})) 1)
             (x : Tm Γ) (dx : Ap (run sp) x)
           → apTy dx ≡ tyOf x → runAp dx ≡ x
    beta-K : (a b : Nat) (sp : Spine (subTm (K-atom a b) (eps {Γ = Γ})) 2)
             (x y : Tm Γ) (dx : Ap (run sp) x) (dy : Ap (runAp dx) y)
           → apTy dy ≡ tyOf x → runAp dy ≡ x
    beta-B : (a b c : Nat)
             (sp : Spine (subTm (B-atom a b c) (eps {Γ = Γ})) 3)
             (f g x : Tm Γ)
             (df : Ap (run sp) f) (dg : Ap (runAp df) g)
             (dx : Ap (runAp dg) x) (gx : Ap g x)
             (fgx : Ap f (runAp gx))
           → apTy dx ≡ apTy fgx → runAp dx ≡ runAp fgx
    beta-C : (a b c : Nat)
             (sp : Spine (subTm (C-atom a b c) (eps {Γ = Γ})) 3)
             (f x y : Tm Γ)
             (df : Ap (run sp) f) (dx : Ap (runAp df) x)
             (dy : Ap (runAp dx) y) (fy : Ap f y)
             (fyx : Ap (runAp fy) x)
           → apTy dy ≡ apTy fyx → runAp dy ≡ runAp fyx
    beta-W : (a b : Nat)
             (sp : Spine (subTm (W-atom a b) (eps {Γ = Γ})) 2)
             (f x : Tm Γ) (df : Ap (run sp) f) (dx : Ap (runAp df) x)
             (fx : Ap f x) (fxx : Ap (runAp fx) x)
           → apTy dx ≡ apTy fxx → runAp dx ≡ runAp fxx
    app-sub : {f x : Tm Δ} (d : Ap f x) (σ : Sub Γ Δ)
              (e : Ap (subTm f σ) (subTm x σ))
            → subRanked (apTy d) σ ≡ apTy e
            → subTm (runAp d) σ ≡ runAp e
    setTm-guarded : (t u : Tm Γ) (p q : t ≡ u)
                 → PathP (λ _ → tyOf t ≡ tyOf u)
                     (λ i → tyOf (p i)) (λ i → tyOf (q i)) → p ≡ q

  record Ap {Γ} f x where
    inductive
    constructor ap
    field
      domainRank codomainRank : Nat
      domain : Ty Γ domainRank
      codomain : Ty (ext Γ domain) codomainRank
      functionType : tyOf f ≡ (max (suc domainRank) codomainRank , Pi domain codomain)
      argumentType : tyOf x ≡ (domainRank , subTy domain id)
  open Ap

  data Spine {Γ} head where
    done : Spine head zero
    step : {n : Nat} (sp : Spine head n) (x : Tm Γ)
         → Ap (run sp) x → Spine head (suc n)

  runAp {f = f} {x = x} d = app-guarded (domain d) (codomain d) f x
    (functionType d) (argumentType d)
  apTy {x = x} d = codomainRank d ,
    subTy (codomain d) (single (domain d) x (argumentType d))
  run {h = h} done = h
  run (step sp x d) = runAp d

  empty = empty'
  ext = ext'
  id = id'
  comp = comp'
  eps = eps'
  pair = pair'
  fstS = fstS'
  sndS = sndS'
  subTy = subTy'
  subTm = subTm'
  ty-id = ty-id'
  ty-comp = ty-comp'
  beta-fst = beta-fst'
  U = U'
  univ = univ'
  El = El'
  Pi = Pi'
  app-guarded = app'
  P = P-atom

  tyOf (subTm' t σ) = subRanked (tyOf t) σ
  tyOf (sndS' {r = r} {A = A} σ) = r , subTy A (fstS σ)
  tyOf (tm-id t i) = fst (tyOf t) , ty-id (snd (tyOf t)) i
  tyOf (tm-comp t σ τ i) = fst (tyOf t) , ty-comp (snd (tyOf t)) σ τ i
  tyOf (beta-snd σ t p q i) = q i
  tyOf (univ' i) = zero , U zero
  tyOf (univ-sub i σ j) = zero , U-sub zero σ j
  tyOf (app' {b = b} A B f x pf px) = b , subTy B (single A x px)
  tyOf (I-atom a) = iRank a , IType a
  tyOf (K-atom a b) = kRank a b , KType a b
  tyOf (P-atom a b) = suc (suc a) , PType a b
  tyOf (B-atom a b c) = bRank a b c , BType a b c
  tyOf (C-atom a b c) = cRank a b c , CType a b c
  tyOf (W-atom a b) = wRank a b , WType a b
  tyOf (beta-I a sp x dx e i) = e i
  tyOf (beta-K a b sp x y dx dy e i) = e i
  tyOf (beta-B a b c sp f g x df dg dx gx fgx e i) = e i
  tyOf (beta-C a b c sp f x y df dx dy fy fyx e i) = e i
  tyOf (beta-W a b sp f x df dx fx fxx e i) = e i
  tyOf (app-sub d σ e p i) = p i
  tyOf (setTm-guarded t u p q e i j) = e i j

  sndType σ = refl
  univType i = refl
  liftType {r = r} σ A = λ i → r , ty-comp A σ (fstS id) i
  varUType r = λ i → zero , U-sub r (fstS id) i
  ElApp d r p = El r (runAp d) p
  qGuard {r = r} A = λ i → r , sym (ty-id (subTy A (wk A))) i
  appUType A r f x pf px = λ i → zero , U-sub r (single A x px) i
  appIdGuard {b = b} A B f x pf px =
    λ i → b , sym (ty-id (subTy B (single A x px))) i

rankedSet : ∀ {Γ} → isSet (RankedTy Γ)
rankedSet = isSetΣ isSetℕ (λ _ → setTy)

-- Derive the truncation guard outside the mutual block. Feeding isSetΣ
-- into tyOf inside that block obscures strict positivity from Agda.
setTm : ∀ {Γ} → isSet (Tm Γ)
setTm t u p q = setTm-guarded t u p q
  (rankedSet (tyOf t) (tyOf u) (cong tyOf p) (cong tyOf q))

-- Guards required by the structural path constructors are proved, not assumed.
beta-snd-derived : ∀ {Γ Δ r} {A : Ty Δ r} (σ : Sub Γ Δ) (t : Tm Γ)
                 (p : tyOf t ≡ (r , subTy A σ)) → sndS (pair σ t p) ≡ t
beta-snd-derived {r = r} {A = A} σ t p = beta-snd σ t p
  ((λ i → r , subTy A (beta-fst σ t p i)) ∙ sym p)

pair-comp-derived : ∀ {Γ Δ Θ r} {A : Ty Θ r} (σ : Sub Δ Θ) (t : Tm Δ)
                    (p : tyOf t ≡ (r , subTy A σ)) (τ : Sub Γ Δ)
                  → comp (pair σ t p) τ ≡ pair (comp σ τ) (subTm t τ)
                    (cong (λ X → subRanked X τ) p ∙
                      (λ i → r , ty-comp A σ τ i))
pair-comp-derived σ t p τ = pair-comp σ t p τ _

TmAt : (Γ : Con) {r : Nat} → Ty Γ r → Set
TmAt Γ {r} A = Σ (Tm Γ) (λ t → tyOf t ≡ (r , A))

-- User-facing application uses the ordinary argument type. The additional
-- guard at the primitive boundary is discharged by the type identity law.
-- BEGINAPPSIGNATURE
app : ∀ {Γ a b} (A : Ty Γ a) (B : Ty (ext Γ A) b) (f x : Tm Γ)
    → tyOf f ≡ (max (suc a) b , Pi A B)
    → tyOf x ≡ (a , A) → Tm Γ
app {a = a} A B f x pf px = app-guarded A B f x pf
  (px ∙ λ i → a , sym (ty-id A) i)
-- ENDAPPSIGNATURE

makeAp : ∀ {Γ a b} {f x : Tm Γ} (A : Ty Γ a) (B : Ty (ext Γ A) b)
       → tyOf f ≡ (max (suc a) b , Pi A B) → tyOf x ≡ (a , A) → Ap f x
makeAp {a = a} {b = b} A B pf px = ap a b A B pf
  (px ∙ λ i → a , sym (ty-id A) i)

ap-type : ∀ {Γ} {f x : Tm Γ} (d : Ap f x) → tyOf (runAp d) ≡ apTy d
ap-type d = refl

El-sub-guard : ∀ {Γ Δ} (r : Nat) (t : Tm Δ) (p : tyOf t ≡ (zero , U r))
              (σ : Sub Γ Δ) → tyOf (subTm t σ) ≡ (zero , U r)
El-sub-guard r t p σ = cong (λ X → subRanked X σ) p ∙
  (λ i → zero , U-sub r σ i)

El-sub-derived : ∀ {Γ Δ} (r : Nat) (t : Tm Δ) (p : tyOf t ≡ (zero , U r))
                (σ : Sub Γ Δ) → subTy (El r t p) σ
                ≡ El r (subTm t σ) (El-sub-guard r t p σ)
El-sub-derived r t p σ = El-sub r t p σ _

-- Each atom carries its fixed, literal ranked type.
B-check : (a b c : Nat) → TmAt empty (BType a b c)
B-check a b c = B-atom a b c , refl

C-check : (a b c : Nat) → TmAt empty (CType a b c)
C-check a b c = C-atom a b c , refl

W-check : (a b : Nat) → TmAt empty (WType a b)
W-check a b = W-atom a b , refl

-- Diagonal substitution contracts a contextual variable, reindexing every
-- dependent type at the same time; it is not a new closed combinator.
diagonal : ∀ {Γ r} (A : Ty Γ r) →
  Sub (ext Γ A) (ext (ext Γ A) (subTy A (wk A)))
diagonal A = pair id (q A) (qGuard A)

contract : ∀ {Γ r} (A : Ty Γ r) →
  Tm (ext (ext Γ A) (subTy A (wk A))) → Tm (ext Γ A)
contract A t = subTm t (diagonal A)

contract-type : ∀ {Γ r} (A : Ty Γ r)
  (t : Tm (ext (ext Γ A) (subTy A (wk A)))) →
  tyOf (contract A t) ≡ subRanked (tyOf t) (diagonal A)
contract-type A t = refl
