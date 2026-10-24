{-# OPTIONS --cubical --safe --guardedness #-}
module Combinatory where

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

  kRank : Nat → Nat → Nat
  kRank a b = max (suc zero)
    (max (suc zero) (max (suc a) (max (suc b) a)))

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

  tailRank : Nat → Nat → Nat → Nat
  tailRank a b c = max (suc (max (suc a) (max (suc b) c)))
    (max (suc (max (suc a) b)) (max (suc a) c))
  sRank : Nat → Nat → Nat → Nat
  sRank a b c = max 1 (max (suc (suc a))
    (max (suc (max (suc a) (suc b))) (tailRank a b c)))

  -- A fixed finite telescope. Every parameter added below is a path, never
  -- an arbitrary type, term, source derivation or telescope.
  module Template (a b c : Nat) where
    ΓA : Con
    ΓA = ext empty (U a)
    A₀ : Ty ΓA a
    A₀ = varEl {Γ = empty} a
    BCode : Ty ΓA (suc a)
    BCode = Pi A₀ (U b)
    ΓAB : Con
    ΓAB = ext ΓA BCode
    A₁ : Ty ΓAB a
    A₁ = subTy A₀ (wk BCode)
    A₂ : Ty (ext ΓAB A₁) a
    A₂ = subTy A₁ (wk A₁)
    Bvar : Tm ΓAB
    Bvar = q BCode
    Bweak : Tm (ext ΓAB A₁)
    Bweak = subTm Bvar (wk A₁)
    BGuard : Set
    BGuard = tyOf Bweak ≡ (suc a , Pi A₂ (U b))

    module One (pB : BGuard) where
      Bx : Tm (ext ΓAB A₁)
      Bx = app-guarded A₂ (U b) Bweak (q A₁) pB (qGuard A₁)
      BFamily : Ty (ext ΓAB A₁) b
      BFamily = El b Bx (appUType A₂ b Bweak (q A₁) pB (qGuard A₁))
      CCode : Ty ΓAB (max (suc a) (suc b))
      CCode = Pi A₁ (Pi BFamily (U c))
      ΓABC : Con
      ΓABC = ext ΓAB CCode
      A₃ : Ty ΓABC a
      A₃ = subTy A₁ (wk CCode)
      B₃ : Ty (ext ΓABC A₃) b
      B₃ = subTy BFamily (lift (wk CCode) A₁)
      Cvar : Tm ΓABC
      Cvar = q CCode
      A₄ : Ty (ext ΓABC A₃) a
      A₄ = subTy A₃ (wk A₃)
      B₄ : Ty (ext (ext ΓABC A₃) A₄) b
      B₄ = subTy B₃ (lift (wk A₃) A₃)
      Cweak : Tm (ext ΓABC A₃)
      Cweak = subTm Cvar (wk A₃)
      CGuard : Set
      CGuard = tyOf Cweak ≡ (max (suc a) (suc b) , Pi A₄ (Pi B₄ (U c)))

    module Two (pB : BGuard) (pC : One.CGuard pB) where
      open One pB public
      Cx : Tm (ext ΓABC A₃)
      Cx = app-guarded A₄ (Pi B₄ (U c)) Cweak (q A₃) pC (qGuard A₃)
      CxGuard : Set
      CxGuard = tyOf Cx ≡ (suc b , Pi B₃ (U c))

    module Three (pB : BGuard) (pC : One.CGuard pB)
                 (pCx : Two.CxGuard pB pC) where
      open Two pB pC public
      B₅ : Ty (ext (ext ΓABC A₃) B₃) b
      B₅ = subTy B₃ (wk B₃)
      CxWeak : Tm (ext (ext ΓABC A₃) B₃)
      CxWeak = subTm Cx (wk B₃)
      CxWeakGuard : Set
      CxWeakGuard = tyOf CxWeak ≡ (suc b , Pi B₅ (U c))

    module Four (pB : BGuard) (pC : One.CGuard pB)
                (pCx : Two.CxGuard pB pC)
                (pCw : Three.CxWeakGuard pB pC pCx) where
      open Three pB pC pCx public
      Cxy : Tm (ext (ext ΓABC A₃) B₃)
      Cxy = app-guarded B₅ (U c) CxWeak (q B₃) pCw (qGuard B₃)
      F : Ty ΓABC (max (suc a) (max (suc b) c))
      F = Pi A₃ (Pi B₃
        (El c Cxy (appUType B₅ c CxWeak (q B₃) pCw (qGuard B₃))))
      ΓABCf : Con
      ΓABCf = ext ΓABC F
      A₆ : Ty ΓABCf a
      A₆ = subTy A₃ (wk F)
      B₆ : Ty (ext ΓABCf A₆) b
      B₆ = subTy B₃ (lift (wk F) A₃)
      G : Ty ΓABCf (max (suc a) b)
      G = Pi A₆ B₆
      ΓABCfg : Con
      ΓABCfg = ext ΓABCf G
      A₇ : Ty ΓABCfg a
      A₇ = subTy A₆ (wk G)
      B₇ : Ty (ext ΓABCfg A₇) b
      B₇ = subTy B₆ (lift (wk G) A₆)
      ΓABCfgx : Con
      ΓABCfgx = ext ΓABCfg A₇
      A₈ : Ty ΓABCfgx a
      A₈ = subTy A₇ (wk A₇)
      B₈ : Ty (ext ΓABCfgx A₈) b
      B₈ = subTy B₇ (lift (wk A₇) A₇)
      gFun : Tm ΓABCfgx
      gFun = subTm (q G) (wk A₇)
      cFun : Tm ΓABCfgx
      cFun = subTm (subTm (subTm Cvar (wk F)) (wk G)) (wk A₇)
      GGuard : Set
      GGuard = tyOf gFun ≡ (max (suc a) b , Pi A₈ B₈)
      DiagCGuard : Set
      DiagCGuard = tyOf cFun ≡
        (max (suc a) (suc b) , Pi A₈ (Pi B₈ (U c)))

    module Five (pB : BGuard) (pC : One.CGuard pB)
                (pCx : Two.CxGuard pB pC)
                (pCw : Three.CxWeakGuard pB pC pCx)
                (pG : Four.GGuard pB pC pCx pCw)
                (pD : Four.DiagCGuard pB pC pCx pCw) where
      open Four pB pC pCx pCw public
      σx : Sub ΓABCfgx (ext ΓABCfgx A₈)
      σx = single A₈ (q A₇) (qGuard A₇)
      BxDiag : Ty ΓABCfgx b
      BxDiag = subTy B₈ σx
      gx : Tm ΓABCfgx
      gx = app-guarded A₈ B₈ gFun (q A₇) pG (qGuard A₇)
      cx : Tm ΓABCfgx
      cx = app-guarded A₈ (Pi B₈ (U c)) cFun (q A₇) pD (qGuard A₇)
      DiagCxGuard : Set
      DiagCxGuard = tyOf cx ≡ (suc b , Pi BxDiag (U c))
      gxGuard : tyOf gx ≡ (b , subTy BxDiag id)
      gxGuard = appIdGuard A₈ B₈ gFun (q A₇) pG (qGuard A₇)

    module Six (pB : BGuard) (pC : One.CGuard pB)
               (pCx : Two.CxGuard pB pC)
               (pCw : Three.CxWeakGuard pB pC pCx)
               (pG : Four.GGuard pB pC pCx pCw)
               (pD : Four.DiagCGuard pB pC pCx pCw)
               (pDx : Five.DiagCxGuard pB pC pCx pCw pG pD) where
      open Five pB pC pCx pCw pG pD public
      cxgx : Tm ΓABCfgx
      cxgx = app-guarded BxDiag (U c) cx gx pDx gxGuard
      body : Ty ΓABCfgx c
      body = El c cxgx (appUType BxDiag c cx gx pDx gxGuard)
      theType : Ty empty (sRank a b c)
      theType = Pi (U a) (Pi BCode (Pi CCode (Pi F (Pi G (Pi A₇ body)))))

    Guards : Set
    Guards = Σ BGuard λ pB → Σ (One.CGuard pB) λ pC →
      Σ (Two.CxGuard pB pC) λ pCx → Σ (Three.CxWeakGuard pB pC pCx) λ pCw →
      Σ (Four.GGuard pB pC pCx pCw) λ pG →
      Σ (Four.DiagCGuard pB pC pCx pCw) λ pD → Five.DiagCxGuard pB pC pCx pCw pG pD

    typeOfS : Guards → Ty empty (sRank a b c)
    typeOfS (pB , pC , pCx , pCw , pG , pD , pDx) = Six.theType pB pC pCx pCw pG pD pDx

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
    K-atom P-atom : Nat → Nat → Tm empty
    S-guarded : (a b c : Nat) → Template.Guards a b c → Tm empty
    -- These laws have fixed heads and fixed saturation arities.
    beta-K : (a b : Nat) (sp : Spine (subTm (K-atom a b) (eps {Γ = Γ})) 2)
             (x y : Tm Γ) (dx : Ap (run sp) x) (dy : Ap (runAp dx) y)
           → apTy dy ≡ tyOf x → runAp dy ≡ x
    beta-S : (a b c : Nat) (guards : Template.Guards a b c)
             (sp : Spine (subTm (S-guarded a b c guards) (eps {Γ = Γ})) 3)
             (f g x : Tm Γ)
             (df : Ap (run sp) f) (dg : Ap (runAp df) g)
             (dx : Ap (runAp dg) x)
             (fx : Ap f x) (gx : Ap g x)
             (fxgx : Ap (runAp fx) (runAp gx))
           → apTy dx ≡ apTy fxgx → runAp dx ≡ runAp fxgx
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
  tyOf (K-atom a b) = kRank a b , KType a b
  tyOf (P-atom a b) = suc (suc a) , PType a b
  tyOf (S-guarded a b c guards) = sRank a b c , Template.typeOfS a b c guards
  tyOf (beta-K a b sp x y dx dy e i) = e i
  tyOf (beta-S a b c guards sp f g x df dg dx fx gx fxgx e i) = e i
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

-- Identity is a derived SK expression, not a primitive term or equation.
-- This law applies to certified instantiations of S K K. Its arguments
-- expose the necessary type instantiations; it is not a construction of
-- a closed universe-polymorphic identity or a completeness theorem.
skk-computes : ∀ {Γ} (a b c ka kb la lb : Nat)
  (guards : Template.Guards a b c)
  (s : Spine (subTm (S-guarded a b c guards) (eps {Γ = Γ})) 3)
  (k : Spine (subTm (K-atom ka kb) (eps {Γ = Γ})) 2)
  (l : Spine (subTm (K-atom la lb) (eps {Γ = Γ})) 2)
  (x : Tm Γ)
  (df : Ap (run s) (run k)) (dg : Ap (runAp df) (run l))
  (dx : Ap (runAp dg) x)
  (fx : Ap (run k) x) (gx : Ap (run l) x)
  (fxgx : Ap (runAp fx) (runAp gx))
  → apTy dx ≡ apTy fxgx → apTy fxgx ≡ tyOf x
  → runAp dx ≡ x
skk-computes a b c ka kb la lb guards s k l x df dg dx fx gx fxgx p q =
  beta-S a b c guards s (run k) (run l) x df dg dx fx gx fxgx p ∙
  beta-K ka kb k x (runAp gx) fx fxgx q
