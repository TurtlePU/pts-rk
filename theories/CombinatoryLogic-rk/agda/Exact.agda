{-# OPTIONS --cubical --safe --guardedness #-}
module Exact where

open import PTSPrelude

-- A relative construction, parameterized by the original annotated syntax,
-- its typing and beta equality, and the expansion of applicative codes.
-- No soundness, reflection or completeness theorem is assumed here.
module Relative (Raw Code : Set) (expand : Code → Raw)
                (Typ Beta : Raw → Raw → Set) (Uraw : Nat → Raw) where

  data TyExact : Nat → Set
  data TmExact : Set

  RankedTyExact : Set
  RankedTyExact = Σ Nat TyExact

  tyOfExact : TmExact → RankedTyExact

  -- BEGINEXACT
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
  -- ENDEXACT

  -- Recover terms at a specified ranked type by a fibre, not a data index.
  TmAtExact : RankedTyExact → Set
  TmAtExact A = Σ TmExact (λ t → tyOfExact t ≡ A)

  -- The recursive type function respects every term path, uniformly.
  typeRespect : {t u : TmExact} → t ≡ u → tyOfExact t ≡ tyOfExact u
  typeRespect = cong tyOfExact

  -- Native reflexivity, not truncation alone, identifies duplicate typing
  -- witnesses. No property of the supplied relation is silently assumed.
  typeWitnesses : (reflexive : (A : Raw) → Beta A A) {r : Nat}
                  (A : Raw) (d e : Typ A (Uraw r)) → ty A d ≡ ty A e
  typeWitnesses reflexive A d e = tyBeta A A d e (reflexive A)

  termWitnesses : (reflexive : (A : Raw) → Beta A A) {r : Nat}
                  (A : Raw) (d e : Typ A (Uraw r)) (p : Code)
                  (h k : Typ (expand p) A) → tm A d p h ≡ tm A e p k
  termWitnesses reflexive A d e p h k =
    tmBeta A A d e p p h k (reflexive A) (reflexive (expand p))

  -- Ordinary inductive representatives retain explicit typed beta witnesses.
  -- These definitions do not use quotient path constructors.
  data TyRep (r : Nat) : Set where
    tyRep : (A : Raw) → Typ A (Uraw r) → TyRep r

  data TmRep : Set where
    tmRep : {r : Nat} (A : Raw) → Typ A (Uraw r)
          → (p : Code) → Typ (expand p) A → TmRep

  tyOfRep : TmRep → Σ Nat TyRep
  tyOfRep (tmRep {r} A dA p h) = r , tyRep A dA

  EqTy : {r : Nat} → TyRep r → TyRep r → Set
  EqTy (tyRep A dA) (tyRep B dB) = Beta A B

  data EqRanked : Σ Nat TyRep → Σ Nat TyRep → Set where
    sameRank : {r : Nat} {A B : TyRep r}
             → EqTy A B → EqRanked (r , A) (r , B)

  data EqTm : TmRep → TmRep → Set where
    termBeta : {r : Nat} {A B : Raw}
               {dA : Typ A (Uraw r)} {dB : Typ B (Uraw r)}
               {p q : Code} {h : Typ (expand p) A} {k : Typ (expand q) B}
             → Beta A B → Beta (expand p) (expand q)
             → EqTm (tmRep A dA p h) (tmRep B dB q k)

  typeRespectRep : {t u : TmRep}
                 → EqTm t u → EqRanked (tyOfRep t) (tyOfRep u)
  typeRespectRep (termBeta e v) = sameRank e
