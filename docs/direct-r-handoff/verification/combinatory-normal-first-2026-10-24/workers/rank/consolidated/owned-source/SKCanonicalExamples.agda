{-# OPTIONS --cubical --safe --guardedness #-}
module SKCanonicalExamples where

-- Computation regressions for the public canonicalizer: every positive
-- example is definitional equality, not a transport through correctness.
open import PTSPrelude
open import Cubical.Data.Empty using (⊥)
open import BinderFreeCore using (ι; _⇒_)
open import SKSource using (Source; ε; _▻_; lam; var; vz; vs; app; ground)
import BinderFreeCore as SK
import BinderFreeBoundary as B
import SKSourceNormal as SN
import SKCanonical as C

identity-source : Source ε (ι ⇒ ι)
identity-source = lam (var vz)

identity-budget : SN.budget identity-source ≡ 0
identity-budget = refl

source-identity-computes : SN.normalize identity-source ≡ identity-source
source-identity-computes = refl

application-budget : SN.budget (app identity-source (ground 7)) ≡ 1
application-budget = refl

source-application-computes : SN.normalize (app identity-source (ground 7)) ≡ ground 7
source-application-computes = refl

under-lambda-computes : SN.normalize
  (app (lam (lam {A = ι} (var (vs vz)))) (ground {Γ = ε} 7))
  ≡ lam (ground 7)
under-lambda-computes = refl

created-redex-computes : SN.normalize
  (app (lam (app (var vz) (ground {Γ = ε ▻ (ι ⇒ ι)} 7)))
    (lam (var vz))) ≡ ground 7
created-redex-computes = refl

-- BEGINSKCANONICALCOMPUTATION
identity-computes : C.normalize (SK.identity {ι}) ≡ SK.identity
identity-computes = refl

identity-applies : C.normalize (SK.identity SK.· SK.ground 7) ≡ SK.ground 7
identity-applies = refl

alternate-identity-computes : C.normalize B.alternate-code ≡ SK.identity
alternate-identity-computes = refl

canonical-application-computes :
  fst (C.apply-and-normalize (C.canonical (SK.identity {ι})) (C.canonical (SK.ground 7)))
    ≡ SK.ground 7
canonical-application-computes = refl
-- ENDSKCANONICALCOMPUTATION

eta-remains-distinct : C.normalize B.eta-code ≡ C.normalize B.arrow-identity-code → ⊥
eta-remains-distinct e = B.eta-not-beta-identity
  (C.reflects B.eta-code B.arrow-identity-code e)
