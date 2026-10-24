{-# OPTIONS --cubical --safe --guardedness #-}
module SKNativeCanonical where

-- A beta-faithful reference for the SK surface, using the ORIGINAL native
-- normalizer. The output retains lambda binders and all type annotations.
-- Recompilation to canonical SK codes is a separate, unassumed obligation.
open import PTSPrelude
open import BoundedReduction using (Normal; normal-isProp; Steps; app)
open import NativeTyping using (Term; Typ; Beta; empty; wf-empty; beta-refl)
open import NativeCertificates using (term-discrete)
open import NativeAlgebra using (beta-app)
open import BinderFreeBoundary using (decode; expand; expand-typed)
import BinderFreeBoundary as Boundary
import BinderFreeCore as SK
import NativeNormalization as Native
import NativeRankCoverage as Coverage
open import Cubical.Relation.Nullary using (Dec; yes; no; Discrete→isSet)
open import Cubical.Foundations.HLevels using (isPropΠ)
open import Cubical.Data.Empty using (⊥)
import Cubical.HITs.SetQuotients as Q

private
  variable
    A D : SK.Ty

-- BEGINSKNATIVECANONICAL
budget : SK.Tm A → Nat
budget t = Coverage.rank-budget wf-empty (expand-typed empty t)

reference : (t : SK.Tm A)
  → Native.Normalized empty (expand t) (decode A) (budget t)
reference t = Coverage.normalize-typed wf-empty (expand-typed empty t)

source-normal : SK.Tm A → Term zero
source-normal t = Native.nf (reference t)

source-coherent : (t : SK.Tm A) (u : SK.Tm D)
  → Beta (expand t) (expand u) → source-normal t ≡ source-normal u
source-coherent t u = Native.normalization-coherent (reference t) (reference u)

source-reflects : (t : SK.Tm A) (u : SK.Tm D)
  → source-normal t ≡ source-normal u → Beta (expand t) (expand u)
source-reflects t u = Native.normalization-reflects (reference t) (reference u)
-- ENDSKNATIVECANONICAL

source-normal-normal : (t : SK.Tm A) → Normal (source-normal t)
source-normal-normal t = Native.nf-normal (reference t)

source-normal-typed : (t : SK.Tm A)
  → Typ empty (source-normal t) (decode A)
source-normal-typed t = Native.nf-typed (reference t)

source-reduces : (t : SK.Tm A) → Steps (expand t) (source-normal t)
source-reduces t = Native.nf-reduces (reference t)

source-beta? : (t : SK.Tm A) (u : SK.Tm D) → Dec (Beta (expand t) (expand u))
source-beta? t u with term-discrete (source-normal t) (source-normal u)
... | yes eq = yes (source-reflects t u eq)
... | no bad = no (λ e → bad (source-coherent t u e))

-- Idempotence is asserted for the native output, not for unconstructed SK
-- reification. A fresh automatically computed rank budget suffices.
source-idempotent : (t : SK.Tm A)
  → Native.nf (Coverage.normalize-typed wf-empty (source-normal-typed t))
    ≡ source-normal t
source-idempotent t = Native.normal-convertible-unique
  (Coverage.normalize-typed wf-empty (source-normal-typed t))
  (source-normal-normal t) beta-refl

-- This is apply-and-normalize by EXPANSION; it is not the direct weak SK
-- algorithm and does not return a binder-free canonical representative.
apply-and-normalize : (f : SK.Tm (A SK.⇒ D)) (x : SK.Tm A)
  → Native.Normalized empty (app (expand f) (expand x)) (decode D)
      (budget (f SK.· x))
apply-and-normalize f x = reference (f SK.· x)

-- The reference recognizes the native identification missed by ordinary
-- weak combinator normal forms and still rejects function eta.
distinct-spines-agree : source-normal Boundary.alternate-code
  ≡ source-normal Boundary.identity-code
distinct-spines-agree = source-coherent Boundary.alternate-code
  Boundary.identity-code Boundary.same-native-beta

eta-still-distinct : source-normal Boundary.eta-code
  ≡ source-normal Boundary.arrow-identity-code → ⊥
eta-still-distinct eq = Boundary.eta-not-beta-identity
  (source-reflects Boundary.eta-code Boundary.arrow-identity-code eq)

-- Unlike the weak-combinatory quotient, this actual set quotient identifies
-- exactly the source codes whose ORIGINAL annotated expansions are beta equal.
Quotient : SK.Ty → Set
Quotient A = SK.Tm A Q./ (λ t u → Beta (expand {zero} t) (expand u))

private
  native-isSet : isSet (Term zero)
  native-isSet = Discrete→isSet term-discrete

normalizeQ : Quotient A → Term zero
normalizeQ = Q.rec native-isSet source-normal source-coherent

normalizeQ-normal : (q : Quotient A) → Normal (normalizeQ q)
normalizeQ-normal = Q.elimProp (λ _ → normal-isProp) source-normal-normal

normalizeQ-injective : (p q : Quotient A)
  → normalizeQ p ≡ normalizeQ q → p ≡ q
normalizeQ-injective = Q.elimProp2 (λ p q → isPropΠ (λ _ → Q.squash/ p q))
  (λ t u eq → Q.eq/ t u (source-reflects t u eq))

quotient-equality? : (p q : Quotient A) → Dec (p ≡ q)
quotient-equality? p q with term-discrete (normalizeQ p) (normalizeQ q)
... | yes eq = yes (normalizeQ-injective p q eq)
... | no bad = no (λ eq → bad (cong normalizeQ eq))

applyQ : Quotient (A SK.⇒ D) → Quotient A → Quotient D
applyQ = Q.rec2 Q.squash/ (λ f x → Q.[ f SK.· x ])
  (λ f g x e → Q.eq/ (f SK.· x) (g SK.· x) (beta-app e beta-refl))
  (λ f x y e → Q.eq/ (f SK.· x) (f SK.· y) (beta-app beta-refl e))

applyQ-represents : (f : SK.Tm (A SK.⇒ D)) (x : SK.Tm A)
  → applyQ Q.[ f ] Q.[ x ] ≡ Q.[ f SK.· x ]
applyQ-represents f x = refl
