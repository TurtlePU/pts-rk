{-# OPTIONS --cubical --safe --guardedness #-}
module SKCanonical where

-- Canonical SK OUTPUTS for original beta equality of the simply typed
-- surface. The reference algorithm uses intrinsic lambda syntax internally;
-- it is not a direct binder-free reduction strategy or a dependent compiler.
open import PTSPrelude
open import NativeTyping using (Beta; beta-refl; beta-sym; beta-trans)
open import NativeInversion using (beta-path)
open import NativeConfluence using (steps-beta)
open import NativeAlgebra using (beta-app)
open import Cubical.Data.Sigma using (Σ≡Prop)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Foundations.Prelude using (isProp→isSet)
open import Cubical.Foundations.Isomorphism using (Iso; iso)
open import Cubical.Relation.Nullary using (Dec; yes; no; Discrete→isSet)
import Cubical.HITs.SetQuotients as Q
import BinderFreeCore as SK
import BinderFreeBoundary as B
import BinderFreeBidirectional as Bidirectional
import BinderFreeEquality as Equality
import SKSource as Source
import SKSourceNormal as SN
import SKBracket as C
import SKCanonicalNormal as CN
import SKNativeCanonical as Reference

private
  variable
    A D : SK.Ty

-- BEGINSKCANONICAL
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
-- ENDSKCANONICAL

normal-form : SK.Tm A → SK.Nf A
normal-form t = fst (CN.compiled-normal (SN.normalize (C.expand-source t))
  (SN.normal (C.expand-source t)))

normal-form-erases : (t : SK.Tm A) → SK.erase (normal-form t) ≡ normalize t
normal-form-erases t = snd (CN.compiled-normal (SN.normalize (C.expand-source t))
  (SN.normal (C.expand-source t)))

irreducible : (t : SK.Tm A) {u : SK.Tm A} → normalize t SK.↝ u → ⊥
irreducible t = CN.compiled-irreducible (SN.normalize (C.expand-source t))
  (SN.normal (C.expand-source t))

-- Equality observes every annotation, including hidden intermediate types.
term-equality? : (t u : SK.Tm A) → Dec (t ≡ u)
term-equality? t u with Equality.raw-discrete (Bidirectional.forget t) (Bidirectional.forget u)
... | yes e = yes (Equality.forget-injective e)
... | no bad = no (λ e → bad (cong Bidirectional.forget e))

term-isSet : isSet (SK.Tm A)
term-isSet = Discrete→isSet term-equality?

Canonical : SK.Ty → Set
Canonical A = Σ (SK.Tm A) (λ t → normalize t ≡ t)

canonical-isSet : isSet (Canonical A)
canonical-isSet = isSetΣ term-isSet (λ _ → isProp→isSet (term-isSet _ _))

canonical-path : {p q : Canonical A} → fst p ≡ fst q → p ≡ q
canonical-path = Σ≡Prop (λ _ → term-isSet _ _)

canonical : SK.Tm A → Canonical A
canonical t = normalize t , idempotent t

canonical-equality? : (p q : Canonical A) → Dec (p ≡ q)
canonical-equality? p q with term-equality? (fst p) (fst q)
... | yes e = yes (canonical-path e)
... | no bad = no (λ e → bad (cong fst e))

-- BEGINSKCANONICALAPPLY
apply-and-normalize : Canonical (A SK.⇒ D) → Canonical A → Canonical D
apply-and-normalize f x = canonical (fst f SK.· fst x)

apply-sound : (f : Canonical (A SK.⇒ D)) (x : Canonical A)
  → Beta (B.expand {zero} (fst (apply-and-normalize f x)))
      (B.expand (fst f SK.· fst x))
apply-sound f x = sound (fst f SK.· fst x)
-- ENDSKCANONICALAPPLY

-- This is the native-beta quotient, not the smaller weak SK quotient.
normalizeQ : Reference.Quotient A → Canonical A
normalizeQ = Q.rec canonical-isSet canonical
  (λ t u e → canonical-path (coherent t u e))

quoteQ : Canonical A → Reference.Quotient A
quoteQ n = Q.[ fst n ]

normalize-quote : (n : Canonical A) → normalizeQ (quoteQ n) ≡ n
normalize-quote n = canonical-path (snd n)

quote-normalize : (q : Reference.Quotient A) → quoteQ (normalizeQ q) ≡ q
quote-normalize = Q.elimProp (λ _ → Q.squash/ _ _)
  (λ t → Q.eq/ (normalize t) t (sound t))

quotient-canonical-iso : Iso (Reference.Quotient A) (Canonical A)
quotient-canonical-iso = iso normalizeQ quoteQ normalize-quote quote-normalize

application-agrees : (f : Reference.Quotient (A SK.⇒ D)) (x : Reference.Quotient A)
  → normalizeQ (Reference.applyQ f x) ≡ apply-and-normalize (normalizeQ f) (normalizeQ x)
application-agrees = Q.elimProp2 (λ _ _ → canonical-isSet _ _)
  (λ f x → canonical-path (coherent (f SK.· x) (normalize f SK.· normalize x)
    (beta-app (beta-sym (sound f)) (beta-sym (sound x)))))

-- Checking still decides the independent declarative SK judgment. Accepted
-- elaborations now share the beta-faithful canonical operation above.
record CheckedCanonical (t : Bidirectional.Raw) (A : SK.Ty) : Set where
  constructor checked
  field
    typing : Bidirectional.Typing t A
    output : Canonical A
    agrees : Beta (B.expand {zero} (fst output)) (B.expand (Bidirectional.elaborate typing))

check-canonical : (t : Bidirectional.Raw) (A : SK.Ty) → Dec (CheckedCanonical t A)
check-canonical t A with Bidirectional.check t A
... | yes d = yes (checked d (canonical (Bidirectional.elaborate d))
    (sound (Bidirectional.elaborate d)))
... | no bad = no (λ r → bad (CheckedCanonical.typing r))

distinct-identities-agree : normalize B.alternate-code ≡ normalize B.identity-code
distinct-identities-agree = coherent B.alternate-code B.identity-code B.same-native-beta

eta-remains-distinct : normalize B.eta-code ≡ normalize B.arrow-identity-code → ⊥
eta-remains-distinct e = B.eta-not-beta-identity (reflects B.eta-code B.arrow-identity-code e)

ground-computes : (n : Nat) → normalize (SK.ground n) ≡ SK.ground n
ground-computes n = refl
