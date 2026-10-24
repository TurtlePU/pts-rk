{-# OPTIONS --cubical --safe --guardedness #-}
module SKDirectGround where

-- For ground OUTPUT type, direct weak SK evaluation already gives the
-- exact native-beta canonical representative. No lambda intermediate is
-- constructed by normalize or apply-and-normalize below.
open import PTSPrelude
import BinderFreeCore as SK
import BinderFreeCoherence as Weak
import BinderFreeQuotient as WQ
import BinderFreeBoundary as B
import SKCanonical as Canonical
import SKDirectSoundness as Direct
import BoundedReduction as R
import NativeTyping as T
open import Cubical.Relation.Nullary using (Dec; yes; no)

private
  variable
    A : SK.Ty

ground-normal-canonical : (n : SK.Nf SK.ι)
  → Canonical.normalize (SK.erase n) ≡ SK.erase n
ground-normal-canonical n with SK.ground-canonical n
... | k , p = cong Canonical.normalize (cong SK.erase p)
  ∙ Canonical.ground-computes k ∙ sym (cong SK.erase p)

-- BEGINSKDIRECTGROUND
normalize : SK.Tm SK.ι → SK.Tm SK.ι
normalize = Direct.direct

agrees : (t : SK.Tm SK.ι) → normalize t ≡ Canonical.normalize t
agrees t = sym (Direct.canonical-after-direct t ∙ ground-normal-canonical (Weak.nf t))

canonical : SK.Tm SK.ι → Canonical.Canonical SK.ι
canonical t = normalize t , ground-normal-canonical (Weak.nf t)

apply-and-normalize : Canonical.Canonical (A SK.⇒ SK.ι)
  → Canonical.Canonical A → Canonical.Canonical SK.ι
apply-and-normalize f x = canonical (fst f SK.· fst x)

application-agrees : (f : Canonical.Canonical (A SK.⇒ SK.ι))
  (x : Canonical.Canonical A)
  → apply-and-normalize f x ≡ Canonical.apply-and-normalize f x
application-agrees f x = Canonical.canonical-path (agrees (fst f SK.· fst x))
-- ENDSKDIRECTGROUND

forward : (t : SK.Tm SK.ι) → R.Steps (B.expand {zero} t) (B.expand (normalize t))
forward = Direct.direct-expands

typed : (t : SK.Tm SK.ι) → T.Typ T.empty (B.expand (normalize t)) (B.decode SK.ι)
typed = Direct.direct-typed

coherent : (t u : SK.Tm SK.ι) → T.Beta (B.expand {zero} t) (B.expand u)
  → normalize t ≡ normalize u
coherent t u p = agrees t ∙ Canonical.coherent t u p ∙ sym (agrees u)

reflects : (t u : SK.Tm SK.ι) → normalize t ≡ normalize u
  → T.Beta (B.expand {zero} t) (B.expand u)
reflects t u p = Canonical.reflects t u (sym (agrees t) ∙ p ∙ agrees u)

idempotent : (t : SK.Tm SK.ι) → normalize (normalize t) ≡ normalize t
idempotent = Direct.direct-idempotent

-- At ground type the weak and native-beta equivalences coincide, so the
-- native conversion decision itself can use only the direct weak evaluator.
native-to-weak : (t u : SK.Tm SK.ι) → T.Beta (B.expand {zero} t) (B.expand u)
  → Weak.WeakConversion t u
native-to-weak t u p = Weak.conversion-reflects
  (sym (Weak.nf-erase (Weak.nf t)) ∙ cong Weak.nf (coherent t u p)
    ∙ Weak.nf-erase (Weak.nf u))

conversion? : (t u : SK.Tm SK.ι) → Dec (T.Beta (B.expand {zero} t) (B.expand u))
conversion? t u with WQ.weak-conversion? t u
... | yes p = yes (Direct.weak-to-native p)
... | no bad = no (λ p → bad (native-to-weak t u p))

regression-identity : normalize (SK.identity SK.· SK.ground 7) ≡ SK.ground 7
regression-identity = refl

regression-constant : normalize (SK.K SK.· SK.ground 7 SK.· SK.ground 9) ≡ SK.ground 7
regression-constant = refl
