{-# OPTIONS --cubical --safe --guardedness #-}
module SKFastCanonical where

-- The same canonical SK trees, using a syntax-only sufficient rank budget.
-- This removes proof-derived budget computation; it does not claim a new
-- asymptotic runtime bound or a lambda-free implementation.
open import PTSPrelude
open import NativeTyping using (Beta)
open import Cubical.Data.Empty using (⊥)
import BinderFreeCore as SK
import BinderFreeBoundary as B
import SKSourceFast as Fast
import SKBracket as Bracket
import SKCanonical as Reference
import SKCanonicalNormal as CN

private
  variable
    A D : SK.Ty

-- BEGIN SK FAST CANONICAL
normalize : SK.Tm A → SK.Tm A
normalize t = Bracket.compile (Fast.normalize (Bracket.expand-source t))

agrees : (t : SK.Tm A) → normalize t ≡ Reference.normalize t
agrees t = cong Bracket.compile (Fast.agrees (Bracket.expand-source t))

canonical : SK.Tm A → Reference.Canonical A
canonical t = normalize t ,
  (cong Reference.normalize (agrees t) ∙ Reference.idempotent t ∙ sym (agrees t))

apply-and-normalize : Reference.Canonical (A SK.⇒ D) → Reference.Canonical A
  → Reference.Canonical D
apply-and-normalize f x = canonical (fst f SK.· fst x)
-- END SK FAST CANONICAL

sound : (t : SK.Tm A) → Beta (B.expand {zero} (normalize t)) (B.expand t)
sound t = subst (λ u → Beta (B.expand u) (B.expand t))
  (sym (agrees t)) (Reference.sound t)

coherent : (t u : SK.Tm A)
  → Beta (B.expand {zero} t) (B.expand u) → normalize t ≡ normalize u
coherent t u e = agrees t ∙ Reference.coherent t u e ∙ sym (agrees u)

reflects : (t u : SK.Tm A) → normalize t ≡ normalize u
  → Beta (B.expand {zero} t) (B.expand u)
reflects t u e = Reference.reflects t u (sym (agrees t) ∙ e ∙ agrees u)

idempotent : (t : SK.Tm A) → normalize (normalize t) ≡ normalize t
idempotent t = coherent (normalize t) t (sound t)

normal-form : SK.Tm A → SK.Nf A
normal-form t = fst (CN.compiled-normal (Fast.normalize (Bracket.expand-source t))
  (Fast.normal (Bracket.expand-source t)))

normal-form-erases : (t : SK.Tm A) → SK.erase (normal-form t) ≡ normalize t
normal-form-erases t = snd (CN.compiled-normal (Fast.normalize (Bracket.expand-source t))
  (Fast.normal (Bracket.expand-source t)))

irreducible : (t : SK.Tm A) {u : SK.Tm A} → normalize t SK.↝ u → ⊥
irreducible t = CN.compiled-irreducible (Fast.normalize (Bracket.expand-source t))
  (Fast.normal (Bracket.expand-source t))

application-agrees : (f : Reference.Canonical (A SK.⇒ D)) (x : Reference.Canonical A)
  → apply-and-normalize f x ≡ Reference.apply-and-normalize f x
application-agrees f x = Reference.canonical-path (agrees (fst f SK.· fst x))

identity-computes : normalize (SK.identity {SK.ι}) ≡ SK.identity
identity-computes = refl

identity-applies : normalize (SK.identity SK.· SK.ground 7) ≡ SK.ground 7
identity-applies = refl

alternate-identity-computes : normalize B.alternate-code ≡ SK.identity
alternate-identity-computes = refl

canonical-application-computes :
  fst (apply-and-normalize (canonical (SK.identity {SK.ι})) (canonical (SK.ground 7)))
    ≡ SK.ground 7
canonical-application-computes = refl

eta-remains-distinct : normalize B.eta-code ≡ normalize B.arrow-identity-code → ⊥
eta-remains-distinct e = B.eta-not-beta-identity
  (reflects B.eta-code B.arrow-identity-code e)
