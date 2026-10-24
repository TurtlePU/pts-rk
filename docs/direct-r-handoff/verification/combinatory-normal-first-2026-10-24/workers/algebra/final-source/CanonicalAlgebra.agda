{-# OPTIONS --cubical --safe --guardedness #-}
module CanonicalAlgebra where

-- A quotient-free, normal-form-first algebra for the simply typed SK
-- fragment. Types are computed from terms; typed terms are its fibres.
-- Ordinary Sigma types suffice here: this is not a dependent PTS IIRT,
-- nor a new termination proof for simultaneous hereditary substitution.
open import PTSPrelude
open import Cubical.Foundations.Prelude using (J; substRefl)
open import Cubical.Foundations.Isomorphism using (Iso; iso)
open import Cubical.Relation.Nullary using (Dec; yes; no)
import BinderFreeCore as SK
import BinderFreeBoundary as B
import SKCanonical as C
import NativeTyping as N

private
  variable
    A D : SK.Ty

-- BEGINCANONICALALGEBRA
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
-- ENDCANONICALALGEBRA

at-embed : (t : C.Canonical A) → at (embed t) ≡ t
at-embed t = substRefl {B = C.Canonical} t

embed-at : (t : TmAt A) → embed (at t) ≡ t
embed-at ((B , t) , p) = J
  (λ A p → embed (subst C.Canonical p t) ≡ ((B , t) , p))
  (cong embed (substRefl {B = C.Canonical} t)) p

fibre-iso : Iso (C.Canonical A) (TmAt A)
fibre-iso = iso embed at embed-at at-embed

at-injective : (t u : TmAt A) → at t ≡ at u → t ≡ u
at-injective t u p = sym (embed-at t) ∙ cong embed p ∙ embed-at u

equality? : (t u : TmAt A) → Dec (t ≡ u)
equality? t u with C.canonical-equality? (at t) (at u)
... | yes p = yes (at-injective t u p)
... | no bad = no (λ p → bad (cong at p))

app-agrees : (f : TmAt (A SK.⇒ D)) (x : TmAt A)
  → at (app f x) ≡ C.apply-and-normalize (at f) (at x)
app-agrees f x = at-embed (C.apply-and-normalize (at f) (at x))

app-type : (f : TmAt (A SK.⇒ D)) (x : TmAt A)
  → tyOf (fst (app f x)) ≡ D
app-type f x = refl

code : (t : Term) → SK.Tm (tyOf t)
code t = fst (snd t)

normal-form : (t : Term) → SK.Nf (tyOf t)
normal-form t = C.normal-form (code t)

normal-form-erases : (t : Term) → SK.erase (normal-form t) ≡ code t
normal-form-erases t = C.normal-form-erases (code t) ∙ snd (snd t)

native-typed : (t : Term)
  → N.Typ N.empty (B.expand (code t)) (B.decode (tyOf t))
native-typed t = B.expand-typed N.empty (code t)

-- No quotient path constructors occur in this carrier or its operations.
-- The fibre retraction and application law are proved, not assumed strict.
