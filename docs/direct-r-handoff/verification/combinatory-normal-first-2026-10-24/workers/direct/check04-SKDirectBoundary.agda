{-# OPTIONS --cubical --safe --guardedness #-}
module SKDirectBoundary where

-- Weak application of canonical INPUTS need not stay in the canonical
-- image at a function OUTPUT type. This is a checked concrete obstruction,
-- not an impossibility theorem for stronger binder-free evaluators.
open import PTSPrelude
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Nat using (_+_; predℕ; snotz)
open import NativeConfluence using (steps-beta)
open import NativeInversion using (beta-path)
import NativeTyping as T
import BoundedReduction as R
import BinderFreeCore as SK
import BinderFreeBoundary as B
import SKSource as L
import SKSourceNormal as SN
import SKBracket as C
import SKCanonical as Canonical
import SKDirectSoundness as Direct

private
  variable
    A : SK.Ty

-- A native-normal source compiles to a fixed point of the canonicalizer.
compiled-fixed : (s : L.Source L.ε A) → R.Normal (L.erase s)
  → Canonical.normalize (C.compile s) ≡ C.compile s
compiled-fixed s ns = cong C.compile
  (SN.coherent (C.expand-source (C.compile s)) s
    (T.beta-trans (beta-path (C.erase-expand (C.compile s)))
      (steps-beta (C.compile-steps s))))
  ∙ cong C.compile (SN.normal-identity s ns)

E : SK.Ty
E = SK.ι SK.⇒ SK.ι

-- F = λf:E.λx:ι.f; a = λy:ι.y; F a = λx:ι.λy:ι.y.
function-source : L.Source L.ε (E SK.⇒ SK.ι SK.⇒ E)
function-source = L.lam (L.lam (L.var (L.vs L.vz)))

argument-source : L.Source L.ε E
argument-source = L.lam (L.var L.vz)

result-source : L.Source L.ε (SK.ι SK.⇒ E)
result-source = L.lam (L.lam (L.var L.vz))

function : Canonical.Canonical (E SK.⇒ SK.ι SK.⇒ E)
function = C.compile function-source , compiled-fixed function-source ((tt , tt) , tt , tt)

argument : Canonical.Canonical E
argument = C.compile argument-source , compiled-fixed argument-source (tt , tt)

result : SK.Tm (SK.ι SK.⇒ E)
result = C.compile result-source

weak-result : SK.Tm (SK.ι SK.⇒ E)
weak-result = Direct.direct (fst function SK.· fst argument)

weak-result-computes : weak-result ≡ SK.K SK.· SK.identity
weak-result-computes = refl

application-beta : T.Beta (B.expand {zero} (fst function SK.· fst argument)) (B.expand result)
application-beta = T.beta-trans
  (steps-beta (R.steps-app (C.compile-steps function-source) (C.compile-steps argument-source)))
  (T.beta-trans (T.beta-step R.beta) (T.beta-sym (steps-beta (C.compile-steps result-source))))

canonical-result : Canonical.normalize (fst function SK.· fst argument) ≡ result
canonical-result = Canonical.coherent _ _ application-beta
  ∙ compiled-fixed result-source (tt , tt , tt)

atoms : SK.Tm A → Nat
atoms SK.S = 1
atoms SK.K = 1
atoms (SK.ground n) = 1
atoms (f SK.· x) = atoms f + atoms x

weak-result-size : atoms weak-result ≡ 4
weak-result-size = refl

canonical-result-size : atoms result ≡ 8
canonical-result-size = refl

private
  drop-four : Nat → Nat
  drop-four n = predℕ (predℕ (predℕ (predℕ n)))

different-results : result ≡ weak-result → ⊥
different-results p = snotz (cong drop-four (cong atoms p))

weak-result-not-canonical : Canonical.normalize weak-result ≡ weak-result → ⊥
weak-result-not-canonical h = different-results
  (sym canonical-result ∙ Direct.canonical-after-direct (fst function SK.· fst argument) ∙ h)
