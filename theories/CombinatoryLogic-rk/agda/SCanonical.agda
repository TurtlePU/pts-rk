{-# OPTIONS --cubical --safe --guardedness #-}
module SCanonical where

open import PTSPrelude
open import Combinatory
import SCoherence as W
import Combinatory as G

module Canonical (a b c : Nat) where
  module T = G.Template a b c

  bVar : TmAt T.ΓAB (Pi T.A₁ (U b))
  bVar = W.castAt
    (Pi-sub T.A₀ (U b) (G.wk T.BCode) ∙
      cong (Pi T.A₁) (U-sub b (lift (G.wk T.BCode) T.A₀)))
    (W.variableAt T.BCode)

  pB : T.BGuard
  pB = snd (W.weakenPiU (G.wk T.A₁) T.A₁ b bVar)

  module O = T.One pB

  cVar : TmAt (ext T.ΓAB O.CCode) (Pi O.A₃ (Pi O.B₃ (U c)))
  cVar = W.castAt
    (Pi-sub T.A₁ (Pi O.BFamily (U c)) (G.wk O.CCode) ∙
      cong (Pi O.A₃)
        (Pi-sub O.BFamily (U c) (lift (G.wk O.CCode) T.A₁) ∙
          cong (Pi O.B₃) (U-sub c (lift (lift (G.wk O.CCode) T.A₁) O.BFamily))))
    (W.variableAt O.CCode)

  pC : O.CGuard
  pC = snd (W.weakenPiPiU (G.wk O.A₃) O.A₃ O.B₃ c cVar)

  module P = T.Two pB pC

  openB : subTy O.B₄ (W.return-q O.A₃) ≡ O.B₃
  openB = ty-comp O.B₃ (lift (G.wk O.A₃) O.A₃) (W.return-q O.A₃) ∙
    cong (subTy O.B₃) (W.open-cancel O.A₃) ∙ ty-id O.B₃

  pCx : P.CxGuard
  pCx = λ i → suc b ,
    (Pi-sub O.B₄ (U c) (W.return-q O.A₃) ∙
      cong (Pi (subTy O.B₄ (W.return-q O.A₃)))
        (U-sub c (lift (W.return-q O.A₃) O.B₄)) ∙
      cong (λ B → Pi B (U c)) openB) i

  module Q = T.Three pB pC pCx

  pCw : Q.CxWeakGuard
  pCw = snd (W.weakenPiU (G.wk O.B₃) O.B₃ c (P.Cx , pCx))

  module R = T.Four pB pC pCx pCw

  gVar : TmAt (ext (ext (ext T.ΓAB O.CCode) R.F) R.G) (Pi R.A₇ R.B₇)
  gVar = W.castAt (Pi-sub R.A₆ R.B₆ (G.wk R.G)) (W.variableAt R.G)

  pG : R.GGuard
  pG = snd (W.weakenPi (G.wk R.A₇) R.A₇ R.B₇ gVar)

  pD : R.DiagCGuard
  pD = snd (W.weakenPiPiU (G.wk R.A₇) R.A₇ R.B₇ c
    (W.weakenPiPiU (G.wk R.G) R.A₆ R.B₆ c
      (W.weakenPiPiU (G.wk R.F) O.A₃ O.B₃ c cVar)))

  module V = T.Five pB pC pCx pCw pG pD

  pDx : V.DiagCxGuard
  pDx = λ i → suc b ,
    (Pi-sub R.B₈ (U c) V.σx ∙
      cong (Pi V.BxDiag) (U-sub c (lift V.σx R.B₈))) i

  canonical : T.Guards
  canonical = pB , pC , pCx , pCw , pG , pD , pDx

-- The public family has only the three original numerical rank indices.
SType : (a b c : Nat) → Ty empty (sRank a b c)
SType a b c = Template.typeOfS a b c (Canonical.canonical a b c)

S : Nat → Nat → Nat → Tm empty
S a b c = S-guarded a b c (Canonical.canonical a b c)

S-type : (a b c : Nat) → tyOf (S a b c) ≡ (sRank a b c , SType a b c)
S-type a b c = refl
