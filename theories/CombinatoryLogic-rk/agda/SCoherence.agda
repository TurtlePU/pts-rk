{-# OPTIONS --cubical --safe --guardedness #-}
module SCoherence where
open import PTSPrelude
open import Combinatory
open import Cubical.Foundations.Prelude using (isProp→PathP)

private variable
  Γ Δ Θ : Con
  a b r : Nat

pair-nat-guard : {A : Ty Δ r} (σ : Sub Γ Δ) (t : Tm Γ)
  (p : tyOf t ≡ (r , subTy A σ)) (τ : Sub Θ Γ)
  → tyOf (subTm t τ) ≡ (r , subTy A (comp σ τ))
pair-nat-guard {r = r} {A = A} σ t p τ =
  cong (λ X → subRanked X τ) p ∙ (λ i → r , ty-comp A σ τ i)

fst-natural : {A : Ty Δ r} (σ : Sub Γ (ext Δ A)) (τ : Sub Θ Γ)
  → fstS (comp σ τ) ≡ comp (fstS σ) τ
fst-natural {A = A} σ τ =
  cong (λ s → fstS (comp s τ)) (sym (eta-pair σ)) ∙
  cong fstS (pair-comp-derived (fstS σ) (sndS σ) (sndType σ) τ) ∙
  beta-fst (comp (fstS σ) τ) (subTm (sndS σ) τ)
    (pair-nat-guard (fstS σ) (sndS σ) (sndType σ) τ)

snd-natural : {A : Ty Δ r} (σ : Sub Γ (ext Δ A)) (τ : Sub Θ Γ)
  → sndS (comp σ τ) ≡ subTm (sndS σ) τ
snd-natural {A = A} σ τ =
  cong (λ s → sndS (comp s τ)) (sym (eta-pair σ)) ∙
  cong sndS (pair-comp-derived (fstS σ) (sndS σ) (sndType σ) τ) ∙
  beta-snd-derived (comp (fstS σ) τ) (subTm (sndS σ) τ)
    (pair-nat-guard (fstS σ) (sndS σ) (sndType σ) τ)

pair-cong : {A : Ty Δ r} {σ τ : Sub Γ Δ} {t u : Tm Γ}
  (p : σ ≡ τ) (q : t ≡ u)
  (pt : tyOf t ≡ (r , subTy A σ)) (pu : tyOf u ≡ (r , subTy A τ))
  → pair σ t pt ≡ pair τ u pu
pair-cong {r = r} {A = A} p q pt pu i = pair (p i) (q i)
  (isProp→PathP (λ j → rankedSet (tyOf (q j)) (r , subTy A (p j))) pt pu i)

sub-ext : {A : Ty Δ r} (σ τ : Sub Γ (ext Δ A))
  → fstS σ ≡ fstS τ → sndS σ ≡ sndS τ → σ ≡ τ
sub-ext σ τ p q = sym (eta-pair σ) ∙
  pair-cong p q (sndType σ) (sndType τ) ∙ eta-pair τ

q-sub : {A : Ty Δ r} (σ : Sub Γ (ext Δ A))
  → subTm (q A) σ ≡ sndS σ
q-sub σ = sym (snd-natural id σ) ∙ cong sndS (id-left σ)

wk-pair : {A : Ty Δ r} (σ : Sub Γ Δ) (t : Tm Γ)
  (p : tyOf t ≡ (r , subTy A σ)) → comp (wk A) (pair σ t p) ≡ σ
wk-pair σ t p = sym (fst-natural id (pair σ t p)) ∙
  cong fstS (id-left (pair σ t p)) ∙ beta-fst σ t p

-- The canonical substitution returning the newly bound variable.
return-q : (A : Ty Γ r) → Sub (ext Γ A) (ext (ext Γ A) (subTy A (wk A)))
return-q {r = r} A = single (subTy A (wk A)) (q A)
  (λ i → r , sym (ty-id (subTy A (wk A))) i)

open-cancel : (A : Ty Γ r) → comp (lift (wk A) A) (return-q A) ≡ id
open-cancel {r = r} A = sub-ext _ id left right
  where
  w = wk A
  Q = subTy A w
  w₂ = wk Q
  s = return-q A
  L = lift w A
  qs = λ i → r , sym (ty-id Q) i
  left : fstS (comp L s) ≡ fstS id
  left = fst-natural L s ∙
    cong (λ τ → comp τ s) (beta-fst (comp w w₂) (q Q) (liftType w A)) ∙
    assoc w w₂ s ∙ cong (comp w) (wk-pair id (q A) qs) ∙ id-right w
  right : sndS (comp L s) ≡ sndS id
  right = snd-natural L s ∙
    cong (λ t → subTm t s) (beta-snd-derived (comp w w₂) (q Q) (liftType w A)) ∙
    q-sub s ∙ beta-snd-derived id (q A) qs

mapAt : {A : Ty Δ r} → (σ : Sub Γ Δ) → TmAt Δ A → TmAt Γ (subTy A σ)
mapAt σ (t , p) = subTm t σ , cong (λ X → subRanked X σ) p

castAt : {A B : Ty Γ r} → A ≡ B → TmAt Γ A → TmAt Γ B
castAt {r = r} p (t , pt) = t , pt ∙ (λ i → r , p i)

-- Apply a function to the fresh variable, cancelling the explicit lifts.
openFun : {A : Ty Γ a} {B : Ty (ext Γ A) b}
        → TmAt Γ (Pi A B) → TmAt (ext Γ A) B
openFun {a = a} {b = b} {A = A} {B = B} (f , pf) = body , bodyType
  where
  w = wk A
  Q = subTy A w
  B′ = subTy B (lift w A)
  f′ = subTm f w
  pf′ : tyOf f′ ≡ (max (suc a) b , Pi Q B′)
  pf′ = cong (λ X → subRanked X w) pf ∙
    (λ i → max (suc a) b , Pi-sub A B w i)
  px = λ i → a , sym (ty-id Q) i
  body = app-guarded Q B′ f′ (q A) pf′ px
  bodyType : tyOf body ≡ (b , B)
  bodyType = (λ i → b , ty-comp B (lift w A) (return-q A) i) ∙
    (λ i → b , subTy B (open-cancel A i)) ∙ (λ i → b , ty-id B i)

variableAt : (A : Ty Γ r) → TmAt (ext Γ A) (subTy A (wk A))
variableAt A = q A , refl

weakenPi : (σ : Sub Γ Δ) (A : Ty Δ a) (B : Ty (ext Δ A) b)
         → TmAt Δ (Pi A B)
         → TmAt Γ (Pi (subTy A σ) (subTy B (lift σ A)))
weakenPi σ A B f = castAt (Pi-sub A B σ) (mapAt σ f)

weakenPiU : (σ : Sub Γ Δ) (A : Ty Δ a) (b : Nat)
          → TmAt Δ (Pi A (U b)) → TmAt Γ (Pi (subTy A σ) (U b))
weakenPiU σ A b f = castAt
  (cong (Pi (subTy A σ)) (U-sub b (lift σ A))) (weakenPi σ A (U b) f)

weakenPiPiU : (σ : Sub Γ Δ) (A : Ty Δ a) (B : Ty (ext Δ A) b) (c : Nat)
            → TmAt Δ (Pi A (Pi B (U c)))
            → TmAt Γ (Pi (subTy A σ) (Pi (subTy B (lift σ A)) (U c)))
weakenPiPiU σ A B c f = castAt
  (cong (Pi (subTy A σ))
    (Pi-sub B (U c) (lift σ A) ∙
      cong (Pi (subTy B (lift σ A))) (U-sub c (lift (lift σ A) B))))
  (weakenPi σ A (Pi B (U c)) f)
