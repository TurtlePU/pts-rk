{-# OPTIONS --cubical --safe --guardedness #-}
module SKSourceEquality where

-- Erasure retains every source annotation. Hidden application domains are
-- recovered by type synthesis; equality never identifies eta expansions.
open import PTSPrelude
open import SKSource
open import BinderFreeCore using (Ty; ι; _⇒_)
open import BinderFreeBidirectional using (ty-isSet)
open import Cubical.Data.Empty using (rec)
open import Cubical.Data.FinData.Base using (¬Fin0)
open import Cubical.Data.Sigma.Base using (_×_)
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)
open import Cubical.Foundations.Prelude using (isProp; substRefl; fromPathP)
open import Cubical.Foundations.HLevels using (isProp×)
import BoundedReduction as R
import BinderFreeBoundary as B
import NativeTyping as N

private
  variable
    Γ : Con
    A D : Ty
    n : Nat

-- A position determines its type and intrinsic variable, with no search.
variableAt : (Γ : Con) → R.Fin (length Γ) → Σ Ty (Var Γ)
variableAt ε i = rec (¬Fin0 i)
variableAt (Γ ▻ A) i = R.caseFin i (A , vz)
  (λ j → fst (variableAt Γ j) , vs (snd (variableAt Γ j)))

variable-retract : (v : Var Γ A) → variableAt Γ (eraseVar v) ≡ (A , v)
variable-retract vz = refl
variable-retract (vs v) = cong (λ p → fst p , vs (snd p)) (variable-retract v)

data View (n : Nat) : Set where
  slot : R.Fin n → View n
  literal : Nat → View n
  lambda : Ty → View (suc n) → View n
  apply : View n → View n → View n

forget : Source Γ A → View (length Γ)
forget (var v) = slot (eraseVar v)
forget (ground i) = literal i
forget (lam {A = A} b) = lambda A (forget b)
forget (app f x) = apply (forget f) (forget x)

private
  codomain : Ty → Ty
  codomain ι = ι
  codomain (A ⇒ D) = D

  domain : Ty → Ty
  domain ι = ι
  domain (A ⇒ D) = A

apparent : (Γ : Con) → View (length Γ) → Ty
apparent Γ (slot i) = fst (variableAt Γ i)
apparent Γ (literal i) = ι
apparent Γ (lambda A b) = A ⇒ apparent (Γ ▻ A) b
apparent Γ (apply f x) = codomain (apparent Γ f)

-- Independent recursive typing witnesses for the annotation-preserving
-- view. This is proof infrastructure, not a replacement PTS judgment.
Check : (Γ : Con) → View (length Γ) → Ty → Set
Check Γ (slot i) A = fst (variableAt Γ i) ≡ A
Check Γ (literal i) A = ι ≡ A
Check Γ (lambda D b) A = Σ Ty (λ E → (D ⇒ E ≡ A) × Check (Γ ▻ D) b E)
Check Γ (apply f x) A = Σ Ty (λ D → Check Γ f (D ⇒ A) × Check Γ x D)

check-type : (Γ : Con) (t : View (length Γ)) (A : Ty)
  → Check Γ t A → apparent Γ t ≡ A
check-type Γ (slot i) A p = p
check-type Γ (literal i) A p = p
check-type Γ (lambda D b) A (E , p , q) =
  cong (D ⇒_) (check-type (Γ ▻ D) b E q) ∙ p
check-type Γ (apply f x) A (D , p , q) =
  cong codomain (check-type Γ f (D ⇒ A) p)

check-prop : (Γ : Con) (t : View (length Γ)) (A : Ty) → isProp (Check Γ t A)
check-prop Γ (slot i) A = ty-isSet _ _
check-prop Γ (literal i) A = ty-isSet _ _
check-prop Γ (lambda D b) A (E , p , q) (F , r , s) =
  Σ≡Prop (λ X → isProp× (ty-isSet _ _) (check-prop (Γ ▻ D) b X))
    (sym (check-type (Γ ▻ D) b E q) ∙ check-type (Γ ▻ D) b F s)
check-prop Γ (apply f x) A (D , p , q) (E , r , s) =
  Σ≡Prop (λ X → isProp× (check-prop Γ f (X ⇒ A)) (check-prop Γ x X))
    (cong domain (sym (check-type Γ f (D ⇒ A) p) ∙ check-type Γ f (E ⇒ A) r))

elaborate : (Γ : Con) (t : View (length Γ)) (A : Ty) → Check Γ t A → Source Γ A
elaborate Γ (slot i) A p = subst (Source Γ) p (var (snd (variableAt Γ i)))
elaborate Γ (literal i) A p = subst (Source Γ) p (ground i)
elaborate Γ (lambda D b) A (E , p , q) =
  subst (Source Γ) p (lam (elaborate (Γ ▻ D) b E q))
elaborate Γ (apply f x) A (D , p , q) =
  app (elaborate Γ f (D ⇒ A) p) (elaborate Γ x D q)

forget-check : (t : Source Γ A) → Check Γ (forget t) A
forget-check (var v) = cong fst (variable-retract v)
forget-check (ground i) = refl
forget-check (lam {D = D} b) = D , refl , forget-check b
forget-check (app {A = A} f x) = A , forget-check f , forget-check x

private
  variable-source-retract : (v : Var Γ A)
    → subst (Source Γ) (cong fst (variable-retract v))
        (var (snd (variableAt Γ (eraseVar v)))) ≡ var v
  variable-source-retract v = fromPathP (λ i → var (snd (variable-retract v i)))

elaborate-forget : (t : Source Γ A) → elaborate Γ (forget t) A (forget-check t) ≡ t
elaborate-forget (var v) = variable-source-retract v
elaborate-forget (ground i) = substRefl {B = Source _}
elaborate-forget (lam b) = substRefl {B = Source _} ∙ cong lam (elaborate-forget b)
elaborate-forget (app f x) = cong₂ app (elaborate-forget f) (elaborate-forget x)

forget-injective : (t u : Source Γ A) → forget t ≡ forget u → t ≡ u
forget-injective {Γ} {A} t u p = sym (elaborate-forget t) ∙
  cong (λ (z : Σ (View (length Γ)) (λ v → Check Γ v A)) → elaborate Γ (fst z) A (snd z))
    (Σ≡Prop (λ v → check-prop Γ v A) p) ∙ elaborate-forget u

-- Total observations suffice to recover the view of an erased Source.
-- They need not validate arbitrary native input and do not normalize it.
read-type : N.Term n → Ty
read-type (R.pi A D) = read-type A ⇒ read-type D
read-type _ = ι

read-decode : (A : Ty) → read-type (B.decode {n} A) ≡ A
read-decode ι = refl
read-decode (A ⇒ D) = cong₂ _⇒_ (read-decode A) (read-decode D)

observe : N.Term n → View n
observe (R.U i) = literal i
observe (R.var i) = slot i
observe (R.pi A D) = literal 0
observe (R.lam A b) = lambda (read-type A) (observe b)
observe (R.app f x) = apply (observe f) (observe x)

observe-erasure : (t : Source Γ A) → observe (erase t) ≡ forget t
observe-erasure (var v) = refl
observe-erasure (ground i) = refl
observe-erasure (lam {A = A} b) = cong₂ lambda (read-decode A) (observe-erasure b)
observe-erasure (app f x) = cong₂ apply (observe-erasure f) (observe-erasure x)

erase-injective : (t u : Source Γ A) → erase t ≡ erase u → t ≡ u
erase-injective t u p = forget-injective t u
  (sym (observe-erasure t) ∙ cong observe p ∙ observe-erasure u)
