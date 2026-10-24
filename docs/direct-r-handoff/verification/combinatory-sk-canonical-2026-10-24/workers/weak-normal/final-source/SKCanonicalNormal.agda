{-# OPTIONS --cubical --safe --guardedness #-}
module SKCanonicalNormal where

-- Compiling a closed native-normal source produces an actual weak SK
-- normal form, not merely an arbitrary representative of its beta class.
open import PTSPrelude
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty using (⊥; rec)
import BoundedReduction as R
import BinderFreeCore as SK
import SKSource as L
import SKBracket as C
open SK using (Ty; ι; _⇒_)
open L using (Con; ε; _▻_; Var; vz; vs; Source)

private
  variable
    Γ : Con
    A D E : Ty

  no-fin : ∀ {X : Set} → R.Fin zero → X
  no-fin ()

  -- This generic eliminator compares two typed variable cases without
  -- matching a variable at a fixed successor-context index.
  CaseVar₂ : {P Q : Ty → Set} → ((A : Ty) → P A → Q A → Set)
    → (Γ : Con) → (A : Ty) → Var Γ A → Set
  CaseVar₂ Rel ε A x = Unit
  CaseVar₂ {P} {Q} Rel (Γ ▻ D) A x =
    (z : P D) (s : ∀ {E} → Var Γ E → P E)
    (z′ : Q D) (s′ : ∀ {E} → Var Γ E → Q E)
    → Rel D z z′ → (∀ {E} (y : Var Γ E) → Rel E (s y) (s′ y))
    → Rel A (L.caseVar x z s) (L.caseVar x z′ s′)

  caseVar₂ : {P Q : Ty → Set} (Rel : (A : Ty) → P A → Q A → Set)
    → (x : Var Γ A) → CaseVar₂ Rel Γ A x
  caseVar₂ Rel vz z s z′ s′ p q = p
  caseVar₂ Rel (vs x) z s z′ s′ p q = q x

-- Abstracting the sole free variable always leaves an unsaturated head.
-- Recursive calls construct normal saved argument spines structurally.
abstractClosedNf : C.Code (ε ▻ A) D → SK.Nf (A ⇒ D)
abstractClosedNf C.s = SK.k1 SK.s0
abstractClosedNf C.k = SK.k1 SK.k0
abstractClosedNf (C.label n) = SK.k1 (SK.lit n)
abstractClosedNf {A = A} (C.cv x) = L.caseVar {P = λ D → SK.Nf (A ⇒ D)} x SK.identityNF
  (λ y → no-fin (L.eraseVar y))
abstractClosedNf (f C.· x) = SK.s2 (abstractClosedNf f) (abstractClosedNf x)

abstractClosedNf-erases : (p : C.Code (ε ▻ A) D)
  → SK.erase (abstractClosedNf p) ≡ C.close (C.bracket p)
abstractClosedNf-erases C.s = refl
abstractClosedNf-erases C.k = refl
abstractClosedNf-erases (C.label n) = refl
abstractClosedNf-erases {A = A} (C.cv x) =
  caseVar₂ {P = λ D → SK.Nf (A ⇒ D)} {Q = λ D → C.Code ε (A ⇒ D)}
    (λ _ n p → SK.erase n ≡ C.close p) x
    SK.identityNF (λ y → no-fin (L.eraseVar y))
    C.identity (λ y → C.k C.· C.cv y) refl (λ y → no-fin (L.eraseVar y))
abstractClosedNf-erases (f C.· x) = cong₂ (λ u v → SK.S SK.· u SK.· v)
  (abstractClosedNf-erases f) (abstractClosedNf-erases x)

private
  IsGround : Ty → Set
  IsGround ι = Unit
  IsGround (A ⇒ D) = ⊥

  -- A closed normal non-lambda is a ground label: no free neutral head
  -- exists. The application case contradicts this statement for its head.
  closed-neutral-ground : (t : Source ε A)
    → R.Normal (L.erase t) → R.NotLambda (L.erase t) → IsGround A
  closed-neutral-ground (L.var x) h nl = no-fin (L.eraseVar x)
  closed-neutral-ground (L.ground n) h nl = tt
  closed-neutral-ground (L.lam b) h ()
  closed-neutral-ground (L.app f x) h nl = rec
    (closed-neutral-ground f (fst h) (snd (snd h)))

compiled-normal : (t : Source ε A) → R.Normal (L.erase t)
  → Σ (SK.Nf A) (λ n → SK.erase n ≡ C.compile t)
compiled-normal (L.var x) h = no-fin (L.eraseVar x)
compiled-normal (L.ground n) h = SK.lit n , refl
compiled-normal (L.lam b) h = abstractClosedNf (C.compile-open b) ,
  abstractClosedNf-erases (C.compile-open b)
compiled-normal (L.app f x) h = rec
  (closed-neutral-ground f (fst h) (snd (snd h)))

compiled-irreducible : (t : Source ε A) (h : R.Normal (L.erase t))
  → ∀ {u} → C.compile t SK.↝ u → ⊥
compiled-irreducible t h p = SK.irreducible (fst (compiled-normal t h))
  (subst (λ u → u SK.↝ _) (sym (snd (compiled-normal t h))) p)

identity-source : Source ε (ι ⇒ ι)
identity-source = L.lam (L.var vz)

regression-compiled-identity : fst (compiled-normal identity-source (tt , tt))
  ≡ SK.identityNF
regression-compiled-identity = refl
