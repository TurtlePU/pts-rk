{-# OPTIONS --cubical --safe --guardedness #-}
module BinderFreeBoundary where

-- Literal expansion of the SK surface into original annotated PTS syntax.
-- The native typing theorem does not identify the two conversion relations.
open import PTSPrelude
open import BoundedReduction
open import NativeTyping
open import NativeConfluence using (steps-beta; normal-beta-unique)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Nat using (_+_; predℕ; snotz)
import BinderFreeCore as SK
open SK using (Ty; ι; _⇒_)

decode : ∀ {n} → Ty → Term n
decode ι = U 0
decode (A ⇒ D) = pi (decode A) (decode D)

order : Ty → Nat
order ι = 0
order (A ⇒ D) = max (suc (order A)) (order D)

decode-rename : ∀ {m n} (ρ : Fin m → Fin n) (A : Ty)
  → rename ρ (decode A) ≡ decode A
decode-rename ρ ι = refl
decode-rename ρ (A ⇒ D) = cong₂ pi
  (decode-rename ρ A) (decode-rename (liftRenaming ρ) D)

decode-replace : ∀ {m n} (σ : Fin m → Term n) (A : Ty)
  → replace σ (decode A) ≡ decode A
decode-replace σ ι = refl
decode-replace σ (A ⇒ D) = cong₂ pi
  (decode-replace σ A) (decode-replace (liftSubstitution σ) D)

decode-sorted : ∀ {n} (Γ : Context n) (A : Ty)
  → Typ Γ (decode A) (U (order A))
decode-sorted Γ ι = universe 0
decode-sorted Γ (A ⇒ D) = product (decode-sorted Γ A)
  (decode-sorted (extend Γ (decode A)) D)

expand : ∀ {n A} → SK.Tm A → Term n
expand (SK.S {A} {D} {E}) =
  lam (decode (A ⇒ D ⇒ E)) (lam (decode (A ⇒ D)) (lam (decode A)
    (app (app (var (fsuc (fsuc fzero))) (var fzero))
      (app (var (fsuc fzero)) (var fzero)))))
expand (SK.K {A} {D}) = lam (decode A) (lam (decode D) (var (fsuc fzero)))
expand (SK.ground n) = U n
expand (f SK.· x) = app (expand f) (expand x)

private
  variable
    n : Nat
    Γ : Context n
    A D E : Ty

  variable₀ : Typ (extend Γ (decode A)) (var fzero) (decode A)
  variable₀ {A = A} = subst (Typ _ (var fzero))
    (decode-rename fsuc A) (lookup-var fzero)

  variable₁ : Typ (extend (extend Γ (decode A)) (decode D))
    (var (fsuc fzero)) (decode A)
  variable₁ {A = A} = subst (Typ _ (var (fsuc fzero)))
    (cong shift (decode-rename fsuc A) ∙ decode-rename fsuc A)
    (lookup-var (fsuc fzero))

  variable₂ : Typ (extend (extend (extend Γ (decode A)) (decode D)) (decode E))
    (var (fsuc (fsuc fzero))) (decode A)
  variable₂ {A = A} = subst (Typ _ (var (fsuc (fsuc fzero))))
    (cong shift (cong shift (decode-rename fsuc A) ∙ decode-rename fsuc A)
      ∙ decode-rename fsuc A) (lookup-var (fsuc (fsuc fzero)))

  apply-native : ∀ {f x} → Typ Γ f (decode (A ⇒ D))
    → Typ Γ x (decode A) → Typ Γ (app f x) (decode D)
  apply-native {D = D} {x = x} pf px = subst (Typ _ (app _ x))
    (decode-replace (single x) D) (application pf px)

-- Every intrinsic SK typing is interpreted in the ORIGINAL six-rule system.
expand-typed : ∀ {n A} (Γ : Context n) (t : SK.Tm A)
  → Typ Γ (expand t) (decode A)
expand-typed Γ (SK.S {A} {D} {E}) =
  abstraction (decode-sorted Γ (A ⇒ D ⇒ E))
    (abstraction (decode-sorted _ (A ⇒ D))
      (abstraction (decode-sorted _ A)
        (apply-native (apply-native variable₂ variable₀)
          (apply-native variable₁ variable₀))))
expand-typed Γ (SK.K {A} {D}) = abstraction (decode-sorted Γ A)
  (abstraction (decode-sorted _ D) variable₁)
expand-typed Γ (SK.ground n) = universe n
expand-typed Γ (f SK.· x) = apply-native (expand-typed Γ f) (expand-typed Γ x)

-- Two distinct unsaturated SK spines nevertheless denote the same native
-- beta normal form. Identity is a macro, never an additional surface atom.
identity-code alternate-code : SK.Tm (ι ⇒ ι)
identity-code = SK.identity
alternate-code = SK.S SK.· SK.K {ι} {ι} SK.· SK.identity

identity-nf alternate-nf : SK.Nf (ι ⇒ ι)
identity-nf = SK.identityNF
alternate-nf = SK.s2 SK.k0 SK.identityNF

native-identity : ∀ {n} → Term n
native-identity = lam (U 0) (var fzero)

-- BEGIN BINDERFREE BOUNDARY
identity-computes : rounds 3 (expand {0} identity-code) ≡ native-identity
identity-computes = refl

alternate-computes : rounds 3 (expand {0} alternate-code) ≡ native-identity
alternate-computes = refl

same-native-beta : Beta (expand {0} alternate-code) (expand identity-code)
same-native-beta = beta-trans
  (steps-beta (rounds-sound 3 (expand alternate-code)))
  (beta-sym (steps-beta (rounds-sound 3 (expand identity-code))))

identity-irreducible : ∀ {u} → identity-code SK.↝ u → ⊥
identity-irreducible = SK.irreducible identity-nf

alternate-irreducible : ∀ {u} → alternate-code SK.↝ u → ⊥
alternate-irreducible = SK.irreducible alternate-nf

private
  atoms : ∀ {A} → SK.Tm A → Nat
  atoms SK.S = 1
  atoms SK.K = 1
  atoms (SK.ground n) = 1
  atoms (f SK.· x) = atoms f + atoms x

  five-not-three : 5 ≡ 3 → ⊥
  five-not-three p = snotz (cong (λ n → predℕ (predℕ (predℕ n))) p)

distinct-codes : alternate-code ≡ identity-code → ⊥
distinct-codes p = five-not-three (cong atoms p)
-- END BINDERFREE BOUNDARY

-- Eta is not a valid repair: these weak-normal codes have different native
-- beta normal forms, λf.λx.f x and λf.f, respectively.
eta-code arrow-identity-code : SK.Tm ((ι ⇒ ι) ⇒ ι ⇒ ι)
eta-code = SK.S SK.· (SK.K SK.· SK.identity)
arrow-identity-code = SK.identity

eta-nf : SK.Nf ((ι ⇒ ι) ⇒ ι ⇒ ι)
eta-nf = SK.s1 (SK.k1 SK.identityNF)

eta-irreducible : ∀ {u} → eta-code SK.↝ u → ⊥
eta-irreducible = SK.irreducible eta-nf

eta-expanded arrow-identity : Term 0
eta-expanded = lam (decode (ι ⇒ ι))
  (lam (U 0) (app (var (fsuc fzero)) (var fzero)))
arrow-identity = lam (decode (ι ⇒ ι)) (var fzero)

eta-computes : rounds 3 (expand {0} eta-code) ≡ eta-expanded
eta-computes = refl

arrow-identity-computes : rounds 3 (expand {0} arrow-identity-code) ≡ arrow-identity
arrow-identity-computes = refl

eta-expanded-normal : Normal eta-expanded
eta-expanded-normal = (tt , tt) , (tt , (tt , tt , tt))

arrow-identity-normal : Normal arrow-identity
arrow-identity-normal = (tt , tt) , tt

private
  IsLambda : ∀ {n} → Term n → Set
  IsLambda (lam _ _) = Unit
  IsLambda (U _) = ⊥
  IsLambda (var _) = ⊥
  IsLambda (pi _ _) = ⊥
  IsLambda (app _ _) = ⊥

  HasLambdaBody : ∀ {n} → Term n → Set
  HasLambdaBody (lam _ b) = IsLambda b
  HasLambdaBody (U _) = ⊥
  HasLambdaBody (var _) = ⊥
  HasLambdaBody (pi _ _) = ⊥
  HasLambdaBody (app _ _) = ⊥

eta-not-beta-identity : Beta (expand {0} eta-code) (expand arrow-identity-code) → ⊥
eta-not-beta-identity e = subst HasLambdaBody
  (normal-beta-unique eta-expanded-normal arrow-identity-normal
    (beta-trans (beta-sym (steps-beta (rounds-sound 3 (expand eta-code))))
      (beta-trans e (steps-beta (rounds-sound 3 (expand arrow-identity-code)))))) tt
