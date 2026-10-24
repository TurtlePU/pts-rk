{-# OPTIONS --cubical --safe --guardedness #-}
module BinderFreeBidirectional where

-- A decidable elaboration interface for the simply typed binder-free core.
-- This does not replace the six native PTS rules or decide dependent typing.
-- Atom parameters are explicit type annotations; neither syntax has binders.
open import PTSPrelude
open import Cubical.Data.Empty.Base using (⊥)
open import Cubical.Data.Unit.Base using (Unit; tt)
open import Cubical.Data.Maybe.Base using (Maybe; just; nothing)
open import Cubical.Data.Sigma.Base using (_×_)
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)
open import Cubical.Foundations.Prelude using (isProp; substRefl)
open import Cubical.Foundations.HLevels using (isPropRetract; isProp×)
open import Cubical.Relation.Nullary.Base using (Dec; yes; no)
open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)
import BinderFreeCore as Core
open Core using (Ty; ι; _⇒_; Tm; Result)

infixl 30 _$_

-- BEGIN BINDER FREE CHECKER SYNTAX
data Raw : Set where
  s : Ty → Ty → Ty → Raw
  k : Ty → Ty → Raw
  ground : Nat → Raw
  _$_ : Raw → Raw → Raw

-- Declarative typing is independent of the decision procedure below.
data Typing : Raw → Ty → Set where
  typed-s : ∀ {A B C} → Typing (s A B C)
    ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
  typed-k : ∀ {A B} → Typing (k A B) (A ⇒ B ⇒ A)
  typed-ground : ∀ {n} → Typing (ground n) ι
  typed-app : ∀ {f x A B} → Typing f (A ⇒ B) → Typing x A
    → Typing (f $ x) B
-- END BINDER FREE CHECKER SYNTAX

private
  domain codomain : Ty → Ty
  domain ι = ι
  domain (A ⇒ B) = A
  codomain ι = ι
  codomain (A ⇒ B) = B

  Base : Ty → Set
  Base ι = Unit
  Base (A ⇒ B) = ⊥

  base-not-arrow : ∀ {A B} → ι ≡ (A ⇒ B) → ⊥
  base-not-arrow p = subst Base p tt

-- This total projection need not check its input. Its agreement lemma only
-- applies to independently derived judgments, and proves type uniqueness.
apparent : Raw → Ty
apparent (s A B C) = (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C
apparent (k A B) = A ⇒ B ⇒ A
apparent (ground n) = ι
apparent (f $ x) = codomain (apparent f)

typing-type : ∀ {t A} → Typing t A → apparent t ≡ A
typing-type typed-s = refl
typing-type typed-k = refl
typing-type typed-ground = refl
typing-type (typed-app pf px) = cong codomain (typing-type pf)

type-unique : ∀ {t A B} → Typing t A → Typing t B → A ≡ B
type-unique p q = sym (typing-type p) ∙ typing-type q

-- Source-recursive inversion avoids unsupported Cubical indexed matching.
Derivation : Raw → Ty → Set
Derivation (f $ x) A = Σ Ty (λ D → Typing f (D ⇒ A) × Typing x D)
Derivation t A = apparent t ≡ A

unfold : ∀ {t A} → Typing t A → Derivation t A
unfold typed-s = refl
unfold typed-k = refl
unfold typed-ground = refl
unfold (typed-app pf px) = _ , pf , px

fold : (t : Raw) (A : Ty) → Derivation t A → Typing t A
fold (s A B C) D p = subst (Typing (s A B C)) p typed-s
fold (k A B) D p = subst (Typing (k A B)) p typed-k
fold (ground n) D p = subst (Typing (ground n)) p typed-ground
fold (f $ x) A (D , pf , px) = typed-app pf px

fold-unfold : ∀ {t A} (p : Typing t A) → fold t A (unfold p) ≡ p
fold-unfold {t} typed-s = substRefl {B = Typing t} typed-s
fold-unfold {t} typed-k = substRefl {B = Typing t} typed-k
fold-unfold {t} typed-ground = substRefl {B = Typing t} typed-ground
fold-unfold (typed-app pf px) = refl

-- Positive elaboration must compute on constructors, not transport an
-- indexed derivation along a Cubical path.  Match carries precisely that
-- computational identity witness; paths are only used in rejection proofs.
data Match (A : Ty) : Ty → Set where
  same : Match A A

private
  match-path : ∀ {A B} → Match A B → A ≡ B
  match-path same = refl

  match-arrow : ∀ {A B C D} → Match A C → Match B D
    → Match (A ⇒ B) (C ⇒ D)
  match-arrow same same = same

type-match : (A B : Ty) → Dec (Match A B)
type-match ι ι = yes same
type-match ι (B ⇒ C) = no (λ p → base-not-arrow (match-path p))
type-match (A ⇒ B) ι = no (λ p → base-not-arrow (sym (match-path p)))
type-match (A ⇒ B) (C ⇒ D) with type-match A C
... | no neq = no (λ p → neq (subst (Match A) (cong domain (match-path p)) same))
... | yes p with type-match B D
...   | no neq = no (λ q → neq (subst (Match B) (cong codomain (match-path q)) same))
...   | yes q = yes (match-arrow p q)

type-equality : (A B : Ty) → Dec (A ≡ B)
type-equality A B with type-match A B
... | yes p = yes (match-path p)
... | no bad = no (λ p → bad (subst (Match A) p same))

ty-isSet : isSet Ty
ty-isSet = Discrete→isSet type-equality

mutual
  typing-proposition : (t : Raw) (A : Ty) → isProp (Typing t A)
  typing-proposition t A = isPropRetract unfold (fold t A) fold-unfold
    (derivation-proposition t A)

  derivation-proposition : (t : Raw) (A : Ty) → isProp (Derivation t A)
  derivation-proposition (s A B C) D = ty-isSet _ _
  derivation-proposition (k A B) D = ty-isSet _ _
  derivation-proposition (ground n) D = ty-isSet _ _
  derivation-proposition (f $ x) A (D , pf , px) (E , qf , qx) =
    Σ≡Prop (λ X → isProp× (typing-proposition f (X ⇒ A))
      (typing-proposition x X)) (cong domain (type-unique pf qf))

typing-isProp : ∀ {t A} → isProp (Typing t A)
typing-isProp {t} {A} = typing-proposition t A

-- In a combinator-only language every head synthesizes.  Checking therefore
-- compares the synthesized type with the expected one; an application checks
-- its argument at the domain synthesized for its function.  No unification,
-- guessed typing derivation, conversion oracle or normalization fuel is used.
-- BEGIN BINDER FREE CHECKER
mutual
  synthesize : (t : Raw) → Dec (Σ Ty (Typing t))
  synthesize (s A B C) = yes (_ , typed-s)
  synthesize (k A B) = yes (_ , typed-k)
  synthesize (ground n) = yes (_ , typed-ground)
  synthesize (f $ x) with synthesize f
  ... | no bad = no (λ q → bad (_ , fst (snd (unfold (snd q)))))
  ... | yes (ι , pf) = no (λ q →
    base-not-arrow (type-unique pf (fst (snd (unfold (snd q))))))
  ... | yes (A ⇒ B , pf) with check x A
  ...   | yes px = yes (B , typed-app pf px)
  ...   | no bad = no (λ q →
    let view = unfold (snd q) in
    bad (subst (Typing x)
      (sym (cong domain (type-unique pf (fst (snd view))))) (snd (snd view))))

  check : (t : Raw) (A : Ty) → Dec (Typing t A)
  check t A with synthesize t
  ... | no bad = no (λ p → bad (A , p))
  ... | yes (B , p) with type-match B A
  ...   | yes same = yes p
  ...   | no neq = no (λ q → neq (subst (Match B) (type-unique p q) same))
-- END BINDER FREE CHECKER

-- A successful answer is a declarative derivation (soundness); a negative
-- answer refutes every such derivation (completeness), not merely one search.
-- These facts are the positive and negative branches of Dec in the API.
elaborate : ∀ {t A} → Typing t A → Tm A
elaborate typed-s = Core.S
elaborate typed-k = Core.K
elaborate (typed-ground {n}) = Core.ground n
elaborate (typed-app pf px) = elaborate pf Core.· elaborate px

forget : ∀ {A} → Tm A → Raw
forget (Core.S {A} {B} {C}) = s A B C
forget (Core.K {A} {B}) = k A B
forget (Core.ground n) = ground n
forget (f Core.· x) = forget f $ forget x

elaboration-erases : ∀ {t A} (p : Typing t A) → forget (elaborate p) ≡ t
elaboration-erases typed-s = refl
elaboration-erases typed-k = refl
elaboration-erases typed-ground = refl
elaboration-erases (typed-app pf px) =
  cong₂ _$_ (elaboration-erases pf) (elaboration-erases px)

forget-typed : ∀ {A} (t : Tm A) → Typing (forget t) A
forget-typed Core.S = typed-s
forget-typed Core.K = typed-k
forget-typed (Core.ground n) = typed-ground
forget-typed (f Core.· x) = typed-app (forget-typed f) (forget-typed x)

elaboration-forget : ∀ {A} (t : Tm A) → elaborate (forget-typed t) ≡ t
elaboration-forget Core.S = refl
elaboration-forget Core.K = refl
elaboration-forget (Core.ground n) = refl
elaboration-forget (f Core.· x) =
  cong₂ Core._·_ (elaboration-forget f) (elaboration-forget x)

-- BEGIN BINDER FREE CHECK AND NORMALIZE
record CheckedNormal (t : Raw) (A : Ty) : Set where
  constructor checked-normal
  field
    typing : Typing t A
    result : Result (elaborate typing)

check-normalize : (t : Raw) (A : Ty) → Dec (CheckedNormal t A)
check-normalize t A with check t A
... | yes p = yes (checked-normal p (Core.normalize (elaborate p)))
... | no bad = no (λ r → bad (CheckedNormal.typing r))

synthesize-normalize : (t : Raw) → Dec (Σ Ty (CheckedNormal t))
synthesize-normalize t with synthesize t
... | yes (A , p) = yes (A , checked-normal p (Core.normalize (elaborate p)))
... | no bad = no (λ r → bad (fst r , CheckedNormal.typing (snd r)))
-- END BINDER FREE CHECK AND NORMALIZE

-- The executable projection drops certificates, never a failed normalization.
normal-output : (t : Raw) (A : Ty) → Maybe (Core.Nf A)
normal-output t A with check-normalize t A
... | yes r = just (Core.normal (CheckedNormal.result r))
... | no _ = nothing

-- Executable accepted/rejected examples, independent of native PTS typing.
identity : Ty → Raw
identity A = s A (A ⇒ A) A $ k A (A ⇒ A) $ k A A

identity-typed : (A : Ty) → Typing (identity A) (A ⇒ A)
identity-typed A = typed-app (typed-app typed-s typed-k) typed-k

identity-application : Typing (identity ι $ ground zero) ι
identity-application = typed-app (identity-typed ι) typed-ground

ground-not-function : ∀ {A} → Typing (ground zero $ ground zero) A → ⊥
ground-not-function p = base-not-arrow (typing-type (fst (snd (unfold p))))

regression-check-identity : normal-output (identity ι $ ground 7) ι ≡ just (Core.lit 7)
regression-check-identity = refl

regression-check-S :
  normal-output (s ι ι ι $ k ι ι $ identity ι $ ground 7) ι ≡ just (Core.lit 7)
regression-check-S = refl

regression-check-K :
  normal-output (k ι ι $ ground 7 $ ground 9) ι ≡ just (Core.lit 7)
regression-check-K = refl

regression-reject-application :
  normal-output (ground zero $ ground zero) ι ≡ nothing
regression-reject-application = refl

regression-reject-type : normal-output (identity ι) ι ≡ nothing
regression-reject-type = refl
