{-# OPTIONS --cubical --safe --guardedness #-}
module NativeCertificates where

-- Independent, finite proof trees. Neither the certificate grammar nor its
-- recursively computed acceptance predicate contains a native typing proof.
-- Acceptance tests only local syntax equalities and accepted subtrees.
open import PTSPrelude
open import FiniteSyntax
open import BoundedReduction
open import NativeTyping
open import Cubical.Data.Sigma.Base using (_×_)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Nat.Properties using (discreteℕ)
open import Cubical.Data.FinData.Properties using (discreteFin)
open import Cubical.Relation.Nullary using (Dec; yes; no; Discrete; Discrete→isSet)
open import Cubical.Foundations.Prelude using (isProp)
open import Cubical.Foundations.HLevels using (isProp×)
open import Cubical.Data.Unit.Properties using (isPropUnit)

private
  variable
    n : Nat

-- A reduction instruction records one redex and its syntactic location.
data StepCertificate (n : Nat) : Set where
  contract-at : Term n → Term (suc n) → Term n → StepCertificate n
  pi-domain : StepCertificate n → Term (suc n) → StepCertificate n
  pi-codomain : Term n → StepCertificate (suc n) → StepCertificate n
  lam-domain : StepCertificate n → Term (suc n) → StepCertificate n
  lam-body : Term n → StepCertificate (suc n) → StepCertificate n
  app-function : StepCertificate n → Term n → StepCertificate n
  app-argument : Term n → StepCertificate n → StepCertificate n

step-source : StepCertificate n → Term n
step-source (contract-at A b y) = app (lam A b) y
step-source (pi-domain p B) = pi (step-source p) B
step-source (pi-codomain A p) = pi A (step-source p)
step-source (lam-domain p b) = lam (step-source p) b
step-source (lam-body A p) = lam A (step-source p)
step-source (app-function p y) = app (step-source p) y
step-source (app-argument f p) = app f (step-source p)

step-target : StepCertificate n → Term n
step-target (contract-at A b y) = substitute b y
step-target (pi-domain p B) = pi (step-target p) B
step-target (pi-codomain A p) = pi A (step-target p)
step-target (lam-domain p b) = lam (step-target p) b
step-target (lam-body A p) = lam A (step-target p)
step-target (app-function p y) = app (step-target p) y
step-target (app-argument f p) = app f (step-target p)

step-certificate-sound : (p : StepCertificate n) → Step (step-source p) (step-target p)
step-certificate-sound (contract-at A b y) = beta
step-certificate-sound (pi-domain p B) = pi-left (step-certificate-sound p)
step-certificate-sound (pi-codomain A p) = pi-right (step-certificate-sound p)
step-certificate-sound (lam-domain p b) = lam-left (step-certificate-sound p)
step-certificate-sound (lam-body A p) = lam-right (step-certificate-sound p)
step-certificate-sound (app-function p y) = app-left (step-certificate-sound p)
step-certificate-sound (app-argument f p) = app-right (step-certificate-sound p)

data EqualityCertificate (n : Nat) : Set where
  reflexive : Term n → EqualityCertificate n
  reduction : StepCertificate n → EqualityCertificate n
  symmetric : EqualityCertificate n → EqualityCertificate n
  transitive : EqualityCertificate n → EqualityCertificate n → EqualityCertificate n

equality-source equality-target : EqualityCertificate n → Term n
equality-source (reflexive t) = t
equality-source (reduction p) = step-source p
equality-source (symmetric p) = equality-target p
equality-source (transitive p q) = equality-source p
equality-target (reflexive t) = t
equality-target (reduction p) = step-target p
equality-target (symmetric p) = equality-source p
equality-target (transitive p q) = equality-target q

EqualityAccepted : EqualityCertificate n → Set
EqualityAccepted (reflexive t) = Unit
EqualityAccepted (reduction p) = Unit
EqualityAccepted (symmetric p) = EqualityAccepted p
EqualityAccepted (transitive p q) = EqualityAccepted p × EqualityAccepted q
  × (equality-target p ≡ equality-source q)

accepted-equality : (p : EqualityCertificate n) → EqualityAccepted p
  → Beta (equality-source p) (equality-target p)
accepted-equality (reflexive t) h = beta-refl
accepted-equality (reduction p) h = beta-step (step-certificate-sound p)
accepted-equality (symmetric p) h = beta-sym (accepted-equality p h)
accepted-equality (transitive p q) (hp , hq , e) = beta-trans
  (subst (Beta (equality-source p)) e (accepted-equality p hp))
  (accepted-equality q hq)

-- BEGIN NATIVECERTIFICATE
data Certificate (n : Nat) : Set where
  sort-rule : Nat → Certificate n
  variable-rule : Fin n → Term n → Certificate n
  product-rule : (A : Term n) (B : Term (suc n)) → Nat → Nat
    → Certificate n → Certificate (suc n) → Certificate n
  abstraction-rule : (A : Term n) (b B : Term (suc n)) → Nat
    → Certificate n → Certificate (suc n) → Certificate n
  application-rule : (f y A : Term n) (B : Term (suc n))
    → Certificate n → Certificate n → Certificate n
  conversion-rule : (t A B : Term n) → Nat
    → Certificate n → Certificate n → EqualityCertificate n → Certificate n

certificate-term certificate-type : Certificate n → Term n
certificate-term (sort-rule i) = U i
certificate-term (variable-rule i A) = var i
certificate-term (product-rule A B a b p q) = pi A B
certificate-term (abstraction-rule A b B r p q) = lam A b
certificate-term (application-rule f y A B p q) = app f y
certificate-term (conversion-rule t A B r p q e) = t
certificate-type (sort-rule i) = U zero
certificate-type (variable-rule i A) = A
certificate-type (product-rule A B a b p q) = U (max (suc a) b)
certificate-type (abstraction-rule A b B r p q) = pi A B
certificate-type (application-rule f y A B p q) = substitute B y
certificate-type (conversion-rule t A B r p q e) = B

Matches : Certificate n → Term n → Term n → Set
Matches c t A = (certificate-term c ≡ t) × (certificate-type c ≡ A)

Accepted : Context n → Certificate n → Set
Accepted Γ (sort-rule i) = Unit
Accepted Γ (variable-rule i A) = lookup Γ i ≡ A
Accepted Γ (product-rule A B a b p q) = Accepted Γ p
  × Accepted (extend Γ A) q × Matches p A (U a) × Matches q B (U b)
Accepted Γ (abstraction-rule A b B r p q) = Accepted Γ p
  × Accepted (extend Γ A) q × Matches p A (U r) × Matches q b B
Accepted Γ (application-rule f y A B p q) = Accepted Γ p
  × Accepted Γ q × Matches p f (pi A B) × Matches q y A
Accepted Γ (conversion-rule t A B r p q e) = Accepted Γ p
  × Accepted Γ q × Matches p t A × Matches q B (U r)
  × EqualityAccepted e × (equality-source e ≡ A) × (equality-target e ≡ B)
-- END NATIVECERTIFICATE

private
  retarget : ∀ {Γ : Context n} {t u A B} → Typ Γ t A
    → t ≡ u → A ≡ B → Typ Γ u B
  retarget {Γ = Γ} h p q = subst (Typ Γ _) q (subst (λ t → Typ Γ t _) p h)

-- All six original inference rules are justified from checked local data.
-- This theorem interprets the checker; it does not replace native Typ.
accepted-typing : ∀ {Γ : Context n} {c : Certificate n} → Accepted Γ c
  → Typ Γ (certificate-term c) (certificate-type c)
accepted-typing {c = sort-rule i} h = universe i
accepted-typing {c = variable-rule i A} h = subst (Typ _ (var i)) h (lookup-var i)
accepted-typing {c = product-rule A B a b p q} (hp , hq , (sp , tp) , (sq , tq)) =
  product (retarget (accepted-typing hp) sp tp) (retarget (accepted-typing hq) sq tq)
accepted-typing {c = abstraction-rule A b B r p q} (hp , hq , (sp , tp) , (sq , tq)) =
  abstraction (retarget (accepted-typing hp) sp tp) (retarget (accepted-typing hq) sq tq)
accepted-typing {c = application-rule f y A B p q} (hp , hq , (sp , tp) , (sq , tq)) =
  application (retarget (accepted-typing hp) sp tp) (retarget (accepted-typing hq) sq tq)
accepted-typing {c = conversion-rule t A B r p q e}
  (hp , hq , (sp , tp) , (sq , tq) , he , se , te) =
  conversion (retarget (accepted-typing hp) sp tp) (retarget (accepted-typing hq) sq tq)
    (subst (Beta A) te (subst (λ u → Beta u (equality-target e)) se (accepted-equality e he)))

accepted-at : ∀ {Γ : Context n} {c : Certificate n} {t A}
  → Accepted Γ c → Matches c t A → Typ Γ t A
accepted-at h (p , q) = retarget (accepted-typing h) p q

-- Every native one-step derivation has an independent location code.
certify-step : {t u : Term n} → Step t u
  → Σ (StepCertificate n) (λ p → (step-source p ≡ t) × (step-target p ≡ u))
certify-step (beta {A = A} {b} {u}) = contract-at A b u , refl , refl
certify-step (pi-left {B = B} p) with certify-step p
... | c , s , t = pi-domain c B , cong (λ A → pi A B) s , cong (λ A → pi A B) t
certify-step (pi-right {A = A} p) with certify-step p
... | c , s , t = pi-codomain A c , cong (pi A) s , cong (pi A) t
certify-step (lam-left {b = b} p) with certify-step p
... | c , s , t = lam-domain c b , cong (λ A → lam A b) s , cong (λ A → lam A b) t
certify-step (lam-right {A = A} p) with certify-step p
... | c , s , t = lam-body A c , cong (lam A) s , cong (lam A) t
certify-step (app-left {u = y} p) with certify-step p
... | c , s , t = app-function c y , cong (λ f → app f y) s , cong (λ f → app f y) t
certify-step (app-right {f = f} p) with certify-step p
... | c , s , t = app-argument f c , cong (app f) s , cong (app f) t

certify-equality : {t u : Term n} → Beta t u
  → Σ (EqualityCertificate n) (λ p → EqualityAccepted p
      × (equality-source p ≡ t) × (equality-target p ≡ u))
certify-equality (beta-refl {t}) = reflexive t , tt , refl , refl
certify-equality (beta-step p) with certify-step p
... | c , s , t = reduction c , tt , s , t
certify-equality (beta-sym p) with certify-equality p
... | c , h , s , t = symmetric c , h , t , s
certify-equality (beta-trans p q) with certify-equality p | certify-equality q
... | c , h , s , t | d , k , u , v =
  transitive c d , (h , k , t ∙ sym u) , s , v

-- Completeness certifies the ORIGINAL relation, rather than replacing it.
-- A typing proof is used to construct a raw certificate, never as a field
-- in the certificate or in its independently computed acceptance predicate.
certify : ∀ {Γ : Context n} {t A} → Typ Γ t A
  → Σ (Certificate n) (λ c → Accepted Γ c × Matches c t A)
certify (universe i) = sort-rule i , tt , refl , refl
certify {Γ = Γ} (lookup-var i) = variable-rule i (lookup Γ i) , refl , refl , refl
certify (product {A} {B} {a} {b} p q) with certify p | certify q
... | c , hc , mc | d , hd , md =
  product-rule A B a b c d , (hc , hd , mc , md) , refl , refl
certify (abstraction {A} {b} {B} {r} p q) with certify p | certify q
... | c , hc , mc | d , hd , md =
  abstraction-rule A b B r c d , (hc , hd , mc , md) , refl , refl
certify (application {f} {y} {A} {B} p q) with certify p | certify q
... | c , hc , mc | d , hd , md =
  application-rule f y A B c d , (hc , hd , mc , md) , refl , refl
certify (conversion {t} {A} {B} {r} p q e) with certify p | certify q | certify-equality e
... | c , hc , mc | d , hd , md | f , hf , sf , tf =
  conversion-rule t A B r c d f , (hc , hd , mc , md , hf , sf , tf) , refl , refl

-- These implications specify exact adequacy, without conflating the two
-- independently defined judgments or asserting equality of proof objects.
certificate-adequacy : ∀ (Γ : Context n) (t A : Term n)
  → (Typ Γ t A → Σ (Certificate n) (λ c → Accepted Γ c × Matches c t A))
    × ((Σ (Certificate n) (λ c → Accepted Γ c × Matches c t A)) → Typ Γ t A)
certificate-adequacy Γ t A = certify , λ { (c , h , m) → accepted-at h m }

private
  -- A computed structural equality code avoids assuming constructor
  -- injectivity or any equality-reflection principle in Cubical Agda.
  Same : Term n → Term n → Set
  Same (U i) (U j) = i ≡ j
  Same (var i) (var j) = i ≡ j
  Same (pi A B) (pi C D) = Same A C × Same B D
  Same (lam A b) (lam C d) = Same A C × Same b d
  Same (app f x) (app g y) = Same f g × Same x y
  Same _ _ = ⊥

  same-refl : (t : Term n) → Same t t
  same-refl (U i) = refl
  same-refl (var i) = refl
  same-refl (pi A B) = same-refl A , same-refl B
  same-refl (lam A b) = same-refl A , same-refl b
  same-refl (app f y) = same-refl f , same-refl y

  same-equality : (t u : Term n) → Same t u → t ≡ u
  same-equality (U i) (U j) p = cong U p
  same-equality (var i) (var j) p = cong var p
  same-equality (pi A B) (pi C D) (p , q) =
    cong₂ pi (same-equality A C p) (same-equality B D q)
  same-equality (lam A b) (lam C d) (p , q) =
    cong₂ lam (same-equality A C p) (same-equality b d q)
  same-equality (app f x) (app g y) (p , q) =
    cong₂ app (same-equality f g p) (same-equality x y q)
  same-equality (U i) (var j) ()
  same-equality (U i) (pi A B) ()
  same-equality (U i) (lam A b) ()
  same-equality (U i) (app f y) ()
  same-equality (var i) (U j) ()
  same-equality (var i) (pi A B) ()
  same-equality (var i) (lam A b) ()
  same-equality (var i) (app f y) ()
  same-equality (pi A B) (U i) ()
  same-equality (pi A B) (var i) ()
  same-equality (pi A B) (lam C b) ()
  same-equality (pi A B) (app f y) ()
  same-equality (lam A b) (U i) ()
  same-equality (lam A b) (var i) ()
  same-equality (lam A b) (pi C D) ()
  same-equality (lam A b) (app f y) ()
  same-equality (app f y) (U i) ()
  same-equality (app f y) (var i) ()
  same-equality (app f y) (pi A B) ()
  same-equality (app f y) (lam A b) ()

  infixr 4 _×?_
  _×?_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
  yes p ×? yes q = yes (p , q)
  yes p ×? no nq = no (λ z → nq (snd z))
  no np ×? q = no (λ z → np (fst z))

  same? : (t u : Term n) → Dec (Same t u)
  same? (U i) (U j) = discreteℕ i j
  same? (var i) (var j) = discreteFin i j
  same? (pi A B) (pi C D) = same? A C ×? same? B D
  same? (lam A b) (lam C d) = same? A C ×? same? b d
  same? (app f x) (app g y) = same? f g ×? same? x y
  same? (U i) (var j) = no (λ ())
  same? (U i) (pi A B) = no (λ ())
  same? (U i) (lam A b) = no (λ ())
  same? (U i) (app f y) = no (λ ())
  same? (var i) (U j) = no (λ ())
  same? (var i) (pi A B) = no (λ ())
  same? (var i) (lam A b) = no (λ ())
  same? (var i) (app f y) = no (λ ())
  same? (pi A B) (U i) = no (λ ())
  same? (pi A B) (var i) = no (λ ())
  same? (pi A B) (lam C b) = no (λ ())
  same? (pi A B) (app f y) = no (λ ())
  same? (lam A b) (U i) = no (λ ())
  same? (lam A b) (var i) = no (λ ())
  same? (lam A b) (pi C D) = no (λ ())
  same? (lam A b) (app f y) = no (λ ())
  same? (app f y) (U i) = no (λ ())
  same? (app f y) (var i) = no (λ ())
  same? (app f y) (pi A B) = no (λ ())
  same? (app f y) (lam A b) = no (λ ())

term-discrete : Discrete (Term n)
term-discrete t u with same? t u
... | yes p = yes (same-equality t u p)
... | no np = no (λ p → np (subst (Same t) p (same-refl t)))

matches? : (c : Certificate n) (t A : Term n) → Dec (Matches c t A)
matches? c t A = term-discrete (certificate-term c) t
  ×? term-discrete (certificate-type c) A

equality-accepted? : (e : EqualityCertificate n) → Dec (EqualityAccepted e)
equality-accepted? (reflexive t) = yes tt
equality-accepted? (reduction p) = yes tt
equality-accepted? (symmetric p) = equality-accepted? p
equality-accepted? (transitive p q) = equality-accepted? p ×? equality-accepted? q
  ×? term-discrete (equality-target p) (equality-source q)

-- The algorithm checks the finite proof tree and its explicit conversion
-- witnesses; it never asks a normalization or native-typing oracle.
accepted? : (Γ : Context n) (c : Certificate n) → Dec (Accepted Γ c)
accepted? Γ (sort-rule i) = yes tt
accepted? Γ (variable-rule i A) = term-discrete (lookup Γ i) A
accepted? Γ (product-rule A B a b p q) = accepted? Γ p
  ×? accepted? (extend Γ A) q ×? matches? p A (U a) ×? matches? q B (U b)
accepted? Γ (abstraction-rule A b B r p q) = accepted? Γ p
  ×? accepted? (extend Γ A) q ×? matches? p A (U r) ×? matches? q b B
accepted? Γ (application-rule f y A B p q) = accepted? Γ p
  ×? accepted? Γ q ×? matches? p f (pi A B) ×? matches? q y A
accepted? Γ (conversion-rule t A B r p q e) = accepted? Γ p
  ×? accepted? Γ q ×? matches? p t A ×? matches? q B (U r)
  ×? equality-accepted? e ×? term-discrete (equality-source e) A
  ×? term-discrete (equality-target e) B

private
  term-isSet : isSet (Term n)
  term-isSet = Discrete→isSet term-discrete

  matches-isProp : (c : Certificate n) (t A : Term n) → isProp (Matches c t A)
  matches-isProp c t A = isProp× (term-isSet _ _) (term-isSet _ _)

equality-accepted-isProp : (e : EqualityCertificate n) → isProp (EqualityAccepted e)
equality-accepted-isProp (reflexive t) = isPropUnit
equality-accepted-isProp (reduction p) = isPropUnit
equality-accepted-isProp (symmetric p) = equality-accepted-isProp p
equality-accepted-isProp (transitive p q) = isProp× (equality-accepted-isProp p)
  (isProp× (equality-accepted-isProp q) (term-isSet _ _))

accepted-isProp : (Γ : Context n) (c : Certificate n) → isProp (Accepted Γ c)
accepted-isProp Γ (sort-rule i) = isPropUnit
accepted-isProp Γ (variable-rule i A) = term-isSet _ _
accepted-isProp Γ (product-rule A B a b p q) = isProp× (accepted-isProp Γ p)
  (isProp× (accepted-isProp (extend Γ A) q)
    (isProp× (matches-isProp p A (U a)) (matches-isProp q B (U b))))
accepted-isProp Γ (abstraction-rule A b B r p q) = isProp× (accepted-isProp Γ p)
  (isProp× (accepted-isProp (extend Γ A) q)
    (isProp× (matches-isProp p A (U r)) (matches-isProp q b B)))
accepted-isProp Γ (application-rule f y A B p q) = isProp× (accepted-isProp Γ p)
  (isProp× (accepted-isProp Γ q)
    (isProp× (matches-isProp p f (pi A B)) (matches-isProp q y A)))
accepted-isProp Γ (conversion-rule t A B r p q e) = isProp× (accepted-isProp Γ p)
  (isProp× (accepted-isProp Γ q) (isProp× (matches-isProp p t A)
    (isProp× (matches-isProp q B (U r)) (isProp× (equality-accepted-isProp e)
      (isProp× (term-isSet _ _) (term-isSet _ _))))))
