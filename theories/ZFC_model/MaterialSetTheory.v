(** An independent first-order deduction language for the foundation audit.
    This file does not assert that BZC, GCH, or the supplied hierarchy is
    satisfied. General logical soundness exposes theory satisfaction as a
    premise. The bounded-separation schema below is syntax, not a Rocq axiom;
    its Ens satisfaction is proved specifically for bounded-formula predicates. *)
From Stdlib Require Import Lists.List.
From Equations Require Import Equations.
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax.
From PTSrkModel Require Import BoundedFormulas BoundedFormulaTransport.

Module MaterialSetTheory.

(** The language has variables only as terms, equality and membership as
    its only relation symbols, and genuinely unbounded quantifiers. *)
Inductive Formula : nat -> Type :=
| equal {n} (x y : Fin n) : Formula n
| member {n} (x y : Fin n) : Formula n
| falsum {n} : Formula n
| conj {n} (p q : Formula n) : Formula n
| disj {n} (p q : Formula n) : Formula n
| impl {n} (p q : Formula n) : Formula n
| all {n} (p : Formula (S n)) : Formula n
| ex {n} (p : Formula (S n)) : Formula n.

Definition neg {n} (p : Formula n) := impl p falsum.
Definition iffF {n} (p q : Formula n) := conj (impl p q) (impl q p).

Fixpoint holds {n} (p : Formula n) : (Fin n -> Ens) -> Prop :=
  match p with
  | @equal _ x y => fun r => EQ (r x) (r y)
  | @member _ x y => fun r => IN (r x) (r y)
  | @falsum _ => fun _ => False
  | @conj _ p q => fun r => holds p r /\ holds q r
  | @disj _ p q => fun r => holds p r \/ holds q r
  | @impl _ p q => fun r => holds p r -> holds q r
  | @all _ p => fun r => forall x : Ens, holds p (fin_match x r)
  | @ex _ p => fun r => exists x : Ens, holds p (fin_match x r)
  end.

Theorem holds_extensional {n} (p : Formula n) : forall r r',
  (forall i, EQ (r i) (r' i)) -> (holds p r <-> holds p r').
Proof.
  induction p; intros r r' E; cbn [holds].
  - split; intro H.
    + eapply EQ_tran; [apply EQ_sym, E |]. eapply EQ_tran; [exact H | apply E].
    + eapply EQ_tran; [apply E |]. eapply EQ_tran; [exact H | apply EQ_sym, E].
  - split; intro H.
    + eapply IN_sound_right; [apply E |]. eapply IN_sound_left; [apply E | exact H].
    + eapply IN_sound_right; [apply EQ_sym, E |]. eapply IN_sound_left; [apply EQ_sym, E | exact H].
  - tauto.
  - rewrite (IHp1 r r' E), (IHp2 r r' E); reflexivity.
  - rewrite (IHp1 r r' E), (IHp2 r r' E); reflexivity.
  - rewrite (IHp1 r r' E), (IHp2 r r' E); reflexivity.
  - split; intros H x.
    + apply (proj1 (IHp _ _ (formula_environment_extend x r r' E))), H.
    + apply (proj2 (IHp _ _ (formula_environment_extend x r r' E))), H.
  - split; intros [x H]; exists x.
    + apply (proj1 (IHp _ _ (formula_environment_extend x r r' E))); exact H.
    + apply (proj2 (IHp _ _ (formula_environment_extend x r r' E))); exact H.
Qed.

Fixpoint rename {n m} (f : Fin n -> Fin m) (p : Formula n) : Formula m :=
  match p in Formula k return (Fin k -> Fin m) -> Formula m with
  | @equal _ x y => fun f => equal (f x) (f y)
  | @member _ x y => fun f => member (f x) (f y)
  | @falsum _ => fun _ => falsum
  | @conj _ p q => fun f => conj (rename f p) (rename f q)
  | @disj _ p q => fun f => disj (rename f p) (rename f q)
  | @impl _ p q => fun f => impl (rename f p) (rename f q)
  | @all _ p => fun f => all (rename (weak f) p)
  | @ex _ p => fun f => ex (rename (weak f) p)
  end f.

Theorem holds_rename {n} (p : Formula n) : forall m (f : Fin n -> Fin m) r,
  holds (rename f p) r <-> holds p (fun i => r (f i)).
Proof.
  induction p; intros m f r; cbn [rename holds]; try reflexivity.
  - rewrite IHp1, IHp2; reflexivity.
  - rewrite IHp1, IHp2; reflexivity.
  - rewrite IHp1, IHp2; reflexivity.
  - assert (E : forall x, holds (rename (weak f) p) (fin_match x r) <->
      holds p (fin_match x (fun i => r (f i)))).
    { intro x; rewrite IHp. apply holds_extensional.
      intro i; dependent elimination i; apply EQ_refl. }
    setoid_rewrite E; reflexivity.
  - assert (E : forall x, holds (rename (weak f) p) (fin_match x r) <->
      holds p (fin_match x (fun i => r (f i)))).
    { intro x; rewrite IHp. apply holds_extensional.
      intro i; dependent elimination i; apply EQ_refl. }
    setoid_rewrite E; reflexivity.
Qed.

Definition shift {n} (p : Formula n) := rename fsucc p.
Definition instantiate {n} (p : Formula (S n)) (x : Fin n) :=
  rename (fin_match x (fun i => i)) p.

Lemma holds_shift {n} (p : Formula n) r x :
  holds (shift p) (fin_match x r) <-> holds p r.
Proof. unfold shift; rewrite holds_rename; apply holds_extensional; intro i; apply EQ_refl. Qed.

Lemma holds_instantiate {n} (p : Formula (S n)) (x : Fin n) r :
  holds (instantiate p x) r <-> holds p (fin_match (r x) r).
Proof.
  unfold instantiate; rewrite holds_rename; apply holds_extensional.
  intro i; dependent elimination i; apply EQ_refl.
Qed.

Definition context_holds {n} (G : list (Formula n)) r :=
  forall p, In p G -> holds p r.
Lemma context_holds_cons {n} (G : list (Formula n)) p r :
  context_holds G r -> holds p r -> context_holds (cons p G) r.
Proof. intros HG HP q [E | HQ]; [subst; exact HP | apply HG; exact HQ]. Qed.
Lemma context_holds_shift {n} (G : list (Formula n)) r x :
  context_holds G r -> context_holds (map shift G) (fin_match x r).
Proof.
  intros HG p HP. apply in_map_iff in HP as [q [E HQ]]; subst p.
  apply holds_shift, HG; exact HQ.
Qed.

(** A theory is a collection of syntactic formula instances. The deduction
    rules below never refer to Ens semantics or to the PTS target. The only
    classical rule is excluded middle. The nonempty-domain rule reflects
    the conventional inhabited semantics of first-order set theory. *)
Definition Theory := forall n, Formula n -> Prop.
Inductive derives (T : Theory) : forall n, list (Formula n) -> Formula n -> Prop :=
| d_hyp n G p : In p G -> derives T n G p
| d_axiom n G p : T n p -> derives T n G p
| d_false n G p : derives T n G falsum -> derives T n G p
| d_and n G p q : derives T n G p -> derives T n G q -> derives T n G (conj p q)
| d_and_left n G p q : derives T n G (conj p q) -> derives T n G p
| d_and_right n G p q : derives T n G (conj p q) -> derives T n G q
| d_or_left n G p q : derives T n G p -> derives T n G (disj p q)
| d_or_right n G p q : derives T n G q -> derives T n G (disj p q)
| d_or_elim n G p q z : derives T n G (disj p q) ->
    derives T n (cons p G) z -> derives T n (cons q G) z -> derives T n G z
| d_impl n G p q : derives T n (cons p G) q -> derives T n G (impl p q)
| d_apply n G p q : derives T n G (impl p q) -> derives T n G p -> derives T n G q
| d_all n G p : derives T (S n) (map shift G) p -> derives T n G (all p)
| d_specialize n G p x : derives T n G (all p) -> derives T n G (instantiate p x)
| d_exists n G p x : derives T n G (instantiate p x) -> derives T n G (ex p)
| d_exists_elim n G p q : derives T n G (ex p) ->
    derives T (S n) (cons p (map shift G)) (shift q) -> derives T n G q
| d_reflexivity n G x : derives T n G (equal x x)
| d_equality n G p x y : derives T n G (equal x y) ->
    derives T n G (instantiate p x) -> derives T n G (instantiate p y)
| d_classical n G p : derives T n G (disj p (neg p))
| d_nonempty n G : derives T n G (ex (equal fzero fzero)).

Definition theory_holds (T : Theory) := forall n p, T n p -> forall r, holds p r.

Theorem logical_soundness (classical_logic : forall P : Prop, P \/ ~ P) T :
  theory_holds T -> forall n G p, derives T n G p -> forall r,
    context_holds G r -> holds p r.
Proof.
  intros TH n G p HD. induction HD; intros r HG; cbn [holds].
  - apply HG; exact H.
  - apply TH; exact H.
  - exfalso; exact (IHHD r HG).
  - split; [apply IHHD1 | apply IHHD2]; exact HG.
  - exact (proj1 (IHHD r HG)).
  - exact (proj2 (IHHD r HG)).
  - left; apply IHHD; exact HG.
  - right; apply IHHD; exact HG.
  - destruct (IHHD1 r HG) as [HP | HQ].
    + apply IHHD2, context_holds_cons; assumption.
    + apply IHHD3, context_holds_cons; assumption.
  - intro HP; apply IHHD, context_holds_cons; assumption.
  - apply (IHHD1 r HG), IHHD2; exact HG.
  - intro x; apply IHHD, context_holds_shift; exact HG.
  - apply holds_instantiate, (IHHD r HG).
  - exists (r x); apply holds_instantiate, IHHD; exact HG.
  - destruct (IHHD1 r HG) as [x HX].
    apply (proj1 (holds_shift q r x)), IHHD2, context_holds_cons;
      [apply context_holds_shift; exact HG | exact HX].
  - apply EQ_refl.
  - apply holds_instantiate.
    assert (E : forall i, EQ (fin_match (r x) r i) (fin_match (r y) r i)).
    { intro i; dependent elimination i; cbn [fin_match]; [apply IHHD1; exact HG | apply EQ_refl]. }
    apply (proj1 (holds_extensional p _ _ E)), holds_instantiate, IHHD2; exact HG.
  - apply classical_logic.
  - exists Vide; apply EQ_refl.
Qed.

Print Assumptions holds_extensional.
Print Assumptions holds_rename.
Print Assumptions holds_instantiate.
Print Assumptions logical_soundness.

(** Translate the existing bounded language by explicit membership guards.
    This is not an arbitrary semantic predicate embedded as a formula. *)
Fixpoint embed_bounded {n} (p : Bounded.Formula n) : Formula n :=
  match p with
  | @Bounded.equal _ x y => equal x y
  | @Bounded.member _ x y => member x y
  | @Bounded.falsum _ => falsum
  | @Bounded.conj _ p q => conj (embed_bounded p) (embed_bounded q)
  | @Bounded.disj _ p q => disj (embed_bounded p) (embed_bounded q)
  | @Bounded.impl _ p q => impl (embed_bounded p) (embed_bounded q)
  | @Bounded.all _ b p => all (impl (member fzero (fsucc b)) (embed_bounded p))
  | @Bounded.ex _ b p => ex (conj (member fzero (fsucc b)) (embed_bounded p))
  end.

Theorem embed_bounded_correct {n} (p : Bounded.Formula n) : forall r,
  holds (embed_bounded p) r <-> Bounded.holds p r.
Proof.
  induction p; intro r; cbn [embed_bounded holds Bounded.holds fin_match]; try reflexivity.
  - rewrite IHp1, IHp2; reflexivity.
  - rewrite IHp1, IHp2; reflexivity.
  - rewrite IHp1, IHp2; reflexivity.
  - split; intros H x HX.
    + apply (proj1 (IHp (fin_match x r))), H; exact HX.
    + apply (proj2 (IHp (fin_match x r))), H; exact HX.
  - split; intros [x [HX HP]]; exists x; split; [exact HX | | exact HX |].
    + apply (proj1 (IHp (fin_match x r))); exact HP.
    + apply (proj2 (IHp (fin_match x r))); exact HP.
Qed.

(** p has the separated element as its first free variable. The new set Y
    is inserted AFTER that element, so Y cannot occur in p. All n other
    parameters remain available. Free variables in an axiom instance are
    universally interpreted by theory_holds. *)
Definition bounded_separation {n} (A : Fin n) (p : Bounded.Formula (S n)) : Formula n :=
  ex (all (iffF (member fzero (fsucc fzero))
    (conj (member fzero (fsucc (fsucc A)))
      (rename (weak (@fsucc n)) (embed_bounded p))))).

Lemma separation_predicate_correct {n} (p : Bounded.Formula (S n)) r Y x :
  holds (rename (weak (@fsucc n)) (embed_bounded p)) (fin_match x (fin_match Y r)) <->
    Bounded.holds p (fin_match x r).
Proof.
  rewrite holds_rename. transitivity (holds (embed_bounded p) (fin_match x r)).
  - apply holds_extensional. intro i; dependent elimination i; apply EQ_refl.
  - apply embed_bounded_correct.
Qed.

(** This theorem identifies the statement of the schema. It does NOT prove
    its truth in Ens or certify unrestricted Comp as bounded separation. *)
Theorem bounded_separation_statement {n} (A : Fin n) p r :
  holds (bounded_separation A p) r <->
    exists Y, forall x, IN x Y <-> IN x (r A) /\ Bounded.holds p (fin_match x r).
Proof.
  unfold bounded_separation, iffF. cbn [holds fin_match].
  setoid_rewrite separation_predicate_correct. reflexivity.
Qed.

Inductive BoundedSeparation : Theory :=
| bounded_separation_instance n (A : Fin n) (p : Bounded.Formula (S n)) :
    BoundedSeparation n (bounded_separation A p).

Theorem bounded_separation_axiom_shape n q : BoundedSeparation n q ->
  exists (A : Fin n) (p : Bounded.Formula (S n)), q = bounded_separation A p.
Proof. intro H; dependent elimination H; eauto. Qed.

(** Only predicates given by the bounded syntax enter this construction.
    The proof uses the ambient Ens implementation of Comp; it does not
    assert that arbitrary uses of Comp elsewhere have bounded definitions,
    or provide an interpretation of Ens in a weak first-order set theory. *)
Theorem bounded_separation_satisfied {n} (A : Fin n)
  (p : Bounded.Formula (S n)) r : holds (bounded_separation A p) r.
Proof.
  apply bounded_separation_statement.
  set (P := fun x => Bounded.holds p (fin_match x r)).
  assert (EP : forall x y, P x -> EQ x y -> P y).
  { intros x y HP E.
    assert (Er : forall i, EQ (fin_match x r i) (fin_match y r i)).
    { intro i; dependent elimination i; cbn [fin_match]; [exact E | apply EQ_refl]. }
    apply (proj1 (BoundedFormulaTransport.holds_extensional p _ _ Er)); exact HP. }
  exists (Comp (r A) P). intro x; split.
  - intro HX; split.
    + exact (Comp_INC (r A) P x HX).
    + exact (IN_Comp_P (r A) x P EP HX).
  - intros [HX HP]. exact (IN_P_Comp (r A) x P EP HX HP).
Qed.

Theorem bounded_separation_theory_satisfied : theory_holds BoundedSeparation.
Proof.
  intros n q H r; dependent elimination H; apply bounded_separation_satisfied.
Qed.

Corollary bounded_theory_logical_soundness
  (classical_logic : forall P : Prop, P \/ ~ P) :
  forall n G p,
    derives BoundedSeparation n G p -> forall r, context_holds G r -> holds p r.
Proof. apply logical_soundness; [exact classical_logic | exact bounded_separation_theory_satisfied]. Qed.

Print Assumptions embed_bounded_correct.
Print Assumptions separation_predicate_correct.
Print Assumptions bounded_separation_statement.
Print Assumptions bounded_separation_axiom_shape.
Print Assumptions bounded_separation_satisfied.
Print Assumptions bounded_separation_theory_satisfied.
Print Assumptions bounded_theory_logical_soundness.
Check logical_soundness.
Check bounded_separation_statement.
Check bounded_separation_theory_satisfied.
Check bounded_theory_logical_soundness.

End MaterialSetTheory.
