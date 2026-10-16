(** Actual first-order Zermelo axioms, with bounded Separation.
    Convention: ZFC without Replacement, restricting Separation to bounded
    formulas (Shulman, Unbounded quantifiers and strong axioms in topos
    theory, slide 7, https://home.sandiego.edu/~shulman/papers/uqsatalk.pdf).

    The satisfaction proofs below concern the ambient Ens encoding. They
    do not derive the native PTS model construction inside this first-order
    theory. In particular, Ens's Type-indexed sup is NOT being certified as
    a construction available in BZC. Classical logic and ordinary Choice,
    when used, remain explicit premises, not new Rocq axioms. *)
From Equations Require Import Equations.
From ZFC Require Import Sets Axioms Cartesian.
From PTSrk Require Import Syntax.
From PTSrkModel Require Import MaterialSetTheory BoundedFormulas
  SetFunctions SetApplication CountableDichotomy.

Module MaterialZermelo.
Import MaterialSetTheory.MaterialSetTheory.

Local Abbreviation v0 := fzero.
Local Abbreviation v1 := (fsucc fzero).
Local Abbreviation v2 := (fsucc (fsucc fzero)).
Local Abbreviation v3 := (fsucc (fsucc (fsucc fzero))).
Local Abbreviation v4 := (fsucc (fsucc (fsucc (fsucc fzero)))).

(** These are formula builders, containing only first-order syntax. *)
Definition emptyF {n} (x : Fin n) : Formula n := all (neg (member v0 (fsucc x))).
Definition subsetF {n} (x y : Fin n) : Formula n :=
  all (impl (member v0 (fsucc x)) (member v0 (fsucc y))).
Definition pairF {n} (p x y : Fin n) : Formula n :=
  all (iffF (member v0 (fsucc p))
    (disj (equal v0 (fsucc x)) (equal v0 (fsucc y)))).
Definition unionF {n} (u a : Fin n) : Formula n :=
  all (iffF (member v0 (fsucc u))
    (ex (conj (member v0 (fsucc (fsucc a))) (member v1 v0)))).
Definition powerF {n} (p a : Fin n) : Formula n :=
  all (iffF (member v0 (fsucc p)) (subsetF v0 (fsucc a))).
Definition successorF {n} (s x : Fin n) : Formula n :=
  all (iffF (member v0 (fsucc s))
    (disj (member v0 (fsucc x)) (equal v0 (fsucc x)))).

Lemma emptyF_correct {n} (r : Fin n -> Ens) x :
  holds (emptyF x) r <-> forall z, ~ IN z (r x).
Proof. reflexivity. Qed.
Lemma subsetF_correct {n} (r : Fin n -> Ens) x y :
  holds (subsetF x y) r <-> INC (r x) (r y).
Proof. reflexivity. Qed.
Lemma pairF_correct {n} (r : Fin n -> Ens) p x y :
  holds (pairF p x y) r <-> forall z, IN z (r p) <-> EQ z (r x) \/ EQ z (r y).
Proof. reflexivity. Qed.
Lemma unionF_correct {n} (r : Fin n -> Ens) u a :
  holds (unionF u a) r <-> forall z, IN z (r u) <-> exists y, IN y (r a) /\ IN z y.
Proof. reflexivity. Qed.
Lemma powerF_correct {n} (r : Fin n -> Ens) p a :
  holds (powerF p a) r <-> forall z, IN z (r p) <-> INC z (r a).
Proof. reflexivity. Qed.
Lemma successorF_correct {n} (r : Fin n -> Ens) s x :
  holds (successorF s x) r <-> forall z, IN z (r s) <-> IN z (r x) \/ EQ z (r x).
Proof. reflexivity. Qed.

(** Closed sentences are provided uniformly at any ambient variable scope;
    no parameter of the surrounding scope occurs in them. *)
Definition extensionality {n} : Formula n :=
  all (all (impl (all (iffF (member v0 v2) (member v0 v1))) (equal v1 v0))).
Definition empty_set {n} : Formula n := ex (emptyF v0).
Definition pairing {n} : Formula n := all (all (ex (pairF v0 v2 v1))).
Definition union {n} : Formula n := all (ex (unionF v0 v1)).
Definition powerset {n} : Formula n := all (ex (powerF v0 v1)).
Definition infinity {n} : Formula n :=
  ex (conj (ex (conj (member v0 v1) (emptyF v0)))
    (all (impl (member v0 v1)
      (ex (conj (member v0 v2) (successorF v0 v1)))))).
Definition foundation {n} : Formula n :=
  all (impl (ex (member v0 v1))
    (ex (conj (member v0 v1)
      (all (impl (member v0 v1) (neg (member v0 v2))))))).

Theorem extensionality_satisfied {n} (r : Fin n -> Ens) : holds extensionality r.
Proof.
  change (forall x y, (forall z, IN z x <-> IN z y) -> EQ x y).
  intros x y H. apply INC_EQ; intros z Hz.
  - exact (proj1 (H z) Hz).
  - exact (proj2 (H z) Hz).
Qed.
Theorem empty_set_satisfied {n} (r : Fin n -> Ens) : holds empty_set r.
Proof.
  change (exists e, forall x, ~ IN x e).
  exists Vide; intros x Hx; destruct (Vide_est_vide x Hx).
Qed.
Theorem pairing_satisfied {n} (r : Fin n -> Ens) : holds pairing r.
Proof.
  change (forall x y, exists p, forall z, IN z p <-> EQ z x \/ EQ z y).
  intros x y; exists (Paire x y); intro z; split.
  - apply Paire_IN.
  - intros [E | E]; eapply IN_sound_left; [apply EQ_sym; exact E | apply IN_Paire_left
      | apply EQ_sym; exact E | apply IN_Paire_right].
Qed.
Theorem union_satisfied {n} (r : Fin n -> Ens) : holds union r.
Proof.
  change (forall a, exists u, forall z, IN z u <-> exists y, IN y a /\ IN z y).
  intro x; exists (Union x); intro z; split.
  - intro H; destruct (Union_IN x z H) as [y [Hy Hz]]; exists y; auto.
  - intros [y [Hy Hz]]; eapply IN_Union; eassumption.
Qed.
Theorem powerset_satisfied {n} (r : Fin n -> Ens) : holds powerset r.
Proof.
  change (forall a, exists p, forall z, IN z p <-> INC z a).
  intro x; exists (Power x); intro z; split; [apply IN_Power_INC | apply INC_IN_Power].
Qed.

(** Genuine von Neumann successors, not the model's singleton-numeral codes.
    Their meta-level collection is used ONLY to establish Ens satisfaction. *)
Definition set_successor x := Union (Paire x (Sing x)).
Lemma set_successor_membership x z :
  IN z (set_successor x) <-> IN z x \/ EQ z x.
Proof.
  split.
  - intro H. destruct (Union_IN _ _ H) as [y [Hy Hz]].
    destruct (Paire_IN _ _ _ Hy) as [E | E].
    + left; eapply IN_sound_right; eassumption.
    + right; apply IN_Sing_EQ. eapply IN_sound_right; eassumption.
  - intros [Hz | E].
    + eapply IN_Union; [apply IN_Paire_left | exact Hz].
    + eapply IN_Union; [apply IN_Paire_right |].
      eapply IN_sound_left; [apply EQ_sym; exact E | apply IN_Sing].
Qed.
Fixpoint von_neumann n : Ens :=
  match n with 0 => Vide | S k => set_successor (von_neumann k) end.
Definition inductive_set := sup nat von_neumann.

Theorem infinity_satisfied {n} (r : Fin n -> Ens) : holds infinity r.
Proof.
  change (exists I, (exists e, IN e I /\ forall z, ~ IN z e) /\
    forall x, IN x I -> exists y, IN y I /\ forall z, IN z y <-> IN z x \/ EQ z x).
  exists inductive_set; split.
  - exists Vide; split; [exists 0; apply EQ_refl |].
    intros z Hz; destruct (Vide_est_vide z Hz).
  - intros x [k Ex]; exists (von_neumann (S k)); split.
    + exists (S k); apply EQ_refl.
    + intro z; cbn [von_neumann]; rewrite set_successor_membership. split.
      * intros [Hz | E].
        -- left; eapply IN_sound_right; [apply EQ_sym; exact Ex | exact Hz].
        -- right; eapply EQ_tran; [exact E | apply EQ_sym; exact Ex].
      * intros [Hz | E].
        -- left; eapply IN_sound_right; [exact Ex | exact Hz].
        -- right; eapply EQ_tran; eassumption.
Qed.

Lemma membership_accessible_extensional x : Acc IN x ->
  forall y, EQ x y -> Acc IN y.
Proof.
  intro H; induction H as [x HX IH]; intros y E; constructor; intros z Hz.
  apply (IH z); [eapply IN_sound_right; [apply EQ_sym; exact E | exact Hz] | apply EQ_refl].
Qed.
Theorem membership_accessible x : Acc IN x.
Proof.
  induction x as [I f IH]. constructor; intros y [i E].
  eapply membership_accessible_extensional; [apply IH | apply EQ_sym; exact E].
Qed.

Lemma member_minimal (classical_logic : forall P : Prop, P \/ ~ P) A x :
  Acc IN x -> IN x A -> exists y, IN y A /\ forall z, IN z y -> ~ IN z A.
Proof.
  intro H; induction H as [x HX IH]; intro Hx.
  destruct (classical_logic (exists y, IN y x /\ IN y A)) as [[y [Hy HA]] | Hnone].
  - exact (IH y Hy HA).
  - exists x; split; [exact Hx |]. intros z Hz HA; apply Hnone; exists z; auto.
Qed.
Theorem foundation_satisfied (classical_logic : forall P : Prop, P \/ ~ P)
  {n} (r : Fin n -> Ens) : holds foundation r.
Proof.
  intros A [x Hx]. exact (member_minimal classical_logic A x (membership_accessible x) Hx).
Qed.

Inductive BoundedZermelo : Theory :=
| bz_extensionality n : BoundedZermelo n extensionality
| bz_empty n : BoundedZermelo n empty_set
| bz_pairing n : BoundedZermelo n pairing
| bz_union n : BoundedZermelo n union
| bz_powerset n : BoundedZermelo n powerset
| bz_infinity n : BoundedZermelo n infinity
| bz_foundation n : BoundedZermelo n foundation
| bz_separation n (A : Fin n) (p : Bounded.Formula (S n)) :
    BoundedZermelo n (bounded_separation A p).

Theorem bounded_zermelo_satisfied (classical_logic : forall P : Prop, P \/ ~ P) :
  theory_holds BoundedZermelo.
Proof.
  intros n p H r; destruct H.
  - apply extensionality_satisfied.
  - apply empty_set_satisfied.
  - apply pairing_satisfied.
  - apply union_satisfied.
  - apply powerset_satisfied.
  - apply infinity_satisfied.
  - apply foundation_satisfied; exact classical_logic.
  - apply bounded_separation_satisfied.
Qed.

Corollary bounded_zermelo_logical_soundness
  (classical_logic : forall P : Prop, P \/ ~ P) n G p :
  derives BoundedZermelo n G p -> forall r, context_holds G r -> holds p r.
Proof.
  apply logical_soundness; [exact classical_logic | apply bounded_zermelo_satisfied; exact classical_logic].
Qed.

(** Choice is formulated with actual set graphs. The imported ordered-pair
    syntax expands to equality/membership and bounded quantifiers only;
    the library's pair is {{x},{empty,{y}}}, not Kuratowski's pair.
    The graph clause is essential: functionality alone permits junk members. *)
Definition applicationF {n} (g x y : Fin n) : Formula n :=
  embed_bounded (Bounded.applicationF g x y).
Definition ordered_pairF {n} (e x y : Fin n) : Formula n :=
  embed_bounded (Bounded.coupleF e x y).
Lemma applicationF_correct {n} (r : Fin n -> Ens) g x y :
  holds (applicationF g x y) r <-> application (r g) (r x) (r y).
Proof. unfold applicationF; rewrite embed_bounded_correct; apply Bounded.application_correct. Qed.
Lemma ordered_pairF_correct {n} (r : Fin n -> Ens) e x y :
  holds (ordered_pairF e x y) r <-> EQ (r e) (Couple (r x) (r y)).
Proof. unfold ordered_pairF; rewrite embed_bounded_correct; apply Bounded.couple_correct. Qed.

Definition graphF {n} (c : Fin n) : Formula n :=
  all (impl (member v0 (fsucc c)) (ex (ex (ordered_pairF v2 v1 v0)))).
Definition choiceLawsF {n} (A c : Fin n) : Formula n :=
  conj (all (impl (member v0 (fsucc A))
      (ex (applicationF (fsucc (fsucc c)) v1 v0))))
    (conj (all (all (impl (applicationF (fsucc (fsucc c)) v1 v0)
        (conj (member v1 (fsucc (fsucc A))) (member v0 v1)))))
      (all (all (all
        (impl (applicationF (fsucc (fsucc (fsucc c))) v2 v1)
          (impl (applicationF (fsucc (fsucc (fsucc c))) v2 v0) (equal v1 v0))))))).
Definition choiceFunctionF {n} (A c : Fin n) : Formula n :=
  conj (choiceLawsF A c) (graphF c).
Definition choice {n} : Formula n :=
  all (impl (all (impl (member v0 v1) (ex (member v0 v1))))
    (ex (choiceFunctionF v1 v0))).

Lemma graphF_correct {n} (r : Fin n -> Ens) c :
  holds (graphF c) r <-> forall e, IN e (r c) -> exists x y, EQ e (Couple x y).
Proof.
  unfold graphF; cbn [holds]. setoid_rewrite ordered_pairF_correct; reflexivity.
Qed.
Lemma choiceLawsF_correct {n} (r : Fin n -> Ens) A c :
  holds (choiceLawsF A c) r <-> function_laws (r A) (fun x => x) (r c).
Proof.
  unfold choiceLawsF, function_laws; cbn [holds].
  setoid_rewrite applicationF_correct; reflexivity.
Qed.

Theorem choiceFunctionF_correct {n} (r : Fin n -> Ens) A c :
  holds (choiceFunctionF A c) r <-> IN (r c) (dependent_product (r A) (fun x => x)).
Proof.
  unfold choiceFunctionF; cbn [holds]. rewrite choiceLawsF_correct, graphF_correct.
  split.
  - intros [HL HG]. unfold dependent_product; apply IN_P_Comp.
    + intros x y HX E; eapply function_laws_extensional; eassumption.
    + apply INC_IN_Power; intros e He.
      destruct (HG e He) as [x [y E]].
      assert (Hxy : application (r c) x y) by (eapply IN_sound_left; eassumption).
      destruct (proj1 (proj2 HL) x y Hxy) as [Hx Hy].
      eapply IN_sound_left; [apply EQ_sym; exact E |].
      apply Couple_IN_Prod; [exact Hx |].
      eapply IN_Union; [| exact Hy].
      destruct (IN_EXType _ _ Hx) as [i Ei]. exists i; exact Ei.
    + exact HL.
  - intro HC; split; [apply dependent_product_elimination; exact HC |].
    intros e He. destruct (dependent_product_pair _ _ _ _ HC He) as [x [y [E _]]].
    exists x, y; apply EQ_sym; exact E.
Qed.

(** Exact equivalence with the EXISTING explicit ordinary-choice principle.
    This does not postulate Choice or assume any PTS soundness conclusion. *)
Theorem choice_statement_correct {n} (r : Fin n -> Ens) : holds choice r <-> family_choice.
Proof.
  unfold choice; cbn [holds]. setoid_rewrite choiceFunctionF_correct; reflexivity.
Qed.
Theorem choice_satisfied (AC : family_choice) {n} (r : Fin n -> Ens) : holds choice r.
Proof. apply choice_statement_correct; exact AC. Qed.

Inductive BZC : Theory :=
| bzc_zermelo n p : BoundedZermelo n p -> BZC n p
| bzc_choice n : BZC n choice.

Theorem bzc_satisfied (classical_logic : forall P : Prop, P \/ ~ P)
  (AC : family_choice) : theory_holds BZC.
Proof.
  intros n p H r; destruct H.
  - apply bounded_zermelo_satisfied; assumption.
  - apply choice_satisfied; exact AC.
Qed.
Corollary bzc_logical_soundness (classical_logic : forall P : Prop, P \/ ~ P)
  (AC : family_choice) n G p :
  derives BZC n G p -> forall r, context_holds G r -> holds p r.
Proof.
  apply logical_soundness; [exact classical_logic | apply bzc_satisfied; assumption].
Qed.

Print Assumptions extensionality_satisfied.
Print Assumptions empty_set_satisfied.
Print Assumptions pairing_satisfied.
Print Assumptions union_satisfied.
Print Assumptions powerset_satisfied.
Print Assumptions infinity_satisfied.
Print Assumptions membership_accessible.
Print Assumptions foundation_satisfied.
Print Assumptions bounded_zermelo_satisfied.
Print Assumptions bounded_zermelo_logical_soundness.
Print Assumptions choiceFunctionF_correct.
Print Assumptions choice_statement_correct.
Print Assumptions choice_satisfied.
Print Assumptions bzc_satisfied.
Print Assumptions bzc_logical_soundness.
Check bounded_zermelo_satisfied.
Check bzc_satisfied.
Check bzc_logical_soundness.
End MaterialZermelo.
