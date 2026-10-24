(** The traversal compiler is independent of comparison's Boolean result.
    It covers every raw tree pair, including malformed/rejected certificates.
    The fixed internal comparator executes that traversal; it is not a bare
    C -> C -> Bool function with internally generated traversal evidence. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia Bool.Bool.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRStructural DirectRCheck.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  GuardedTables InternalCodeComparison CheckerComparisons InternalComparisonFolds.
Import ListNotations.

Module CodeComparisonRealization.
Import CommonCodes DirectRKernel.Core Structural.
Module IC := InternalCarrier.InternalCarrier.
Module BT := GuardedTables.GuardedTables.
Module CC := InternalCodeComparison.InternalCodeComparison.
Module NC := CheckerComparisons.CheckerComparisons.
Module F := InternalComparisonFolds.InternalComparisonFolds.

Definition v1 {n} : Term nat (S (S n)) := var (fsucc fzero).
Definition v2 {n} : Term nat (S (S (S n))) := var (fsucc (fsucc fzero)).
Definition v3 {n} : Term nat (S (S (S (S n)))) := var (fsucc (fsucc (fsucc fzero))).

Ltac comparison_substitution H :=
  unfold CC.zip_at, CC.pair_at, V0, v1, v2, v3 in H;
  structural_substitution_in H.

Lemma atom_zip_application t y : Typed ε y IC.carrier ->
  Typed ε (app (CC.atom_zip t) y) (CC.zip_at (IC.atom t) y).
Proof.
  intro Hy; pose proof (CC.atom_zip_typed t) as H.
  change (Typed ε (CC.atom_zip t)
    (Π IC.carrier (CC.zip_at (lift_closed (IC.atom t)) V0))) in H.
  pose proof (tApp H Hy) as J; comparison_substitution J.
  unfold CC.zip_at; rewrite lift_closed_zero; exact J.
Qed.
Lemma pair_atom_zip_application t a b : Typed ε a IC.carrier -> Typed ε b IC.carrier ->
  Typed ε (app (app (CC.pair_atom_zip t) a) b)
    (CC.zip_at (CC.pair_at a b) (IC.atom t)).
Proof.
  intros Ha Hb; pose proof (CC.pair_atom_zip_typed t) as H.
  change (Typed ε (CC.pair_atom_zip t) (Π IC.carrier (Π (lift_closed IC.carrier)
    (CC.zip_at (CC.pair_at v1 V0) (lift_closed (IC.atom t)))))) in H.
  pose proof (tApp H Ha) as H1; comparison_substitution H1.
  pose proof (tApp H1 Hb) as H2; comparison_substitution H2.
  unfold CC.zip_at, CC.pair_at; rewrite !lift_closed_zero; exact H2.
Qed.
Lemma pair_pair_zip_application a b c d gac gbd :
  Typed ε a IC.carrier -> Typed ε b IC.carrier ->
  Typed ε c IC.carrier -> Typed ε d IC.carrier ->
  Typed ε gac (CC.zip_at a c) -> Typed ε gbd (CC.zip_at b d) ->
  Typed ε (app (app (app (app (app (app CC.pair_pair_zip a) b) c) d) gac) gbd)
    (CC.zip_at (CC.pair_at a b) (CC.pair_at c d)).
Proof.
  intros Ha Hb Hc Hd Hac Hbd; pose proof CC.pair_pair_zip_typed as H.
  change (Typed ε CC.pair_pair_zip (Π IC.carrier (Π (lift_closed IC.carrier)
    (Π (lift_closed IC.carrier) (Π (lift_closed IC.carrier)
      (Arrow (CC.zip_at v3 v1) (Arrow (CC.zip_at v2 V0)
        (CC.zip_at (CC.pair_at v3 v2) (CC.pair_at v1 V0))))))))) in H.
  pose proof (tApp H Ha) as H1; comparison_substitution H1.
  pose proof (tApp H1 Hb) as H2; comparison_substitution H2.
  pose proof (tApp H2 Hc) as H3; comparison_substitution H3.
  pose proof (tApp H3 Hd) as H4; comparison_substitution H4.
  unfold CC.zip_at, CC.pair_at in *; rewrite !lift_closed_zero in *.
  eapply arrow_application; [eapply arrow_application; [exact H4 |exact Hac] |exact Hbd].
Qed.

Lemma compare_application x y g : Typed ε x IC.carrier -> Typed ε y IC.carrier ->
  Typed ε g (CC.zip_at x y) ->
  Typed ε (app (app (app CC.compare x) y) g) BT.boolean.
Proof.
  intros Hx Hy Hg; pose proof CC.compare_typed as H.
  change (Typed ε CC.compare (Π IC.carrier (Π (lift_closed IC.carrier)
    (Arrow (CC.zip_at v1 V0) (lift_closed BT.boolean))))) in H.
  pose proof (tApp H Hx) as H1; comparison_substitution H1.
  pose proof (tApp H1 Hy) as H2; comparison_substitution H2.
  eapply arrow_application; [exact H2 |exact Hg].
Qed.

Fixpoint quote_zip (x y : code) : closed_term :=
  match x, y with
  | Atom t, y => app (CC.atom_zip t) (IC.quote y)
  | Pair a b, Atom t => app (app (CC.pair_atom_zip t) (IC.quote a)) (IC.quote b)
  | Pair a b, Pair c d =>
      app (app (app (app (app (app CC.pair_pair_zip (IC.quote a)) (IC.quote b))
        (IC.quote c)) (IC.quote d)) (quote_zip a c)) (quote_zip b d)
  end.
Theorem quote_zip_typed x y :
  Typed ε (quote_zip x y) (CC.zip_at (IC.quote x) (IC.quote y)).
Proof.
  revert y; induction x as [t|a IHa b IHb]; intros y.
  - apply atom_zip_application, IC.quote_typed.
  - destruct y as [t|c d]; cbn [quote_zip IC.quote].
    + change (Typed ε (quote_zip (Pair a b) (Atom t))
        (CC.zip_at (CC.pair_at (IC.quote a) (IC.quote b)) (IC.atom t))).
      apply pair_atom_zip_application; apply IC.quote_typed.
    + change (Typed ε (quote_zip (Pair a b) (Pair c d))
        (CC.zip_at (CC.pair_at (IC.quote a) (IC.quote b))
        (CC.pair_at (IC.quote c) (IC.quote d)))).
      apply pair_pair_zip_application; auto using IC.quote_typed.
Qed.

Definition comparison x y :=
  app (app (app CC.compare (IC.quote x)) (IC.quote y)) (quote_zip x y).
Theorem comparison_typed x y : Typed ε (comparison x y) BT.boolean.
Proof. apply compare_application; auto using IC.quote_typed, quote_zip_typed. Qed.

Ltac comparison_equation H :=
  unfold CC.compare_at, CC.conjunction_at, CC.pair_at,
    CC.v0, CC.v1, CC.v2, CC.v3, CC.v4, CC.v5 in H;
  structural_substitution_in H.

Lemma is_atom_pair_beta t (a b : closed_term) :
  app (CC.is_atom t) (app (app IC.pair a) b) =ᵝ BT.point false.
Proof.
  pose proof (replace_equiv
    (fin_match b (fin_match a (fun i : Fin 0 => match i with end)))
    _ _ (CC.is_atom_pair_schema t)) as H.
  comparison_equation H; exact H.
Qed.
Lemma compare_atom_beta t (y : closed_term) :
  app (app (app CC.compare (IC.atom t)) y) (app (CC.atom_zip t) y)
    =ᵝ app (CC.is_atom t) y.
Proof.
  pose proof (replace_equiv (fin_match y (fun i : Fin 0 => match i with end))
    _ _ (CC.compare_atom_schema t)) as H.
  comparison_equation H; exact H.
Qed.
Lemma compare_pair_atom_beta t (a b : closed_term) :
  app (app (app CC.compare (app (app IC.pair a) b)) (IC.atom t))
    (app (app (CC.pair_atom_zip t) a) b) =ᵝ BT.point false.
Proof.
  pose proof (replace_equiv
    (fin_match b (fin_match a (fun i : Fin 0 => match i with end)))
    _ _ (CC.compare_pair_atom_schema t)) as H.
  comparison_equation H; exact H.
Qed.
Lemma compare_pair_pair_beta (a b c d gac gbd : closed_term) :
  app (app (app CC.compare (app (app IC.pair a) b)) (app (app IC.pair c) d))
    (app (app (app (app (app (app CC.pair_pair_zip a) b) c) d) gac) gbd) =ᵝ
  app (app CC.conjunction (app (app (app CC.compare a) c) gac))
    (app (app (app CC.compare b) d) gbd).
Proof.
  pose proof (replace_equiv
    (fin_match gbd (fin_match gac (fin_match d (fin_match c (fin_match b
      (fin_match a (fun i : Fin 0 => match i with end)))))))
    _ _ CC.compare_pair_pair_schema) as H.
  comparison_equation H; exact H.
Qed.

Theorem comparison_beta x y : comparison x y =ᵝ BT.point (NC.code_eqb x y).
Proof.
  revert y; induction x as [t|a IHa b IHb]; intro y.
  - unfold comparison; cbn [quote_zip IC.quote].
    transitivity (app (CC.is_atom t) (IC.quote y)); [apply compare_atom_beta |].
    destruct y as [u|c d]; cbn [IC.quote NC.code_eqb].
    + apply CC.is_atom_atom_beta.
    + apply is_atom_pair_beta.
  - destruct y as [t|c d].
    + apply compare_pair_atom_beta.
    + unfold comparison at 1; cbn [quote_zip IC.quote NC.code_eqb].
      transitivity (app (app CC.conjunction (comparison a c)) (comparison b d)).
      * apply compare_pair_pair_beta.
      * transitivity (app (app CC.conjunction (BT.point (NC.code_eqb a c)))
          (BT.point (NC.code_eqb b d))).
        -- apply beta_app; [apply beta_app; [reflexivity |apply IHa] |apply IHb].
        -- exact (CC.conjunction_beta (NC.code_eqb a c) (NC.code_eqb b d)).
Qed.

Theorem boolean_equiv_injective b c : BT.point b =ᵝ BT.point c -> b = c.
Proof. apply F.point_equiv_injective. Qed.
Theorem comparison_output_exact x y b :
  comparison x y =ᵝ BT.point b <-> NC.code_eqb x y = b.
Proof.
  split.
  - intro H; apply boolean_equiv_injective.
    transitivity (comparison x y); [symmetry; apply comparison_beta |exact H].
  - intro H; rewrite <- H; apply comparison_beta.
Qed.
Theorem comparison_true_exact x y : comparison x y =ᵝ BT.point true <-> x = y.
Proof. rewrite comparison_output_exact, NC.code_eqb_correct; reflexivity. Qed.
Theorem comparison_false_exact x y : comparison x y =ᵝ BT.point false <-> x <> y.
Proof. rewrite comparison_output_exact, NC.code_eqb_false; reflexivity. Qed.
Theorem term_comparison_beta {n} (t u : Term nat n) :
  comparison (encode_term t) (encode_term u) =ᵝ
    BT.point (NativeProofCodes.NativeProofCodes.term_eqb t u).
Proof. rewrite <- NC.code_eqb_encoded_terms; apply comparison_beta. Qed.

(** This counts traversal constructors, not emitted PTS syntax or running time. *)
Fixpoint traversal_nodes (x y : code) : nat :=
  match x, y with
  | Pair a b, Pair c d => S (traversal_nodes a c + traversal_nodes b d)
  | _, _ => 1
  end.
Theorem traversal_nodes_bounded x y :
  traversal_nodes x y <= Nat.min (code_size x) (code_size y).
Proof.
  revert y; induction x as [t|a IHa b IHb]; intros y; destruct y as [u|c d];
    cbn [traversal_nodes code_size]; try lia.
  specialize (IHa c); specialize (IHb d); lia.
Qed.

End CodeComparisonRealization.
