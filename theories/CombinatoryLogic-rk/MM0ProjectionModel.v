From Stdlib Require Import Lists.List Bool.Bool.
From Stdlib Require Vectors.Vector.
From PTSrk.Combinatory Require Import MM0FiniteSignature MM0FiniteAxioms MM0FiniteSearch.
Import ListNotations.

(** A fixed total model for selected quantified MM0 subtheories that omit
    sveq and f0.  These omissions are substantive: without f0 the form/ax
    predicates can be empty.  Thus this construction does NOT realize the
    positive Hilbert catalogue or prove full native PTS soundness.  Every
    retained universal axiom and the Void denial are satisfied at EVERY
    semantic valuation, on one fixed carrier per sort. *)
Module MM0ProjectionModel.
Import MM0FiniteSignature MM0FiniteAxioms MM0FiniteSearch.

Definition retained (a : AxiomName) : bool :=
  match a with A_sveq | A_f0 => false | _ => true end.
Definition projection_fragment := filter retained all_axioms.

Theorem projection_fragment_size : length projection_fragment = 53.
Proof. reflexivity. Qed.

Lemma projection_fragment_retained :
  Forall (fun a => retained a = true) projection_fragment.
Proof.
  vm_compute; repeat constructor.
Qed.

Section ProjectionModel.
Context {D : Type}.
Variables universe variable : D.
Hypothesis distinct : variable <> universe.

Definition projection_algebra : Algebra D :=
  fun o => match o return Vector.t D (arity o) -> D with
  | OZ | ONil => fun _ => universe
  | OS => fun xs => Vector.hd xs
  | OU => fun _ => universe
  | OV => fun _ => variable
  | OApp => fun xs => Vector.hd xs
  | OPi | OLam => fun xs => Vector.hd (Vector.tl xs)
  | OCons => fun xs => Vector.hd (Vector.tl (Vector.tl xs))
  end.

Definition projection_truth (a : GroundAtom D) : Prop :=
  match a with
  | (PLe, _) | (PLt, _) | (PMax, _) | (PStel, _) | (PPrefix, _) => True
  | (PLift, [_; M; N]) | (PSub, [_; _; M; N]) | (PRed, [M; N]) => M = N
  | (PH, [_; A]) => A = universe
  | _ => False
  end.

Lemma retained_rule_sound a :
  retained a = true ->
  forall env : Vector.t D (length (variables (axiom_rule a))),
  Forall (fun atom => projection_truth
    (evaluate_atom universe projection_algebra (Vector.to_list env) atom))
    (premises (axiom_rule a)) ->
  projection_truth (evaluate_atom universe projection_algebra (Vector.to_list env)
    (conclusion (axiom_rule a))).
Proof.
  destruct a; cbn [retained]; try discriminate; intros _ env H;
    cbn in *;
    repeat match goal with
    | H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H
    end;
    cbn in *; intuition congruence.
Qed.

Theorem projection_model names :
  Forall (fun a => retained a = true) names ->
  Model universe projection_algebra (selected_rules names) [void_denial] projection_truth.
Proof.
  intro Hnames; split.
  - intros r Hr env HP; apply in_map_iff in Hr; destruct Hr as [a [<- Ha]].
    apply retained_rule_sound; [|exact HP].
    rewrite Forall_forall in Hnames; now apply Hnames.
  - intros r Hr env HP; destruct Hr as [<- | []].
    inversion HP; subst; cbn in *; contradiction.
Qed.

Theorem full_projection_fragment_model :
  Model universe projection_algebra (selected_rules projection_fragment) [void_denial] projection_truth.
Proof.
  exact (projection_model projection_fragment projection_fragment_retained).
Qed.

Theorem projection_void_empty t :
  ~ projection_truth (PH, [t; evaluate universe projection_algebra [] (EPi (EU EZ) (EV EZ))]).
Proof. cbn; exact distinct. Qed.

Theorem projection_universe_inhabited :
  projection_truth (PH, [universe; universe]).
Proof. reflexivity. Qed.

(** Application has a genuinely enabled semantic instance.  The model does
    not satisfy all typing implications merely by making h empty. *)
Theorem projection_application_enabled :
  Forall (fun atom => projection_truth
    (evaluate_atom universe projection_algebra
      [universe; universe; universe; universe; universe] atom))
    (premises (axiom_rule A_h_apply)) /\
  projection_truth (evaluate_atom universe projection_algebra
    [universe; universe; universe; universe; universe]
    (conclusion (axiom_rule A_h_apply))).
Proof. split; [repeat constructor | reflexivity]. Qed.

Theorem projection_rejects_sveq :
  ~ PositiveSatisfaction universe projection_algebra [axiom_rule A_sveq] projection_truth.
Proof.
  intro H.
  specialize (H _ (or_introl eq_refl)
    (Vector.cons D universe 1 (Vector.cons D universe 0 (Vector.nil D))) (Forall_nil _)).
  cbn in H; exact (distinct H).
Qed.

Theorem projection_rejects_f0 :
  ~ PositiveSatisfaction universe projection_algebra [axiom_rule A_f0] projection_truth.
Proof.
  intro H.
  specialize (H _ (or_introl eq_refl)
    (Vector.cons D universe 1 (Vector.cons D universe 0 (Vector.nil D))) (Forall_nil _)).
  exact H.
Qed.
End ProjectionModel.

Definition boolean_domain : list bool := [false; true].
Lemma boolean_domain_complete x : In x boolean_domain.
Proof. destruct x; cbn; auto. Qed.

Theorem selected_projection_search_succeeds names :
  Forall (fun a => retained a = true) names ->
  exists table, find_model false boolean_domain Bool.bool_dec names = Some table.
Proof.
  intro H; apply (fixed_domain_search_exact false boolean_domain Bool.bool_dec
    boolean_domain_complete names).
  exists (projection_algebra false true), (projection_truth false).
  apply projection_model; [discriminate | exact H].
Qed.

Theorem fifty_three_quantified_axioms_have_fixed_two_element_model :
  exists algebra truth,
    Model false algebra (selected_rules projection_fragment) [void_denial] truth.
Proof.
  exists (projection_algebra false true), (projection_truth false).
  apply full_projection_fragment_model; discriminate.
Qed.

Print Assumptions projection_fragment_size.
Print Assumptions retained_rule_sound.
Print Assumptions projection_model.
Print Assumptions full_projection_fragment_model.
Print Assumptions projection_void_empty.
Print Assumptions projection_universe_inhabited.
Print Assumptions projection_application_enabled.
Print Assumptions projection_rejects_sveq.
Print Assumptions projection_rejects_f0.
Print Assumptions selected_projection_search_succeeds.
Print Assumptions fifty_three_quantified_axioms_have_fixed_two_element_model.
End MM0ProjectionModel.
