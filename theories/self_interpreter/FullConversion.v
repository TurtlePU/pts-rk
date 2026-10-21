From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation
  Ranks Reduction AbstractRewriting DefEq.
From PTSrk.NormalizationComplexity Require Import Greedy.
From PTSrk.SelfInterpreter Require Import FullSource OpenCanonical.
Import Context.

(** Executable METALEVEL forward certificates for the full original source.
    An arbitrary conversion path can pass through untyped terms. Instead,
    compute both normalization traces from their originally typed endpoints.
    No Prop proof is eliminated to obtain a reduction constructor. *)
Module FullConversion.
Module FS := FullSource.FullSource.
Module OC := OpenCanonical.OpenCanonical.

Fixpoint greedy_trace {n} (t : Term nat n) : FS.reduction n t (greedy t).
Proof.
  induction t; cbn [greedy].
  - apply FS.r_refl.
  - apply FS.reduction_pi; assumption.
  - apply FS.r_refl.
  - apply FS.reduction_lam; assumption.
  - refine (@FS.reduction_append n _ (app (greedy t1) (greedy t2)) _ _ _).
    + apply FS.reduction_app; assumption.
    + destruct (greedy t1); try apply FS.r_refl.
      eapply FS.r_cons; [apply FS.s_beta | apply FS.r_refl].
Defined.

Fixpoint rounds_trace {n} (fuel : nat) (t : Term nat n) :
    FS.reduction n t (rounds fuel t) :=
  match fuel with
  | 0 => FS.r_refl t
  | S fuel' => FS.reduction_append (greedy_trace t) (rounds_trace fuel' (greedy t))
  end.

Definition normalization_trace {n} (G : Ctx nat n) (t : Term nat n) :
    FS.reduction n t (OC.nf G t) := rounds_trace (OC.budget G t) t.

Fixpoint trace_length {n t u} (p : FS.reduction n t u) : nat :=
  match p with FS.r_refl _ => 0 | FS.r_cons _ q => S (trace_length q) end.

Fixpoint trace_typed {n t u} (G : Ctx nat n) (T : Term nat n)
    (p : FS.reduction n t u) : Prop :=
  match p in FS.reduction _ t' _ return Prop with
  | FS.r_refl x => @typ nat RankSorts n G x T
  | @FS.r_cons _ x _ _ _ q => @typ nat RankSorts n G x T /\ trace_typed G T q
  end.

Theorem every_forward_stage_typed n G t u T (p : FS.reduction n t u) :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T -> trace_typed G T p.
Proof.
  intros HG Ht; induction p; cbn [trace_typed]; [exact Ht |].
  split; [exact Ht |]. apply IHp. eapply subject_reduction;
    [exact Ht | exact HG | apply FS.step_sound; eassumption].
Qed.

Theorem normalization_trace_correct n G t T :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  trace_typed G T (normalization_trace G t) /\ normalb (OC.nf G t) = true /\
  @typ nat RankSorts n G (OC.nf G t) T.
Proof.
  intros HG Ht; split; [apply every_forward_stage_typed; assumption |].
  split; [eapply OC.nf_normal | eapply OC.nf_typed]; eassumption.
Qed.

(** Structural equality is an actual decision, not a postulated oracle. *)
Fixpoint fin_eq_dec {n} (i : Fin n) : forall j : Fin n, {i=j}+{i<>j}.
Proof.
  induction i; intro j; dependent elimination j as [fzero | fsucc j].
  - left; reflexivity.
  - right; discriminate.
  - right; discriminate.
  - destruct (IHi j) as [E | H]; [left; now subst | right].
    intro E; apply H.
    exact (f_equal (fun x => fin_match i (fun y => y) x) E).
Defined.

Fixpoint term_eq_dec {n} (t : Term nat n) : forall u : Term nat n, {t=u}+{t<>u}.
Proof.
  induction t; intro u; destruct u as [r | u1 u2 | j | u1 u2 | u1 u2];
    try (right; discriminate).
  - destruct (Nat.eq_dec l r) as [E | H]; [left; now subst | right].
    intro E; inversion E; contradiction.
  - destruct (IHt1 u1) as [E1 | H1], (IHt2 u2) as [E2 | H2];
      try (left; now subst); right; intro E; injection E; intros; contradiction.
  - destruct (fin_eq_dec f j) as [E | H]; [left; now subst | right].
    intro E; injection E; contradiction.
  - destruct (IHt1 u1) as [E1 | H1], (IHt2 u2) as [E2 | H2];
      try (left; now subst); right; intro E; injection E; intros; contradiction.
  - destruct (IHt1 u1) as [E1 | H1], (IHt2 u2) as [E2 | H2];
      try (left; now subst); right; intro E; injection E; intros; contradiction.
Defined.

Record joining n (t u : Term nat n) := {
  middle : Term nat n;
  left_trace : FS.reduction n t middle;
  right_trace : FS.reduction n u middle
}.
Arguments middle {n t u} _.
Arguments left_trace {n t u} _.
Arguments right_trace {n t u} _.

Definition make_join {n} (G : Ctx nat n) t u (E : OC.nf G t = OC.nf G u)
    : joining n t u :=
  {| middle := OC.nf G t;
     left_trace := normalization_trace G t;
     right_trace := eq_rect (OC.nf G u) (FS.reduction n u)
       (normalization_trace G u) (OC.nf G t) (eq_sym E) |}.

(** Total on RAW syntax. Success gives valid reduction paths even on raw
    inputs; completeness and normality require original well-typed inputs. *)
Definition join_attempt {n} (G : Ctx nat n) (t u : Term nat n) : option (joining n t u) :=
  match term_eq_dec (OC.nf G t) (OC.nf G u) with
  | left E => Some (make_join G t u E)
  | right _ => None
  end.

Definition convertibleb {n} (G : Ctx nat n) (t u : Term nat n) : bool :=
  match join_attempt G t u with Some _ => true | None => false end.

Theorem joining_sound n t u (j : joining n t u) : def_equiv nat n t u.
Proof.
  apply def_equiv_prop; exists (middle j); split;
    apply FS.reduction_sound; [apply left_trace | apply right_trace].
Qed.

Theorem joining_typed n G t u T U (j : joining n t u) :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T -> @typ nat RankSorts n G u U ->
  trace_typed G T (left_trace j) /\ trace_typed G U (right_trace j).
Proof. intros; split; apply every_forward_stage_typed; assumption. Qed.

Theorem join_attempt_normal n G t u T j :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  join_attempt G t u = Some j -> normalb (middle j) = true.
Proof.
  intros HG Ht; unfold join_attempt; destruct (term_eq_dec (OC.nf G t) (OC.nf G u));
    intro H; inversion H; subst; cbn [make_join middle]; eapply OC.nf_normal; eassumption.
Qed.

Theorem join_attempt_complete n G t u T U :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T -> @typ nat RankSorts n G u U ->
  def_equiv nat n t u -> exists j, join_attempt G t u = Some j.
Proof.
  intros HG Ht Hu HE. unfold join_attempt.
  destruct (term_eq_dec (OC.nf G t) (OC.nf G u)) as [E | H]; [eexists; reflexivity |].
  exfalso; apply H. apply (proj2 (OC.nf_conversion_iff n G G t u T U HG HG Ht Hu)); exact HE.
Qed.

Theorem convertibleb_correct n G t u T U :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T -> @typ nat RankSorts n G u U ->
  (convertibleb G t u = true <-> def_equiv nat n t u).
Proof.
  intros HG Ht Hu; split.
  - unfold convertibleb. destruct (join_attempt G t u) as [j |];
      [intro; apply (joining_sound n t u j) | discriminate].
  - intro H; destruct (join_attempt_complete n G t u T U HG Ht Hu H) as [j Hj].
    unfold convertibleb; now rewrite Hj.
Qed.

Theorem supplied_conversion_certified n G t u T U
    (dt : FS.derivation n G t T) (du : FS.derivation n G u U)
    (e : FS.conversion n t u) :
  @wf nat RankSorts n G ->
  exists j, join_attempt G t u = Some j /\ normalb (middle j) = true /\
    trace_typed G T (left_trace j) /\ trace_typed G U (right_trace j).
Proof.
  intro HG. pose proof (FS.derivation_sound n G t T dt) as Ht.
  pose proof (FS.derivation_sound n G u U du) as Hu.
  destruct (join_attempt_complete n G t u T U HG Ht Hu
    (FS.conversion_sound n t u e)) as [j Hj].
  exists j; split; [exact Hj |]. split.
  - eapply join_attempt_normal; eassumption.
  - apply joining_typed; assumption.
Qed.

(** These computations include an actual beta contraction and retain the
    original annotation. They are regressions, not the coverage proof. *)
Definition beta_example : Term nat 0 := app (lam (𝓤 0) (var fzero)) (𝓤 0).
Example beta_trace_computes : trace_length (normalization_trace ε beta_example) = 1.
Proof. vm_compute; reflexivity. Qed.
Example beta_comparison_computes : convertibleb ε beta_example (𝓤 0) = true.
Proof. vm_compute; reflexivity. Qed.
Example distinct_sorts_compute : convertibleb ε (𝓤 0) (𝓤 1) = false.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions greedy_trace.
Print Assumptions rounds_trace.
Print Assumptions every_forward_stage_typed.
Print Assumptions normalization_trace_correct.
Print Assumptions fin_eq_dec.
Print Assumptions term_eq_dec.
Print Assumptions joining_sound.
Print Assumptions joining_typed.
Print Assumptions join_attempt_normal.
Print Assumptions join_attempt_complete.
Print Assumptions convertibleb_correct.
Print Assumptions supplied_conversion_certified.
Print Assumptions beta_trace_computes.
Print Assumptions beta_comparison_computes.
Print Assumptions distinct_sorts_compute.
End FullConversion.
