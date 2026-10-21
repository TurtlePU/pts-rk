From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Ranks
  Reduction AbstractRewriting DefEq.
From PTSrk.NormalizationComplexity Require Import Rank.
Import Context ListNotations RankEstimate.

(** Independent computational source evidence for the FULL original PTS.
    No quote, target typing, normalization result, or conversion oracle is
    a field of these datatypes. In particular, lambda annotations and
    reduction within annotations are retained literally. *)
Module FullSource.

Inductive step_data : forall n, Term nat n -> Term nat n -> Type :=
| s_pi_left {n A A'} (B : Term nat (S n)) :
    step_data n A A' -> step_data n (Π A B) (Π A' B)
| s_pi_right {n} (A : Term nat n) {B B'} :
    step_data (S n) B B' -> step_data n (Π A B) (Π A B')
| s_lam_left {n A A'} (t : Term nat (S n)) :
    step_data n A A' -> step_data n (lam A t) (lam A' t)
| s_lam_right {n} (A : Term nat n) {t t'} :
    step_data (S n) t t' -> step_data n (lam A t) (lam A t')
| s_app_left {n f f'} (u : Term nat n) :
    step_data n f f' -> step_data n (app f u) (app f' u)
| s_app_right {n} (f : Term nat n) {u u'} :
    step_data n u u' -> step_data n (app f u) (app f u')
| s_beta {n} (A : Term nat n) (t : Term nat (S n)) (u : Term nat n) :
    step_data n (app (lam A t) u) (subst t u).

Theorem step_sound n t u : step_data n t u -> step nat n t u.
Proof. intro d; induction d; constructor; assumption. Qed.

(** Completeness remains in Prop. It does NOT extract executable data
    from an opaque Prop proof. A supplied Type-valued witness is executable. *)
Theorem step_complete n t u : step nat n t u -> inhabited (step_data n t u).
Proof.
  intro H; induction H; try destruct IHstep as [d]; constructor;
    constructor; assumption.
Qed.

Theorem step_iff n t u : inhabited (step_data n t u) <-> step nat n t u.
Proof. split; [intros [d]; exact (step_sound n t u d) | apply step_complete]. Qed.

Inductive reduction (n : nat) : Term nat n -> Term nat n -> Type :=
| r_refl t : reduction n t t
| r_cons {t u v} : step_data n t u -> reduction n u v -> reduction n t v.
Arguments r_refl {n} _.
Arguments r_cons {n t u v} _ _.

Fixpoint reduction_append {n t u} (d : reduction n t u)
    {v} (e : reduction n u v) : reduction n t v :=
  match d in reduction _ t' u' return
      forall v, reduction n u' v -> reduction n t' v with
  | r_refl _ => fun _ e => e
  | r_cons p q => fun _ e => r_cons p (reduction_append q e)
  end v e.

Fixpoint reduction_map {m n} (f : Term nat m -> Term nat n)
    (map_step : forall t u, step_data m t u -> step_data n (f t) (f u))
    {t u} (d : reduction m t u) : reduction n (f t) (f u) :=
  match d with
  | r_refl _ => r_refl _
  | r_cons p q => r_cons (map_step _ _ p) (reduction_map f map_step q)
  end.

Definition reduction_pi {n A A' B B'} (d : reduction n A A')
    (e : reduction (S n) B B') : reduction n (Π A B) (Π A' B') :=
  reduction_append
    (reduction_map (fun X => Π X B) (fun _ _ p => s_pi_left B p) d)
    (reduction_map (fun Y => Π A' Y) (fun _ _ p => s_pi_right A' p) e).

Definition reduction_lam {n A A' t t'} (d : reduction n A A')
    (e : reduction (S n) t t') : reduction n (lam A t) (lam A' t') :=
  reduction_append
    (reduction_map (fun X => lam X t) (fun _ _ p => s_lam_left t p) d)
    (reduction_map (fun y => lam A' y) (fun _ _ p => s_lam_right A' p) e).

Definition reduction_app {n f f' u u'} (d : reduction n f f')
    (e : reduction n u u') : reduction n (app f u) (app f' u') :=
  reduction_append
    (reduction_map (fun x => app x u) (fun _ _ p => s_app_left u p) d)
    (reduction_map (fun y => app f' y) (fun _ _ p => s_app_right f' p) e).

Theorem reduction_sound n t u : reduction n t u -> reduces_to nat n t u.
Proof.
  intro d; induction d; [reflexivity |].
  eapply rtc_step; [apply step_sound; eassumption | exact IHd].
Qed.

Theorem reduction_complete n t u :
  reduces_to nat n t u -> inhabited (reduction n t u).
Proof.
  intro H; induction H; [constructor; constructor |].
  destruct (step_complete _ _ _ H) as [p], IHRTC as [q].
  constructor; exact (r_cons p q).
Qed.

Theorem reduction_iff n t u :
  inhabited (reduction n t u) <-> reduces_to nat n t u.
Proof. split; [intros [d]; exact (reduction_sound n t u d) | apply reduction_complete]. Qed.

(** Finite symmetric paths. Their intermediate terms need not be typed:
    this mirrors ORIGINAL unrestricted beta conversion exactly. *)
Inductive conversion (n : nat) : Term nat n -> Term nat n -> Type :=
| c_refl t : conversion n t t
| c_forward {t u v} : step_data n t u -> conversion n u v -> conversion n t v
| c_backward {t u v} : step_data n u t -> conversion n u v -> conversion n t v.
Arguments c_refl {n} _.
Arguments c_forward {n t u v} _ _.
Arguments c_backward {n t u v} _ _.

Fixpoint conversion_append {n t u} (d : conversion n t u)
    {v} (e : conversion n u v) : conversion n t v :=
  match d in conversion _ t' u' return
      forall v, conversion n u' v -> conversion n t' v with
  | c_refl _ => fun _ e => e
  | c_forward p q => fun _ e => c_forward p (conversion_append q e)
  | c_backward p q => fun _ e => c_backward p (conversion_append q e)
  end v e.

Fixpoint conversion_reverse {n t u} (d : conversion n t u) : conversion n u t :=
  match d with
  | c_refl _ => c_refl _
  | c_forward p q => conversion_append (conversion_reverse q) (c_backward p (c_refl _))
  | c_backward p q => conversion_append (conversion_reverse q) (c_forward p (c_refl _))
  end.

Fixpoint reduction_conversion {n t u} (d : reduction n t u) : conversion n t u :=
  match d with
  | r_refl _ => c_refl _
  | r_cons p q => c_forward p (reduction_conversion q)
  end.

Theorem conversion_sound n t u : conversion n t u -> def_equiv nat n t u.
Proof.
  intro d; induction d; [reflexivity | |]; eapply rtc_step;
    try exact IHd; [apply forward | apply backwards]; apply step_sound; eassumption.
Qed.

Theorem conversion_complete n t u :
  def_equiv nat n t u -> inhabited (conversion n t u).
Proof.
  intro H; induction H; [constructor; constructor |].
  destruct IHRTC as [q]; destruct H;
    match goal with H : step _ _ _ _ |- _ => destruct (step_complete _ _ _ H) as [p] end;
    constructor; [exact (c_forward p q) | exact (c_backward p q)].
Qed.

Theorem conversion_iff n t u :
  inhabited (conversion n t u) <-> def_equiv nat n t u.
Proof. split; [intros [d]; exact (conversion_sound n t u d) | apply conversion_complete]. Qed.

Inductive derivation : forall n, Ctx nat n -> Term nat n -> Term nat n -> Type :=
| d_sort {n} (G : Ctx nat n) r : derivation n G (𝓤 r) (𝓤 0)
| d_pi {n G A B} a b :
    derivation n G A (𝓤 a) -> derivation (S n) (G & A) B (𝓤 b) ->
    derivation n G (Π A B) (𝓤 (Nat.max (S a) b))
| d_var {n} (G : Ctx nat n) i : derivation n G (var i) (G !! i)
| d_lam {n G A t B} a :
    derivation n G A (𝓤 a) -> derivation (S n) (G & A) t B ->
    derivation n G (lam A t) (Π A B)
| d_app {n G f u A B} :
    derivation n G f (Π A B) -> derivation n G u A ->
    derivation n G (app f u) (subst B u)
| d_conv {n G t A B} b :
    derivation n G t A -> derivation n G B (𝓤 b) -> conversion n A B ->
    derivation n G t B.

Theorem derivation_sound n G t T : derivation n G t T -> @typ nat RankSorts n G t T.
Proof.
  intro d; induction d.
  - constructor; reflexivity.
  - eapply typ_Π; [exact IHd1 | exact IHd2 | reflexivity].
  - constructor.
  - eapply typ_λ; eassumption.
  - eapply typ_app; eassumption.
  - eapply typ_conv; [exact IHd1 | exact IHd2 | apply conversion_sound; exact c].
Qed.

Theorem derivation_complete n G t T :
  @typ nat RankSorts n G t T -> inhabited (derivation n G t T).
Proof.
  intro H; induction H.
  - cbn in H; subst; constructor; constructor.
  - cbn in H1; subst. destruct IHtyp1 as [d], IHtyp2 as [e].
    constructor; exact (d_pi _ _ d e).
  - constructor; constructor.
  - destruct IHtyp1 as [d], IHtyp2 as [e]; constructor; exact (d_lam _ d e).
  - destruct IHtyp1 as [d], IHtyp2 as [e]; constructor; exact (d_app d e).
  - destruct IHtyp1 as [d], IHtyp2 as [e], (conversion_complete _ _ _ H1) as [p].
    constructor; exact (d_conv _ d e p).
Qed.

Theorem derivation_iff n G t T :
  inhabited (derivation n G t T) <-> @typ nat RankSorts n G t T.
Proof. split; [intros [d]; exact (derivation_sound n G t T d) | apply derivation_complete]. Qed.

(** Finite traversals of SUPPLIED data, not an extraction of a derivation
    from Prop and not a proved budget for an unconstructed target quoter. *)
Fixpoint reduction_length {n t u} (d : reduction n t u) : nat :=
  match d with r_refl _ => 0 | r_cons _ q => S (reduction_length q) end.

Fixpoint conversion_length {n t u} (d : conversion n t u) : nat :=
  match d with
  | c_refl _ => 0
  | c_forward _ q | c_backward _ q => S (conversion_length q)
  end.

Fixpoint conversion_terms {n t u} (d : conversion n t u) : list (Term nat n) :=
  match d with
  | c_refl v => [v]
  | @c_forward _ v _ _ _ q | @c_backward _ v _ _ _ q => v :: conversion_terms q
  end.

Theorem conversion_terms_length n t u (d : conversion n t u) :
  length (conversion_terms d) = S (conversion_length d).
Proof. induction d; cbn; congruence. Qed.

Fixpoint context_literal {n} (G : Ctx nat n) : nat :=
  match G with ε => 0 | D & A => Nat.max (context_literal D) (maxRankLiteral A) end.

Definition judgment_literals {n} (G : Ctx nat n) (t T : Term nat n) :=
  [context_literal G; maxRankLiteral t; maxRankLiteral T].

(** Literal ceilings of ALL judgment contexts/terms/types, plus every
    intermediate whole term in every conversion path. maxRankLiteral
    traverses products and lambda annotations as well as term bodies. *)
Fixpoint literal_indices {n G t T} (d : derivation n G t T) : list nat :=
  judgment_literals G t T ++
  match d with
  | d_sort _ _ | d_var _ _ => []
  | d_pi _ _ p q | d_lam _ p q | d_app p q => literal_indices p ++ literal_indices q
  | d_conv _ p q c => literal_indices p ++ literal_indices q ++
      map (@maxRankLiteral _) (conversion_terms c)
  end.

(** Only the EXPLICIT formation-rank indices carried by source rules:
    product input/output ranks, lambda domain ranks and conversion target
    sorts. This is not a bound on all inferred semantic subterm ranks. *)
Fixpoint rule_indices {n G t T} (d : derivation n G t T) : list nat :=
  match d with
  | d_sort _ _ => [0]
  | d_var _ _ => []
  | d_pi a b p q => [a; b; Nat.max (S a) b] ++ rule_indices p ++ rule_indices q
  | d_lam a p q | d_conv a p q _ => a :: (rule_indices p ++ rule_indices q)
  | d_app p q => rule_indices p ++ rule_indices q
  end.

Fixpoint rule_count {n G t T} (d : derivation n G t T) : nat :=
  match d with
  | d_sort _ _ | d_var _ _ => 1
  | d_pi _ _ p q | d_lam _ p q | d_app p q | d_conv _ p q _ =>
      S (rule_count p + rule_count q)
  end.

Fixpoint conversion_count {n G t T} (d : derivation n G t T) : nat :=
  match d with
  | d_sort _ _ | d_var _ _ => 0
  | d_pi _ _ p q | d_lam _ p q | d_app p q => conversion_count p + conversion_count q
  | d_conv _ p q c => conversion_count p + conversion_count q + conversion_length c
  end.

Definition ceiling := fold_right Nat.max 0.
Definition source_budget {n G t T} (d : derivation n G t T) :=
  ceiling (literal_indices d ++ rule_indices d).

Lemma ceiling_bounds xs r : In r xs -> r <= ceiling xs.
Proof.
  induction xs as [|x xs IH]; cbn [In ceiling fold_right]; [contradiction |].
  intros [-> | H]; [lia | specialize (IH H); lia].
Qed.

Lemma judgment_literals_in n G t T (d : derivation n G t T) r :
  In r (judgment_literals G t T) -> In r (literal_indices d).
Proof. destruct d; cbn [literal_indices]; intro H; apply in_or_app; auto. Qed.

Theorem source_budget_bounds n G t T (d : derivation n G t T) :
  (forall r, In r (literal_indices d) -> r <= source_budget d) /\
  (forall r, In r (rule_indices d) -> r <= source_budget d).
Proof.
  split; intros r Hr; apply ceiling_bounds, in_or_app; auto.
Qed.

Theorem source_judgment_bounds n G t T (d : derivation n G t T) :
  context_literal G <= source_budget d /\
  maxRankLiteral t <= source_budget d /\ maxRankLiteral T <= source_budget d.
Proof.
  repeat split; apply (proj1 (source_budget_bounds n G t T d)), judgment_literals_in;
    cbn [judgment_literals In]; auto.
Qed.

Theorem source_sort_bound n G t r (d : derivation n G t (𝓤 r)) :
  r <= source_budget d.
Proof. exact (proj2 (proj2 (source_judgment_bounds n G t (𝓤 r) d))). Qed.

Theorem source_conversion_bound n G t A B b
    (p : derivation n G t A) (q : derivation n G B (𝓤 b))
    (c : conversion n A B) v :
  In v (conversion_terms c) -> maxRankLiteral v <= source_budget (d_conv b p q c).
Proof.
  intro H; apply (proj1 (source_budget_bounds _ _ _ _ (d_conv b p q c))).
  cbn [literal_indices]. apply in_or_app; right.
  apply in_or_app; right. apply in_or_app; right.
  apply in_map; exact H.
Qed.

Theorem source_rule_count_positive n G t T (d : derivation n G t T) :
  0 < rule_count d.
Proof. destruct d; cbn [rule_count]; lia. Qed.

(** Full original coverage, as a Prop existence statement. It neither
    computes evidence from opaque typing nor proves that this numerical
    ceiling suffices for global target quotation/coherence. *)
Theorem every_original_derivation_has_finite_data n G t T :
  @typ nat RankSorts n G t T ->
  exists d : derivation n G t T,
    (forall r, In r (literal_indices d) -> r <= source_budget d) /\
    (forall r, In r (rule_indices d) -> r <= source_budget d).
Proof.
  intro H; destruct (derivation_complete n G t T H) as [d].
  exists d; apply source_budget_bounds.
Qed.

Print Assumptions step_iff.
Print Assumptions reduction_iff.
Print Assumptions conversion_iff.
Print Assumptions derivation_iff.
Print Assumptions conversion_terms_length.
Print Assumptions source_budget_bounds.
Print Assumptions source_judgment_bounds.
Print Assumptions source_sort_bound.
Print Assumptions source_conversion_bound.
Print Assumptions source_rule_count_positive.
Print Assumptions every_original_derivation_has_finite_data.
End FullSource.
