(** Finite-fragment normalization for the unchanged independent certificates.
    The finite carrier contains raw annotated syntax, not proof objects and
    not an ungraded finite model of all native operations.  Both rank and
    carrier are computed from the subject; their soundness follows from
    acceptance, never from a native typing field in the input certificate.

    The final rejection equations are external Rocq theorems.  They provide
    verified entries for finite internal checker tables, not a single internal
    PTS theorem quantifying over all represented certificates or budgets. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks Reduction Preservation.
From PTSrk.NormalizationComplexity Require Import Greedy Bounds RedexRanks
  AutomaticBound Normalization.
From PTSrk.Combinatory Require Import QuantitativeNormalization FiniteNormalForms
  NativeCanonicity.
From PTSrk.SelfConsistency Require Import NativeProofCodes CertificateAdequacy
  StructuralCodes CertificateSerialization.

Module FiniteFragmentNormalization.
Import NativeProofCodes.NativeProofCodes FiniteNormalForms.FiniteNormalForms.
Import ListNotations.

(** Every state of this path belongs to the stated finite list. *)
Inductive CarrierSteps {n} (carrier : list (Term nat n)) :
  Term nat n -> Term nat n -> Prop :=
| carrier_refl t : In t carrier -> CarrierSteps carrier t t
| carrier_step t u v : In t carrier -> step nat n t u ->
    CarrierSteps carrier u v -> CarrierSteps carrier t v.

Lemma bounded_steps_carrier {n} limit alphabet (t u : Term nat n) :
  BoundedSteps limit t u -> Uses alphabet t ->
  CarrierSteps (sizedTerms limit n alphabet) t u.
Proof.
  intro H; induction H; intro HA.
  - constructor. apply sizedTerms_iff; auto.
  - eapply carrier_step; [apply sizedTerms_iff; auto | exact H0 |].
    apply IHBoundedSteps. eapply uses_step; eassumption.
Qed.

Lemma carrier_steps_sound {n} carrier (t u : Term nat n) :
  CarrierSteps carrier t u -> reduces_to nat n t u.
Proof.
  intro H; induction H; [constructor |].
  eapply AbstractRewriting.rtc_step; eassumption.
Qed.

Definition fragment_rank (p : Certificate 0) := conservativeRank (subject p).
Definition fragment_peak (p : Certificate 0) :=
  tower (fragment_rank p) (nodes (subject p)).
Definition fragment_carrier (p : Certificate 0) :=
  sizedTerms (fragment_peak p) 0 (labels (subject p)).
Definition fragment_normal_forms (p : Certificate 0) :=
  normalForms (fragment_peak p) (labels (subject p)).
Definition certificate_normal_form (p : Certificate 0) :=
  rounds (fragment_rank p) (subject p).

Theorem certificate_rank_sound (p : Certificate 0) :
  check ε p = true -> RedexBound ε (subject p) (fragment_rank p).
Proof.
  intro H; unfold fragment_rank. eapply conservative_rank_sound.
  apply certificate_sound; exact H.
Qed.

Theorem certificate_bounded_normalization (p : Certificate 0) :
  check ε p = true ->
  BoundedSteps (fragment_peak p) (subject p) (certificate_normal_form p) /\
  normalb (certificate_normal_form p) = true /\
  @typ nat RankSorts 0 ε (certificate_normal_form p) (type p).
Proof.
  intro H.
  destruct (fixed_rank_peak_normalization (fragment_rank p) ε (subject p)
    (type p) (@wf_empty nat RankSorts) (certificate_sound p ε H)
    (certificate_rank_sound p H)) as [HP [HN [HT _]]].
  repeat split; assumption.
Qed.

Theorem certificate_finite_normalization (p : Certificate 0) :
  check ε p = true ->
  CarrierSteps (fragment_carrier p) (subject p) (certificate_normal_form p) /\
  normalb (certificate_normal_form p) = true /\
  @typ nat RankSorts 0 ε (certificate_normal_form p) (type p) /\
  In (certificate_normal_form p) (fragment_normal_forms p).
Proof.
  intro H; destruct (certificate_bounded_normalization p H) as [HP [HN HT]].
  repeat split; try assumption.
  - apply bounded_steps_carrier; [exact HP | apply uses_self].
  - apply normalizer_in_finite_carrier with (A := type p).
    + apply certificate_sound; exact H.
    + apply certificate_rank_sound; exact H.
Qed.

(** The whole syntax carrier has an elementary cardinality bound at its
    computed rank.  This does not bound the certificate or its equality tree. *)
Theorem fragment_carrier_capacity (p : Certificate 0) :
  length (fragment_carrier p) <=
    tower (fragment_rank p + 2) (4 * nodes (subject p) + 4).
Proof. apply finite_syntax_elementary, label_count. Qed.

Theorem fragment_normal_forms_capacity (p : Certificate 0) :
  length (fragment_normal_forms p) <=
    tower (fragment_rank p + 2) (4 * nodes (subject p) + 4).
Proof. apply finite_carrier_elementary, label_count. Qed.

(** Unlike the preceding per-input carrier, this one is shared by EVERY
    accepted certificate meeting the same syntactic bounds.  No native
    typing or semantic redex-bound witness is an input premise.  The size
    and label bounds here concern subjects; finite checker enumeration must
    separately bound the complete serialized certificate. *)
Theorem bounded_fragment_normalization (p : Certificate 0) d N alphabet :
  check ε p = true -> fragment_rank p <= d -> nodes (subject p) <= N ->
  Uses alphabet (subject p) ->
  CarrierSteps (sizedTerms (tower d N) 0 alphabet)
    (subject p) (rounds d (subject p)) /\
  normalb (rounds d (subject p)) = true /\
  @typ nat RankSorts 0 ε (rounds d (subject p)) (type p) /\
  In (rounds d (subject p)) (normalForms (tower d N) alphabet).
Proof.
  intros HC HR HS HA.
  assert (HB : RedexBound ε (subject p) d).
  { eapply redex_bound_monotone; [apply certificate_rank_sound; exact HC | exact HR]. }
  destruct (fixed_rank_peak_normalization d ε (subject p) (type p)
    (@wf_empty nat RankSorts) (certificate_sound p ε HC) HB)
    as [HP [HN [HT [HNsize _]]]].
  assert (Hsize : nodes (rounds d (subject p)) <= tower d N).
  { eapply Nat.le_trans; [exact HNsize | apply tower_monotone; exact HS]. }
  repeat split; try assumption.
  - apply bounded_steps_carrier; [|exact HA].
    eapply bounded_steps_weaken; [exact HP | apply tower_monotone; exact HS].
  - apply normalForms_iff; repeat split; try assumption.
    eapply uses_reduction; [apply rounds_sound | exact HA].
Qed.

Theorem bounded_fragment_capacity d N alphabet : length alphabet <= N ->
  length (sizedTerms (tower d N) 0 alphabet) <= tower (d + 2) (4 * N + 4).
Proof. apply finite_syntax_elementary. Qed.

(** A common envelope is computed from an arbitrary finite list, without
    filtering by acceptance.  Rejected but scoped certificates contribute to
    the same bounds.  Malformed raw trees are omitted only by the decoder. *)
Definition family_rank (ps : list (Certificate 0)) :=
  fold_right (fun p d => Nat.max (fragment_rank p) d) 0 ps.
Definition family_nodes (ps : list (Certificate 0)) :=
  fold_right (fun p N => Nat.max (nodes (subject p)) N) 0 ps.
Definition family_alphabet (ps : list (Certificate 0)) :=
  flat_map (fun p => labels (subject p)) ps.
Definition family_seed ps := Nat.max (family_nodes ps) (length (family_alphabet ps)).

Lemma member_fold_bound {A} (f : A -> nat) xs x : In x xs ->
  f x <= fold_right (fun y N => Nat.max (f y) N) 0 xs.
Proof.
  induction xs as [|y ys IH]; cbn; [contradiction |].
  intros [<- | H]; [apply Nat.le_max_l |].
  eapply Nat.le_trans; [apply IH; exact H | apply Nat.le_max_r].
Qed.

Theorem certificate_family_bounds ps p : In p ps ->
  fragment_rank p <= family_rank ps /\ nodes (subject p) <= family_seed ps /\
  Uses (family_alphabet ps) (subject p).
Proof.
  intro H; split.
  - apply member_fold_bound; exact H.
  - split.
    + unfold family_seed. eapply Nat.le_trans; [|apply Nat.le_max_l].
      exact (member_fold_bound (fun q : Certificate 0 => nodes (subject q)) ps p H).
    + intros r Hr; apply in_flat_map. exists p; auto.
Qed.

Theorem certificate_family_normalization ps p : In p ps -> check ε p = true ->
  CarrierSteps (sizedTerms (tower (family_rank ps) (family_seed ps)) 0
    (family_alphabet ps)) (subject p) (rounds (family_rank ps) (subject p)) /\
  normalb (rounds (family_rank ps) (subject p)) = true /\
  @typ nat RankSorts 0 ε (rounds (family_rank ps) (subject p)) (type p) /\
  In (rounds (family_rank ps) (subject p))
    (normalForms (tower (family_rank ps) (family_seed ps)) (family_alphabet ps)).
Proof.
  intros HM HC; destruct (certificate_family_bounds ps p HM) as [HR [HS HA]].
  apply bounded_fragment_normalization; assumption.
Qed.

Theorem certificate_family_capacity ps :
  length (sizedTerms (tower (family_rank ps) (family_seed ps)) 0 (family_alphabet ps)) <=
    tower (family_rank ps + 2) (4 * family_seed ps + 4).
Proof. apply bounded_fragment_capacity; unfold family_seed; apply Nat.le_max_r. Qed.

Definition decoded_certificates (qs : list code) : list (Certificate 0) :=
  flat_map (fun q => match decode_certificate q 0 with
    | Some p => [p] | None => [] end) qs.

Theorem decoded_certificates_spec qs p : In p (decoded_certificates qs) <->
  exists q, In q qs /\ decode_certificate q 0 = Some p.
Proof.
  unfold decoded_certificates; rewrite in_flat_map; split.
  - intros [q [HQ HP]]; exists q; split; [exact HQ |].
    destruct (decode_certificate q 0) as [p'|] eqn:HD; cbn in HP;
      [destruct HP as [<- | []]; reflexivity | contradiction].
  - intros [q [HQ HD]]; exists q; split; [exact HQ |].
    rewrite HD; cbn; auto.
Qed.

(** This interface applies to arbitrary decoded accepted certificates,
    including non-Bottom judgments.  Thus the finite normalization package
    is not obtained by elimination of the impossible Bottom case. *)
Theorem raw_accepted_finite_normalization q (p : Certificate 0) :
  decode_certificate q 0 = Some p -> check ε p = true ->
  q = encode_certificate p /\
  CarrierSteps (fragment_carrier p) (subject p) (certificate_normal_form p) /\
  normalb (certificate_normal_form p) = true /\
  @typ nat RankSorts 0 ε (certificate_normal_form p) (type p) /\
  In (certificate_normal_form p) (fragment_normal_forms p).
Proof.
  intros HD HC; split.
  - symmetry; exact (certificate_decode_encode q 0 p HD).
  - apply certificate_finite_normalization; exact HC.
Qed.

Theorem certificate_bottom_rejected (p : Certificate 0) :
  accepts_bottom p = false.
Proof.
  destruct (accepts_bottom p) eqn:H; [|reflexivity].
  unfold accepts_bottom in H; apply andb_true_iff in H as [HC HE].
  apply term_eqb_correct in HE.
  destruct (certificate_bounded_normalization p HC) as [_ [HN HT]].
  rewrite HE in HT. exfalso.
  apply (NativeCanonicity.normal_void_empty (certificate_normal_form p)).
  - exact (normalb_sound _ HN).
  - exact HT.
Qed.

(** Malformed inputs are covered too: raw_bottom_sound includes the actual
    decoder, all six native rules and every supplied raw conversion step. *)
Theorem raw_bottom_rejected q : raw_bottom_check q = false.
Proof.
  unfold raw_bottom_check; destruct (decode_certificate q 0) as [p|].
  - apply certificate_bottom_rejected.
  - reflexivity.
Qed.

Print Assumptions certificate_rank_sound.
Print Assumptions certificate_bounded_normalization.
Print Assumptions certificate_finite_normalization.
Print Assumptions fragment_carrier_capacity.
Print Assumptions fragment_normal_forms_capacity.
Print Assumptions bounded_fragment_normalization.
Print Assumptions bounded_fragment_capacity.
Print Assumptions certificate_family_bounds.
Print Assumptions certificate_family_normalization.
Print Assumptions certificate_family_capacity.
Print Assumptions decoded_certificates_spec.
Print Assumptions raw_accepted_finite_normalization.
Print Assumptions certificate_bottom_rejected.
Print Assumptions raw_bottom_rejected.
End FiniteFragmentNormalization.
