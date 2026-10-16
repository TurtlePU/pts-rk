(** The complete existing decoder, represented by bounded separation.
    The branch specifications below exclude mismatched tags, for arbitrary
    set inputs, before the three branches are combined. No native range of
    decoded values is collected to construct the graph. *)
From ZFC Require Import Sets Axioms Cartesian.
From PTSrk Require Import Syntax.
From PTSrkModel Require Import SetFunctions SetApplication CodeUniverses
  CountableCodes CardinalHierarchy HierarchyBounds SuppliedHierarchy GlobalCodeChoice
  BoundedFormulas BoundedGraphs BoundedCodeArithmetic BoundedFiniteCarriers
  BoundedIteration BoundedInfiniteDecoder BoundedUniverses BoundedSortDecoder.
Import Bounded CodeUniverses.CodeUniverses.

Theorem omega_codes_all_codes : EQ omega_codes all_codes.
Proof.
  apply INC_EQ.
  - intros x Hx. apply all_codes_member, omega_has_code; exact Hx.
  - intros x Hx. apply all_codes_member in Hx as [c E].
    apply omega_membership. exists (key c); exact E.
Qed.

Theorem bounded_finite_decoder_spec x y :
  application bounded_finite_decoder x y <->
  exists n, EQ x (repr (finite n)) /\ EQ y (finite_carrier n).
Proof.
  split.
  - intro HF. unfold bounded_finite_decoder in HF.
    apply bounded_formula_graph_spec in HF as [_ [_ HP]].
    unfold finite_decode_certificate in HP. cbn [holds] in HP.
    setoid_rewrite application_correct in HP.
    cbn [finite_decode_parameters fin_match] in HP.
    destruct HP as [q [Hq [HT HC]]].
    apply omega_membership in Hq as [n E]. exists n; split.
    + apply numeral_tripling_application.
      eapply application_arguments; [apply EQ_refl | exact E | apply EQ_refl | exact HT].
    + apply finite_carrier_graph_application.
      eapply application_arguments; [apply EQ_refl | exact E | apply EQ_refl | exact HC].
  - intros [n [Ex Ey]].
    eapply application_arguments; [apply EQ_refl | apply EQ_sym; exact Ex | apply EQ_refl |].
    apply bounded_finite_decoder_application; exact Ey.
Qed.

Section Decoding.
Variables W H : Ens.
Hypothesis HW : transitive_set W.
Hypothesis HO : INC omega_codes W.
Hypothesis HH : tower_envelope W H.

Theorem bounded_infinite_decoder_spec x y :
  application (bounded_infinite_decoder H) x y <->
  exists n, EQ x (repr (infinite n)) /\ EQ y (carrier n).
Proof.
  split.
  - intro HF. unfold bounded_infinite_decoder in HF.
    apply bounded_formula_graph_spec in HF as [_ [_ HP]].
    unfold infinite_decode_certificate in HP. cbn [holds] in HP.
    setoid_rewrite application_correct in HP. setoid_rewrite singleton_correct in HP.
    cbn [infinite_decode_parameters fin_match] in HP.
    destruct HP as [q [Hq [z [Hz [HT [ES HC]]]]]].
    apply omega_membership in Hq as [n E]. exists n; split.
    + eapply EQ_tran; [exact ES | apply Sing_sound].
      apply numeral_tripling_application.
      eapply application_arguments; [apply EQ_refl | exact E | apply EQ_refl | exact HT].
    + apply (bounded_carrier_graph_application W H HW HO HH n y).
      eapply application_arguments; [apply EQ_refl | exact E | apply EQ_refl | exact HC].
  - intros [n [Ex Ey]].
    eapply application_arguments; [apply EQ_refl | apply EQ_sym; exact Ex | apply EQ_refl |].
    apply (bounded_infinite_decoder_application W H HW HO HH n y); exact Ey.
Qed.

Theorem bounded_sort_decoder_spec x y :
  application bounded_sort_decoder x y <->
  exists n, EQ x (repr (sort n)) /\ EQ y (U n).
Proof.
  split.
  - intro HF. unfold bounded_sort_decoder in HF.
    apply bounded_formula_graph_spec in HF as [_ [_ HP]].
    unfold sort_decode_certificate in HP. cbn [holds] in HP.
    setoid_rewrite application_correct in HP. setoid_rewrite singleton_correct in HP.
    cbn [eq_rect sort_decode_parameters fin_match] in HP.
    destruct HP as [q [Hq [z [Hz [t [Ht [HT [ET [ES HU]]]]]]]]].
    apply omega_membership in Hq as [n E]. exists n; split.
    + eapply EQ_tran; [exact ES | apply Sing_sound].
      eapply EQ_tran; [exact ET | apply Sing_sound].
      apply numeral_tripling_application.
      eapply application_arguments; [apply EQ_refl | exact E | apply EQ_refl | exact HT].
    + apply bounded_universe_graph_application.
      eapply application_arguments; [apply EQ_refl | exact E | apply EQ_refl | exact HU].
  - intros [n [Ex Ey]].
    eapply application_arguments; [apply EQ_refl | apply EQ_sym; exact Ex | apply EQ_refl |].
    apply bounded_sort_decoder_application; exact Ey.
Qed.

(** Environment: output, code, finite graph, infinite graph, sort graph. *)
Definition decoder_certificate : Formula 5 :=
  disj (applicationF (fsucc (fsucc fzero)) (fsucc fzero) fzero)
    (disj (applicationF (fsucc (fsucc (fsucc fzero))) (fsucc fzero) fzero)
      (applicationF (fsucc (fsucc (fsucc (fsucc fzero)))) (fsucc fzero) fzero)).
Definition decoder_parameters := fin_match bounded_finite_decoder
  (fin_match (bounded_infinite_decoder H)
    (fin_match bounded_sort_decoder (fun i : Fin 0 => match i with end))).
Definition bounded_decoder := bounded_formula_graph decoder_certificate
  decoder_parameters omega_codes H.

Lemma decoder_at_code x c : EQ x (repr c) -> EQ (decode x) (code_value carrier c).
Proof.
  intro E. eapply EQ_tran; [apply decoding_extensional; exact E | apply decode_repr].
Qed.

Theorem decoder_certificate_correct x y : IN x omega_codes ->
  (holds decoder_certificate (fin_match y (fin_match x decoder_parameters)) <->
   EQ y (decode x)).
Proof.
  intro Hx. unfold decoder_certificate. cbn [holds].
  setoid_rewrite application_correct. cbn [decoder_parameters fin_match].
  rewrite bounded_finite_decoder_spec, bounded_infinite_decoder_spec, bounded_sort_decoder_spec.
  split.
  - intros [[n [Ex Ey]] | [[n [Ex Ey]] | [n [Ex Ey]]]].
    + eapply EQ_tran; [exact Ey | apply EQ_sym; exact (decoder_at_code x (finite n) Ex)].
    + eapply EQ_tran; [exact Ey | apply EQ_sym; exact (decoder_at_code x (infinite n) Ex)].
    + eapply EQ_tran; [exact Ey | apply EQ_sym; exact (decoder_at_code x (sort n) Ex)].
  - intro E. destruct (omega_has_code x Hx) as [[n|n|n] Ex].
    + left. exists n; split; [exact Ex |].
      eapply EQ_tran; [exact E | exact (decoder_at_code x (finite n) Ex)].
    + right; left. exists n; split; [exact Ex |].
      eapply EQ_tran; [exact E | exact (decoder_at_code x (infinite n) Ex)].
    + right; right. exists n; split; [exact Ex |].
      eapply EQ_tran; [exact E | exact (decoder_at_code x (sort n) Ex)].
Qed.

Lemma decoder_value_bound x : IN x omega_codes -> IN (decode x) H.
Proof.
  intro Hx. destruct (all_codes_in_some_universe x
    (IN_sound_right x omega_codes all_codes omega_codes_all_codes Hx)) as [i Hi].
  exact (envelope_decode W H i x HO HH Hi).
Qed.

Theorem bounded_decoder_application x y :
  application bounded_decoder x y <-> IN x omega_codes /\ EQ y (decode x).
Proof.
  unfold bounded_decoder. rewrite bounded_formula_graph_spec. split.
  - intros [Hx [Hy HC]]. split; [exact Hx |].
    apply (proj1 (decoder_certificate_correct x y Hx)); exact HC.
  - intros [Hx E]. split; [exact Hx |]. split.
    + exact (IN_sound_left (decode x) y H (EQ_sym _ _ E) (decoder_value_bound x Hx)).
    + apply (proj2 (decoder_certificate_correct x y Hx)); exact E.
Qed.

Theorem bounded_decoder_typed :
  IN bounded_decoder (dependent_product omega_codes (fun _ => H)).
Proof.
  apply bounded_formula_graph_typed.
  - intros x Hx. exists (decode x). split; [apply decoder_value_bound; exact Hx |].
    apply (proj2 (decoder_certificate_correct x (decode x) Hx)), EQ_refl.
  - intros x y z Hx Hy Hz HC HD.
    apply (proj1 (decoder_certificate_correct x y Hx)) in HC.
    apply (proj1 (decoder_certificate_correct x z Hx)) in HD.
    eapply EQ_tran; [exact HC | apply EQ_sym; exact HD].
Qed.

Theorem bounded_decoder_beta x : IN x omega_codes ->
  EQ (apply_set bounded_decoder x) (decode x).
Proof.
  intro Hx. apply apply_set_value.
  - apply bounded_decoder_application; split; [exact Hx | apply EQ_refl].
  - intros y Hy. apply bounded_decoder_application in Hy; tauto.
Qed.

Theorem bounded_decoder_graph_agrees : EQ bounded_decoder all_decoding_graph.
Proof.
  assert (E : EQ bounded_decoder (graph omega_codes decode)).
  { apply bounded_formula_graph_agrees.
    - intros x y Exy; apply decoding_extensional; exact Exy.
    - apply decoder_value_bound.
    - intros x y Hx Hy; apply decoder_certificate_correct; exact Hx. }
  eapply EQ_tran; [exact E |]. apply INC_EQ.
  - intros e [i EE].
    apply (IN_sound_left (Couple (pi2 omega_codes i) (decode (pi2 omega_codes i))) e _
      (EQ_sym _ _ EE)).
    apply graph_beta; [intros x y Exy; apply decoding_extensional; exact Exy |].
    exact (IN_sound_right _ _ _ omega_codes_all_codes (index_member omega_codes i)).
  - intros e [i EE].
    apply (IN_sound_left (Couple (pi2 all_codes i) (decode (pi2 all_codes i))) e _
      (EQ_sym _ _ EE)).
    apply graph_beta; [intros x y Exy; apply decoding_extensional; exact Exy |].
    exact (IN_sound_right _ _ _ (EQ_sym _ _ omega_codes_all_codes) (index_member all_codes i)).
Qed.
End Decoding.

Print Assumptions omega_codes_all_codes.
Print Assumptions bounded_finite_decoder_spec.
Print Assumptions bounded_infinite_decoder_spec.
Print Assumptions bounded_sort_decoder_spec.
Print Assumptions decoder_certificate_correct.
Print Assumptions bounded_decoder_application.
Print Assumptions bounded_decoder_typed.
Print Assumptions bounded_decoder_beta.
Print Assumptions bounded_decoder_graph_agrees.
Check bounded_decoder_graph_agrees.
