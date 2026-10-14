(** Least closed relation, with all candidate relations bounded by a
    supplied powerset. This avoids using a native indexed sup as the
    definition of the carrier graph. Ens semantics is not a BZC derivation. *)
From ZFC Require Import Sets Axioms Cartesian.
From PTSrk Require Import Syntax.
From PTSrkModel Require Import SetFunctions SetApplication CodeUniverses
  CountableCodes CardinalHierarchy HierarchyBounds SuppliedHierarchy
  BoundedFormulas BoundedGraphs BoundedPowersets.
Import Bounded CodeUniverses.CodeUniverses.

Definition up4 {n} (i : Fin n) := fsucc (fsucc (fsucc (fsucc i))).
Definition iterationClosedF {n} (R O H P z b : Fin n) :=
  conj (applicationF R z b)
    (all O (all (fsucc H) (all (fsucc (fsucc O))
      (all (fsucc (fsucc (fsucc H)))
        (impl (conj (applicationF (up4 R) (fsucc (fsucc (fsucc fzero)))
                    (fsucc (fsucc fzero)))
          (conj (singletonF (fsucc fzero) (fsucc (fsucc (fsucc fzero))))
            (applicationF (up4 P) (fsucc (fsucc fzero)) fzero)))
          (applicationF (up4 R) (fsucc fzero) fzero)))))).

Definition iteration_closed R O H P z b :=
  application R z b /\ forall i x j y,
  IN i O -> IN x H -> IN j O -> IN y H ->
  application R i x -> EQ j (Sing i) -> application P x y -> application R j y.

Lemma iteration_closed_formula_correct {n} (r : Fin n -> Ens) R O H P z b :
  holds (iterationClosedF R O H P z b) r <->
  iteration_closed (r R) (r O) (r H) (r P) (r z) (r b).
Proof.
  unfold iterationClosedF, iteration_closed. cbn [holds].
  setoid_rewrite application_correct. setoid_rewrite singleton_correct.
  cbn [fin_match up4]. split.
  - intros [HB HC]. split; [exact HB |]. intros i x j y Hi Hx Hj Hy HR ES HP.
    apply (HC i Hi x Hx j Hj y Hy); auto.
  - intros [HB HC]. split; [exact HB |]. intros i Hi x Hx j Hj y Hy [HR [ES HP]].
    exact (HC i x j y Hi Hx Hj Hy HR ES HP).
Qed.

Definition iterationValueF {n} (Q O H P z b i y : Fin n) :=
  all Q (impl (iterationClosedF fzero (fsucc O) (fsucc H) (fsucc P)
    (fsucc z) (fsucc b)) (applicationF fzero (fsucc i) (fsucc y))).

Lemma iteration_value_formula_correct {n} (r : Fin n -> Ens) Q O H P z b i y :
  holds (iterationValueF Q O H P z b i y) r <->
  forall R, IN R (r Q) ->
    iteration_closed R (r O) (r H) (r P) (r z) (r b) -> application R (r i) (r y).
Proof.
  unfold iterationValueF. cbn [holds].
  setoid_rewrite iteration_closed_formula_correct.
  setoid_rewrite application_correct. reflexivity.
Qed.

Definition carrier_relation := sup nat (fun n => Couple (numeral n) (carrier n)).
Lemma carrier_relation_application i y : application carrier_relation i y <->
  exists n, EQ i (numeral n) /\ EQ y (carrier n).
Proof.
  split.
  - intros [n E]. exists n. split; [eapply Couple_inj_left | eapply Couple_inj_right]; exact E.
  - intros [n [Ei Ey]]. exists n.
    eapply EQ_tran; [apply Couple_sound_left; exact Ei | apply Couple_sound_right; exact Ey].
Qed.

(** Environment: output, index, omega, H, power graph, zero, base,
    powerset of omega x H. *)
Definition carrier_iteration_certificate : Formula 8 :=
  iterationValueF
    (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))
    (fsucc (fsucc fzero)) (fsucc (fsucc (fsucc fzero)))
    (fsucc (fsucc (fsucc (fsucc fzero))))
    (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))
    (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))
    (fsucc fzero) fzero.
Definition carrier_iteration_parameters H :=
  fin_match omega_codes (fin_match H (fin_match (bounded_powerset_graph H)
    (fin_match (numeral 0) (fin_match omega_codes
      (fin_match (Power (Prod omega_codes H)) (fun i : Fin 0 => match i with end)))))).
Definition bounded_carrier_graph H := bounded_formula_graph
  carrier_iteration_certificate (carrier_iteration_parameters H) omega_codes H.

(** Finite separating relations. Each successor is one bounded separation;
    no set collecting the sequence of separating relations is constructed. *)
Definition slice_filter_certificate : Formula 5 :=
  conj (applicationF (fsucc (fsucc fzero)) (fsucc fzero) fzero)
    (impl (equal (fsucc fzero) (fsucc (fsucc (fsucc fzero))))
      (equal fzero (fsucc (fsucc (fsucc (fsucc fzero)))))).
Definition slice_filter_parameters (R k v : Ens) :=
  fin_match R (fin_match k (fin_match v (fun i : Fin 0 => match i with end))).
Definition slice_filter H R k v := bounded_formula_graph
  slice_filter_certificate (slice_filter_parameters R k v) omega_codes H.

Lemma slice_filter_application H R k v i y :
  application (slice_filter H R k v) i y <->
  IN i omega_codes /\ IN y H /\ application R i y /\ (EQ i k -> EQ y v).
Proof.
  unfold slice_filter. rewrite bounded_formula_graph_spec.
  unfold slice_filter_certificate. cbn [holds]. rewrite application_correct.
  reflexivity.
Qed.

Fixpoint carrier_separator H n : Ens :=
  match n with
  | 0 => slice_filter H (Prod omega_codes H) (numeral 0) omega_codes
  | S k => slice_filter H (carrier_separator H k) (numeral (S k)) (carrier (S k))
  end.

Lemma carrier_separator_bound H n : INC (carrier_separator H n) (Prod omega_codes H).
Proof.
  destruct n; unfold carrier_separator, slice_filter, bounded_formula_graph;
    apply Comp_INC.
Qed.

Section CarrierIteration.
Variables W H : Ens.
Hypothesis HW : transitive_set W.
Hypothesis HO : INC omega_codes W.
Hypothesis HH : tower_envelope W H.

Lemma carrier_relation_bound : INC carrier_relation (Prod omega_codes H).
Proof.
  intros e [n E]. apply (IN_sound_left (Couple (numeral n) (carrier n)) e _ (EQ_sym _ _ E)).
  apply Couple_IN_Prod; [apply numeral_in_omega | exact (envelope_carrier W H n HO HH)].
Qed.

Lemma carrier_relation_closed : iteration_closed carrier_relation omega_codes H
  (bounded_powerset_graph H) (numeral 0) omega_codes.
Proof.
  split.
  - apply carrier_relation_application. exists 0; split; apply EQ_refl.
  - intros i x j y Hi Hx Hj Hy HR ES HP.
    apply carrier_relation_application in HR as [n [Ei Ex]].
    apply (bounded_powerset_graph_application H (envelope_transitive W H HW HH)
      (fun t Ht => envelope_power_closed W H t HW HH Ht)) in HP as [_ Ey].
    apply carrier_relation_application. exists (S n). split.
    + eapply EQ_tran; [exact ES | apply Sing_sound; exact Ei].
    + eapply EQ_tran; [exact Ey | apply Power_sound; exact Ex].
Qed.

Theorem carrier_relation_least R :
  iteration_closed R omega_codes H (bounded_powerset_graph H) (numeral 0) omega_codes ->
  forall n, application R (numeral n) (carrier n).
Proof.
  intros [HB HC] n. induction n as [|n IH]; [exact HB |].
  eapply HC; [apply numeral_in_omega | exact (envelope_carrier W H n HO HH) |
    apply numeral_in_omega | exact (envelope_carrier W H (S n) HO HH) |
    exact IH | apply EQ_refl |].
  apply (bounded_powerset_graph_application H (envelope_transitive W H HW HH)
    (fun t Ht => envelope_power_closed W H t HW HH Ht)).
  split; [exact (envelope_carrier W H n HO HH) | apply EQ_refl].
Qed.

Theorem carrier_separator_laws n :
  iteration_closed (carrier_separator H n) omega_codes H
    (bounded_powerset_graph H) (numeral 0) omega_codes /\
  forall i y, application (carrier_separator H n) i y ->
    EQ i (numeral n) -> EQ y (carrier n).
Proof.
  induction n as [|n [HC HV]].
  - split.
    + split.
      * apply slice_filter_application. split; [apply numeral_in_omega |].
        split; [exact (envelope_carrier W H 0 HO HH) |]. split.
        -- apply Couple_IN_Prod; [apply numeral_in_omega | exact (envelope_carrier W H 0 HO HH)].
        -- intro E; apply EQ_refl.
      * intros i x j y Hi Hx Hj Hy HR ES HP.
        apply slice_filter_application. split; [exact Hj |]. split; [exact Hy |]. split.
        -- apply Couple_IN_Prod; assumption.
        -- intro E. assert (EV : EQ Vide (Sing i)).
           { eapply EQ_tran; [apply EQ_sym; exact E | exact ES]. }
           destruct (not_EQ_Vide_Sing i EV).
    + intros i y HA E. apply slice_filter_application in HA as [_ [_ [_ HV]]].
      apply HV; exact E.
  - destruct HC as [HB HC]. split.
    + split.
      * apply slice_filter_application. split; [apply numeral_in_omega |].
        split; [exact (envelope_carrier W H 0 HO HH) |]. split; [exact HB |].
        intro E; destruct (not_EQ_Vide_Sing (numeral n) E).
      * intros i x j y Hi Hx Hj Hy HR ES HP.
        apply slice_filter_application in HR as [_ [_ [HR _]]].
        apply slice_filter_application. split; [exact Hj |]. split; [exact Hy |]. split.
        -- exact (HC i x j y Hi Hx Hj Hy HR ES HP).
        -- intro EJ.
           assert (EI : EQ i (numeral n)).
           { apply EQ_Sing_EQ. eapply EQ_tran; [apply EQ_sym; exact ES | exact EJ]. }
           pose proof (HV i x HR EI) as EX.
           apply (bounded_powerset_graph_application H (envelope_transitive W H HW HH)
             (fun t Ht => envelope_power_closed W H t HW HH Ht)) in HP as [_ EY].
           eapply EQ_tran; [exact EY | apply Power_sound; exact EX].
    + intros i y HA E. apply slice_filter_application in HA as [_ [_ [_ HV']]].
      apply HV'; exact E.
Qed.

Theorem carrier_iteration_certificate_correct x n y : EQ x (numeral n) ->
  (holds carrier_iteration_certificate
    (fin_match y (fin_match x (carrier_iteration_parameters H))) <-> EQ y (carrier n)).
Proof.
  intro Ex. unfold carrier_iteration_certificate.
  rewrite iteration_value_formula_correct. cbn [carrier_iteration_parameters fin_match].
  split.
  - intro HC. destruct (carrier_separator_laws n) as [HS HV].
    apply (HV x y); [| exact Ex]. apply HC; [| exact HS].
    apply INC_IN_Power, carrier_separator_bound.
  - intros Ey R HR HC.
    pose proof (carrier_relation_least R HC n) as HA.
    unfold application in *. apply (IN_sound_left (Couple (numeral n) (carrier n))
      (Couple x y) R); [| exact HA].
    eapply EQ_tran; [apply Couple_sound_left; apply EQ_sym; exact Ex |].
    apply Couple_sound_right; apply EQ_sym; exact Ey.
Qed.

Theorem bounded_carrier_graph_application n y :
  application (bounded_carrier_graph H) (numeral n) y <-> EQ y (carrier n).
Proof.
  unfold bounded_carrier_graph. rewrite bounded_formula_graph_spec.
  rewrite (carrier_iteration_certificate_correct _ n y (EQ_refl _)). split.
  - tauto.
  - intro E. split; [apply numeral_in_omega |]. split; [| exact E].
    exact (IN_sound_left (carrier n) y H (EQ_sym _ _ E) (envelope_carrier W H n HO HH)).
Qed.

Theorem bounded_carrier_graph_typed :
  IN (bounded_carrier_graph H) (dependent_product omega_codes (fun _ => H)).
Proof.
  apply bounded_formula_graph_typed.
  - intros x Hx. apply omega_membership in Hx as [n Ex].
    exists (carrier n). split; [exact (envelope_carrier W H n HO HH) |].
    apply (proj2 (carrier_iteration_certificate_correct x n _ Ex)), EQ_refl.
  - intros x y z Hx Hy Hz HY HZ. apply omega_membership in Hx as [n Ex].
    apply (proj1 (carrier_iteration_certificate_correct x n y Ex)) in HY.
    apply (proj1 (carrier_iteration_certificate_correct x n z Ex)) in HZ.
    eapply EQ_tran; [exact HY | apply EQ_sym; exact HZ].
Qed.

Theorem bounded_carrier_graph_beta n :
  EQ (apply_set (bounded_carrier_graph H) (numeral n)) (carrier n).
Proof.
  apply apply_set_value.
  - apply bounded_carrier_graph_application, EQ_refl.
  - intros y Hy. apply bounded_carrier_graph_application; exact Hy.
Qed.

End CarrierIteration.
Print Assumptions iteration_closed_formula_correct.
Print Assumptions iteration_value_formula_correct.
Print Assumptions carrier_relation_closed.
Print Assumptions carrier_relation_least.
Print Assumptions slice_filter_application.
Print Assumptions carrier_separator_laws.
Print Assumptions carrier_iteration_certificate_correct.
Print Assumptions bounded_carrier_graph_application.
Print Assumptions bounded_carrier_graph_typed.
Print Assumptions bounded_carrier_graph_beta.
