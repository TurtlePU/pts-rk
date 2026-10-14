(** Bounded recursion for the existing countable choice sequence. The
    reference sequence is used only to prove agreement, never to collect
    its range in the definition of the new graph. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From ZFC Require Import Sets Axioms Cartesian.
From PTSrk Require Import Syntax.
From PTSrkModel Require Import SetFunctions SetApplication SetBijections
  ProductEmbedding CodeUniverses CountableCodes CountableDichotomy
  BoundedFormulas BoundedApplication BoundedGraphs BoundedRecursion.
Import Bounded CodeUniverses.CodeUniverses.

Definition remainingF {n} (X S R : Fin n) : Formula n :=
  conj (all R (conj (member fzero (fsucc X))
    (impl (member fzero (fsucc S)) falsum)))
    (all X (impl (impl (member fzero (fsucc S)) falsum)
      (member fzero (fsucc R)))).

Lemma remaining_formula_correct {n} (r : Fin n -> Ens) X S R :
  holds (remainingF X S R) r <-> EQ (r R) (remaining (r X) (r S)).
Proof.
  unfold remainingF. cbn [holds fin_match]. split.
  - intros [HL HR]. apply INC_EQ.
    + intros z Hz. apply remaining_spec, HL; exact Hz.
    + intros z Hz. apply remaining_spec in Hz as [HX HS]. exact (HR z HX HS).
  - intro E. split.
    + intros z Hz. apply remaining_spec. exact (IN_sound_right z _ _ E Hz).
    + intros z HX HS. apply (IN_sound_right z _ _ (EQ_sym _ _ E)).
      apply remaining_spec; auto.
Qed.

Definition adjoin S z := Union (Paire S (Sing z)).
Lemma adjoin_spec S z x : IN x (adjoin S z) <-> IN x S \/ EQ x z.
Proof.
  split.
  - intro H. destruct (Union_IN _ _ H) as [Y [HY HX]].
    destruct (Paire_IN _ _ _ HY) as [E | E].
    + left; exact (IN_sound_right x _ _ E HX).
    + right; apply IN_Sing_EQ; exact (IN_sound_right x _ _ E HX).
  - intros [H | E].
    + apply (IN_Union (Paire S (Sing z)) S x); [apply IN_Paire_left | exact H].
    + apply (IN_Union (Paire S (Sing z)) (Sing z) x); [apply IN_Paire_right |].
      exact (IN_sound_left z x _ (EQ_sym _ _ E) (IN_Sing z)).
Qed.

Definition adjoinF {n} (S z Y : Fin n) : Formula n :=
  conj (all Y (disj (member fzero (fsucc S)) (equal fzero (fsucc z))))
    (conj (all S (member fzero (fsucc Y))) (member z Y)).
Lemma adjoin_formula_correct {n} (r : Fin n -> Ens) S z Y :
  holds (adjoinF S z Y) r <-> EQ (r Y) (adjoin (r S) (r z)).
Proof.
  unfold adjoinF. cbn [holds fin_match]. split.
  - intros [HU [HS HZ]]. apply INC_EQ.
    + intros x HX. apply adjoin_spec, HU; exact HX.
    + intros x HX. apply adjoin_spec in HX as [HX | E]; [apply HS; exact HX |].
      exact (IN_sound_left (r z) x _ (EQ_sym _ _ E) HZ).
  - intro E. split.
    + intros x HX. apply adjoin_spec. exact (IN_sound_right x _ _ E HX).
    + split.
      * intros x HX. apply (IN_sound_right x _ _ (EQ_sym _ _ E)), adjoin_spec; auto.
      * apply (IN_sound_right (r z) _ _ (EQ_sym _ _ E)), adjoin_spec.
        right; apply EQ_refl.
Qed.

Definition remainingChoiceF {n} (X c PX V S y : Fin n) : Formula n :=
  ex PX (conj (remainingF (fsucc X) (fsucc S) fzero)
    (applyValueF (fsucc V) (fsucc c) fzero (fsucc y))).

Lemma remaining_choice_formula_correct {n} (r : Fin n -> Ens) X c PX V S y :
  r PX = Power (r X) -> r V = value_bound (r c) ->
  (holds (remainingChoiceF X c PX V S y) r <->
    EQ (r y) (apply_set (r c) (remaining (r X) (r S)))).
Proof.
  intros EP EV. unfold remainingChoiceF. cbn [holds].
  setoid_rewrite remaining_formula_correct.
  setoid_rewrite apply_value_formula_correct.
  2: { cbn [eq_rect fin_match]. rewrite EV. apply application_value_bound. }
  cbn [fin_match]. rewrite EP. split.
  - intros [R [HR [ER EY]]]. eapply EQ_tran; [exact EY |].
    apply apply_set_extensional; [apply EQ_refl | exact ER].
  - intro E. exists (remaining (r X) (r S)).
    split; [apply INC_IN_Power, Comp_INC |]. split; [apply EQ_refl | exact E].
Qed.

Definition choice_step_certificate : Formula 6 :=
  ex (fsucc (fsucc fzero))
    (conj (remainingChoiceF (fsucc (fsucc (fsucc fzero)))
      (fsucc (fsucc (fsucc (fsucc fzero))))
      (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))
      (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))
      (fsucc (fsucc fzero)) fzero)
      (adjoinF (fsucc (fsucc fzero)) fzero (fsucc fzero))).
Definition choice_step_parameters X c := fin_match X
  (fin_match c (fin_match (Power X)
    (fin_match (value_bound c) (fun i : Fin 0 => match i with end)))).

Lemma choice_step_certificate_correct X c S Y :
  holds choice_step_certificate (fin_match Y (fin_match S (choice_step_parameters X c))) <->
  IN (apply_set c (remaining X S)) X /\
    EQ Y (adjoin S (apply_set c (remaining X S))).
Proof.
  unfold choice_step_certificate. cbn [holds].
  setoid_rewrite remaining_choice_formula_correct; try reflexivity.
  setoid_rewrite adjoin_formula_correct.
  cbn [choice_step_parameters fin_match]. split.
  - intros [z [HZ [EZ EY]]]. split.
    + exact (IN_sound_left z _ X EZ HZ).
    + eapply EQ_tran; [exact EY |]. apply Union_sound, Paire_sound_right, Sing_sound; exact EZ.
  - intros [HZ EY]. exists (apply_set c (remaining X S)); split; [exact HZ |].
    split; [apply EQ_refl | exact EY].
Qed.

Definition bounded_choice_step X c := bounded_formula_graph
  choice_step_certificate (choice_step_parameters X c) (Power X) (Power X).

Lemma bounded_choice_step_application X c S Y :
  application (bounded_choice_step X c) S Y <->
  IN S (Power X) /\ IN Y (Power X) /\
  IN (apply_set c (remaining X S)) X /\
    EQ Y (adjoin S (apply_set c (remaining X S))).
Proof.
  unfold bounded_choice_step. rewrite bounded_formula_graph_spec,
    choice_step_certificate_correct. reflexivity.
Qed.

Print Assumptions remaining_formula_correct.
Print Assumptions adjoin_formula_correct.
Print Assumptions remaining_choice_formula_correct.
Print Assumptions choice_step_certificate_correct.
Print Assumptions bounded_choice_step_application.

Lemma remaining_argument_congruence X S T : EQ S T ->
  EQ (remaining X S) (remaining X T).
Proof.
  intro E. apply INC_EQ; intros x HX; apply remaining_spec in HX as [HX HN];
    apply remaining_spec; split; [exact HX | | exact HX |]; intro HI; apply HN.
  - exact (IN_sound_right x T S (EQ_sym _ _ E) HI).
  - exact (IN_sound_right x S T E HI).
Qed.

Definition bounded_choice_prefix X c :=
  bounded_recursion_graph (Power X) (bounded_choice_step X c) Vide.

(** Environment: selected value, index, X, selector, Power X, value bound,
    prefix graph. Neither graph definition mentions the native sequence. *)
Definition choice_sequence_certificate : Formula 7 :=
  ex (fsucc (fsucc (fsucc (fsucc fzero))))
    (conj (applicationF (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))
      (fsucc (fsucc fzero)) fzero)
      (remainingChoiceF (fsucc (fsucc (fsucc fzero)))
        (fsucc (fsucc (fsucc (fsucc fzero))))
        (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))
        (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))
        fzero (fsucc fzero))).
Definition choice_sequence_parameters X c := fin_match X
  (fin_match c (fin_match (Power X) (fin_match (value_bound c)
    (fin_match (bounded_choice_prefix X c) (fun i : Fin 0 => match i with end))))).
Definition bounded_choice_sequence X c := bounded_formula_graph
  choice_sequence_certificate (choice_sequence_parameters X c) omega_codes X.

Section Infinite.
Variable classical_logic : forall P : Prop, P \/ ~ P.
Variables X c : Ens.
Hypothesis HC : subset_choice X c.
Hypothesis Hinf : forall n, ~ equinumerous X (finite_carrier n).

Lemma chosen_stage_power_bound n : IN (chosen_stage X c n) (Power X).
Proof.
  apply INC_IN_Power. intros z HZ.
  apply chosen_stage_spec in HZ as [i [HI E]].
  exact (IN_sound_left (chosen X c i) z X (EQ_sym _ _ E)
    (chosen_typed classical_logic X c HC Hinf i)).
Qed.

Lemma chosen_stage_step n : application (bounded_choice_step X c)
  (chosen_stage X c n) (chosen_stage X c (S n)).
Proof.
  apply bounded_choice_step_application. split; [apply chosen_stage_power_bound |].
  split; [apply chosen_stage_power_bound |]. split.
  - exact (chosen_typed classical_logic X c HC Hinf n).
  - apply EQ_refl.
Qed.

Lemma chosen_stage_step_unique n S Y : EQ S (chosen_stage X c n) ->
  application (bounded_choice_step X c) S Y -> EQ Y (chosen_stage X c (Datatypes.S n)).
Proof.
  intros ES HA.
  assert (HA' : application (bounded_choice_step X c) (chosen_stage X c n) Y).
  { eapply application_arguments; [apply EQ_refl | exact ES | apply EQ_refl | exact HA]. }
  apply bounded_choice_step_application in HA' as [_ [_ [_ EY]]]. exact EY.
Qed.

Theorem bounded_choice_prefix_application n Y :
  application (bounded_choice_prefix X c) (numeral n) Y <-> EQ Y (chosen_stage X c n).
Proof.
  exact (bounded_recursion_graph_application (Power X) (bounded_choice_step X c)
    (chosen_stage X c) chosen_stage_power_bound chosen_stage_step chosen_stage_step_unique n Y).
Qed.

Theorem bounded_choice_prefix_typed :
  IN (bounded_choice_prefix X c) (dependent_product omega_codes (fun _ => Power X)).
Proof.
  exact (bounded_recursion_graph_typed (Power X) (bounded_choice_step X c)
    (chosen_stage X c) chosen_stage_power_bound chosen_stage_step chosen_stage_step_unique).
Qed.

Lemma choice_sequence_certificate_correct n y :
  holds choice_sequence_certificate
    (fin_match y (fin_match (numeral n) (choice_sequence_parameters X c))) <->
  EQ y (chosen X c n).
Proof.
  unfold choice_sequence_certificate. cbn [holds].
  setoid_rewrite application_correct.
  setoid_rewrite remaining_choice_formula_correct; try reflexivity.
  cbn [choice_sequence_parameters fin_match]. split.
  - intros [S [HS [HP EY]]]. apply bounded_choice_prefix_application in HP.
    eapply EQ_tran; [exact EY |]. apply apply_set_extensional; [apply EQ_refl |].
    apply remaining_argument_congruence; exact HP.
  - intro E. exists (chosen_stage X c n); split; [apply chosen_stage_power_bound |].
    split; [apply bounded_choice_prefix_application, EQ_refl | exact E].
Qed.

Theorem bounded_choice_sequence_application n y :
  application (bounded_choice_sequence X c) (numeral n) y <-> EQ y (chosen X c n).
Proof.
  unfold bounded_choice_sequence. rewrite bounded_formula_graph_spec,
    choice_sequence_certificate_correct. split; [tauto |].
  intro E. split; [apply numeral_in_omega |]. split; [| exact E].
  exact (IN_sound_left (chosen X c n) y X (EQ_sym _ _ E)
    (chosen_typed classical_logic X c HC Hinf n)).
Qed.

Theorem bounded_choice_sequence_spec x y :
  application (bounded_choice_sequence X c) x y <->
    exists n, EQ x (numeral n) /\ EQ y (chosen X c n).
Proof.
  split.
  - intro HA. assert (HX : IN x omega_codes).
    { apply bounded_formula_graph_spec in HA; tauto. }
    apply omega_membership in HX as [n EX]. exists n; split; [exact EX |].
    apply (bounded_choice_sequence_application n y).
    eapply application_arguments; [apply EQ_refl | exact EX | apply EQ_refl | exact HA].
  - intros [n [EX EY]].
    eapply application_arguments; [apply EQ_refl | apply EQ_sym; exact EX | apply EQ_refl |].
    apply bounded_choice_sequence_application; exact EY.
Qed.

Theorem bounded_choice_sequence_agrees :
  EQ (bounded_choice_sequence X c) (choice_sequence_graph X c).
Proof.
  apply INC_EQ.
  - intros e HE.
    pose proof (Comp_INC _ _ e HE) as HB.
    destruct (IN_Prod_EXType omega_codes X e HB) as [x [y E]].
    assert (HA : application (bounded_choice_sequence X c) x y).
    { exact (IN_sound_left e _ _ (EQ_sym _ _ E) HE). }
    assert (HX : IN x omega_codes).
    { apply bounded_formula_graph_spec in HA; tauto. }
    apply omega_membership in HX as [n EX].
    assert (HY : EQ y (chosen X c n)).
    { apply (bounded_choice_sequence_application n y).
      eapply application_arguments; [apply EQ_refl | exact EX | apply EQ_refl | exact HA]. }
    apply (IN_sound_left (Couple x y) e _ E).
    apply choice_sequence_application. exists n; auto.
  - intros e [n E].
    apply (IN_sound_left (Couple (numeral n) (chosen X c n)) e _ (EQ_sym _ _ E)).
    apply bounded_choice_sequence_application, EQ_refl.
Qed.

Theorem bounded_choice_sequence_injection : injection omega_codes X (bounded_choice_sequence X c).
Proof.
  split.
  - apply bounded_function_member.
    + apply Comp_INC.
    + split.
      * intros x HX. apply omega_membership in HX as [n EX].
        exists (chosen X c n). apply bounded_choice_sequence_spec.
        exists n; split; [exact EX | apply EQ_refl].
      * split.
        -- intros x y HA. apply bounded_formula_graph_spec in HA; tauto.
        -- intros x y z HY HZ. apply bounded_choice_sequence_spec in HY as [n [EX EY]].
           apply bounded_choice_sequence_spec in HZ as [k [EX' EZ]].
           assert (EN : n = k).
           { apply numeral_injective; eapply EQ_tran; [apply EQ_sym; exact EX | exact EX']. }
           subst k; eapply EQ_tran; [exact EY | apply EQ_sym; exact EZ].
  - intros x x' y HA HB.
    apply bounded_choice_sequence_spec in HA as [n [EX EY]].
    apply bounded_choice_sequence_spec in HB as [k [EX' EY']].
    assert (EN : n = k).
    { apply (chosen_injective classical_logic X c HC Hinf).
      eapply EQ_tran; [apply EQ_sym; exact EY | exact EY']. }
    subst k; eapply EQ_tran; [exact EX | apply EQ_sym; exact EX'].
Qed.

Theorem bounded_choice_sequence_beta n :
  EQ (apply_set (bounded_choice_sequence X c) (numeral n)) (chosen X c n).
Proof.
  apply apply_set_value.
  - apply bounded_choice_sequence_application, EQ_refl.
  - intros y HY; apply bounded_choice_sequence_application; exact HY.
Qed.
End Infinite.

Theorem bounded_finite_countable_dichotomy (classical_logic : forall P : Prop, P \/ ~ P) X c :
  subset_choice X c ->
  (exists n, equinumerous X (finite_carrier n)) \/
    injection omega_codes X (bounded_choice_sequence X c).
Proof.
  intro HC. destruct (classical_logic (exists n, equinumerous X (finite_carrier n)))
    as [HF | Hinf]; [left; exact HF |].
  right; apply bounded_choice_sequence_injection; [exact classical_logic | exact HC |].
  intros n HN; apply Hinf; exists n; exact HN.
Qed.

Theorem bounded_finite_countable_from_choice (classical_logic : forall P : Prop, P \/ ~ P) :
  family_choice -> forall X,
  (exists n, equinumerous X (finite_carrier n)) \/
    exists c, subset_choice X c /\ injection omega_codes X (bounded_choice_sequence X c).
Proof.
  intros AC X. destruct (subset_choice_from_family_choice AC X) as [c HC].
  destruct (bounded_finite_countable_dichotomy classical_logic X c HC) as [HF | HI].
  - left; exact HF.
  - right; exists c; auto.
Qed.

Print Assumptions chosen_stage_power_bound.
Print Assumptions bounded_choice_prefix_application.
Print Assumptions bounded_choice_prefix_typed.
Print Assumptions choice_sequence_certificate_correct.
Print Assumptions bounded_choice_sequence_application.
Print Assumptions bounded_choice_sequence_spec.
Print Assumptions bounded_choice_sequence_agrees.
Print Assumptions bounded_choice_sequence_injection.
Print Assumptions bounded_choice_sequence_beta.
Print Assumptions bounded_finite_countable_dichotomy.
Print Assumptions bounded_finite_countable_from_choice.
Check bounded_choice_sequence_injection.
