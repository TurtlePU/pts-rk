(** Bounded membership test for the existing universes. Infinite tags are
    admitted exactly up to the supplied index; other tags are unrestricted. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From Equations Require Import Equations.
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax.
From PTSrkModel Require Import SetFunctions SetApplication CodeUniverses
  CountableCodes CodeHierarchyBounds BoundedFormulas BoundedGraphs
  BoundedCodeArithmetic BoundedFiniteCarriers BoundedFormulaTransport.
Import Bounded CodeUniverses.CodeUniverses.

Lemma key_enumerate n : key (enumerate n) = n.
Proof.
  induction n as [|n IH]; [reflexivity |]. cbn [enumerate].
  assert (HN : forall c, key (next c) = S (key c)) by (intro c; destruct c; cbn [key next]; lia).
  rewrite HN, IH; reflexivity.
Qed.
Lemma omega_has_code x : IN x omega_codes -> exists c, EQ x (repr c).
Proof.
  intro Hx. apply omega_membership in Hx as [n E]. exists (enumerate n).
  unfold repr; rewrite key_enumerate; exact E.
Qed.

Definition allowed_code_test C i x := forall q z,
  IN q omega_codes -> IN z omega_codes -> application numeral_tripling_graph q z ->
  EQ x (Sing z) -> EQ q i \/ IN q C.

Theorem allowed_code_test_correct n x : IN x omega_codes ->
  (allowed_code_test (finite_carrier n) (numeral n) x <-> IN x (U n)).
Proof.
  intro Hx; split.
  - intro HA. destruct (omega_has_code x Hx) as [c E].
    apply universe_membership. exists c; split; [| exact E].
    destruct c as [j|j|j]; cbn [Allowed]; [exact I | | exact I].
    assert (HT : application numeral_tripling_graph (numeral j) (numeral (3*j))) by
      (apply numeral_tripling_application, EQ_refl).
    destruct (HA (numeral j) (numeral (3*j)) (numeral_in_omega j)
      (numeral_in_omega (3*j)) HT E) as [EQj | Hj].
    + apply numeral_injective in EQj; lia.
    + apply finite_carrier_membership in Hj as [k [Hk Ek]].
      apply numeral_injective in Ek; lia.
  - intro HU. apply universe_membership in HU as [c [HC EC]].
    intros q z Hq Hz HT EX. apply omega_membership in Hq as [j EQq].
    assert (HT' : application numeral_tripling_graph (numeral j) z) by
      (eapply application_arguments; [apply EQ_refl | exact EQq | apply EQ_refl | exact HT]).
    apply numeral_tripling_application in HT'.
    assert (EI : EQ x (repr (infinite j))).
    { eapply EQ_tran; [exact EX | apply Sing_sound; exact HT']. }
    assert (E : c = infinite j).
    { apply repr_injective. eapply EQ_tran; [apply EQ_sym; exact EC | exact EI]. }
    subst c. change (j <= n) in HC. destruct (Nat.eq_dec j n) as [-> | Hne].
    + left; exact EQq.
    + right. apply finite_carrier_membership. exists j; split; [lia | exact EQq].
Qed.

Definition allowedCodeF {n} (O T C i x : Fin n) :=
  all O (all (fsucc O)
    (impl (conj (applicationF (fsucc (fsucc T)) (fsucc fzero) fzero)
      (singletonF (fsucc (fsucc x)) fzero))
      (disj (equal (fsucc fzero) (fsucc (fsucc i)))
        (member (fsucc fzero) (fsucc (fsucc C)))))).

Lemma allowed_code_formula_correct {n} (r : Fin n -> Ens) O T C i x :
  r O = omega_codes -> r T = numeral_tripling_graph ->
  (holds (allowedCodeF O T C i x) r <-> allowed_code_test (r C) (r i) (r x)).
Proof.
  intros EO ET. unfold allowedCodeF, allowed_code_test. cbn [holds].
  setoid_rewrite application_correct. setoid_rewrite singleton_correct.
  cbn [eq_rect fin_match]. rewrite EO, ET. split.
  - intros HC q z Hq Hz HT EX. exact (HC q Hq z Hz (Logic.conj HT EX)).
  - intros HC q Hq z Hz [HT EX]. exact (HC q z Hq Hz HT EX).
Qed.

Definition universeBodyF {n} (O T C i Y : Fin n) :=
  conj (all Y (conj (member fzero (fsucc O))
    (allowedCodeF (fsucc O) (fsucc T) (fsucc C) (fsucc i) fzero)))
    (all O (impl (allowedCodeF (fsucc O) (fsucc T) (fsucc C) (fsucc i) fzero)
      (member fzero (fsucc Y)))).

Theorem universe_body_formula_correct {k} (r : Fin k -> Ens) O T C i Y n :
  r O = omega_codes -> r T = numeral_tripling_graph ->
  r C = finite_carrier n -> r i = numeral n ->
  (holds (universeBodyF O T C i Y) r <-> EQ (r Y) (U n)).
Proof.
  intros EO ET EC EI. unfold universeBodyF. cbn [holds].
  assert (HA : forall x,
    holds (allowedCodeF (fsucc O) (fsucc T) (fsucc C) (fsucc i) fzero) (fin_match x r) <->
    allowed_code_test (finite_carrier n) (numeral n) x).
  { intro x. rewrite (allowed_code_formula_correct (fin_match x r)
      (fsucc O) (fsucc T) (fsucc C) (fsucc i) fzero EO ET).
    cbn [eq_rect fin_match]. rewrite EC, EI; reflexivity. }
  setoid_rewrite HA. cbn [eq_rect fin_match]. rewrite EO. split.
  - intros [HS HC]. apply INC_EQ.
    + intros x Hx. destruct (HS x Hx) as [HO HX].
      apply (proj1 (allowed_code_test_correct n x HO)); exact HX.
    + intros x Hx. pose proof (universe_subset_omega n x Hx) as HO.
      apply HC; [exact HO | apply (proj2 (allowed_code_test_correct n x HO)); exact Hx].
  - intro E. split.
    + intros x Hx. pose proof (IN_sound_right x _ _ E Hx) as HU.
      pose proof (universe_subset_omega n x HU) as HO. split; [exact HO |].
      apply (proj2 (allowed_code_test_correct n x HO)); exact HU.
    + intros x HO HX. apply (IN_sound_right x _ _ (EQ_sym _ _ E)).
      apply (proj1 (allowed_code_test_correct n x HO)); exact HX.
Qed.

(** Environment: universe value, index, finite-carrier graph, tripling
    graph, omega, powerset omega. *)
Definition universe_certificate : Formula 6 :=
  ex (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))
    (conj (applicationF (fsucc (fsucc (fsucc fzero))) (fsucc (fsucc fzero)) fzero)
      (universeBodyF (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))
        (fsucc (fsucc (fsucc (fsucc fzero)))) fzero
        (fsucc (fsucc fzero)) (fsucc fzero))).
Definition universe_parameters := fin_match finite_carrier_graph
  (fin_match numeral_tripling_graph (fin_match omega_codes
    (fin_match (Power omega_codes) (fun i : Fin 0 => match i with end)))).
Definition universe_env i Y := fin_match Y (fin_match i universe_parameters).

Theorem universe_certificate_correct n Y :
  holds universe_certificate (universe_env (numeral n) Y) <-> EQ Y (U n).
Proof.
  unfold universe_certificate. cbn [holds].
  setoid_rewrite application_correct. cbn [eq_rect universe_env universe_parameters fin_match].
  split.
  - intros [C [HC [HF HB]]]. apply finite_carrier_graph_application in HF.
    assert (ER : forall j, EQ (fin_match C (universe_env (numeral n) Y) j)
      (fin_match (finite_carrier n) (universe_env (numeral n) Y) j)).
    { intro j; dependent elimination j; [exact HF | apply EQ_refl]. }
    apply (proj1 (holds_extensional _ _ _ ER)) in HB.
    exact (proj1 (universe_body_formula_correct
      (fin_match (finite_carrier n) (universe_env (numeral n) Y))
      (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))
      (fsucc (fsucc (fsucc (fsucc fzero)))) fzero
      (fsucc (fsucc fzero)) (fsucc fzero) n eq_refl eq_refl eq_refl eq_refl) HB).
  - intro E. exists (finite_carrier n). split; [apply INC_IN_Power, finite_subset_omega |].
    split; [apply finite_carrier_graph_application, EQ_refl |].
    exact (proj2 (universe_body_formula_correct
      (fin_match (finite_carrier n) (universe_env (numeral n) Y))
      (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))
      (fsucc (fsucc (fsucc (fsucc fzero)))) fzero
      (fsucc (fsucc fzero)) (fsucc fzero) n eq_refl eq_refl eq_refl eq_refl) E).
Qed.

Definition bounded_universe_graph := bounded_formula_graph universe_certificate
  universe_parameters omega_codes (Power omega_codes).
Theorem bounded_universe_graph_application n Y :
  application bounded_universe_graph (numeral n) Y <-> EQ Y (U n).
Proof.
  unfold bounded_universe_graph. rewrite bounded_formula_graph_spec.
  fold (universe_env (numeral n) Y).
  rewrite universe_certificate_correct. split; [tauto |].
  intro E. split; [apply numeral_in_omega |]. split; [| exact E].
  apply (IN_sound_left (U n) Y _ (EQ_sym _ _ E)), INC_IN_Power, universe_subset_omega.
Qed.
Theorem bounded_universe_graph_beta n : EQ (apply_set bounded_universe_graph (numeral n)) (U n).
Proof.
  apply apply_set_value.
  - apply bounded_universe_graph_application, EQ_refl.
  - intros Y HY. apply bounded_universe_graph_application; exact HY.
Qed.

Print Assumptions key_enumerate.
Print Assumptions omega_has_code.
Print Assumptions allowed_code_test_correct.
Print Assumptions allowed_code_formula_correct.
Print Assumptions universe_body_formula_correct.
Print Assumptions universe_certificate_correct.
Print Assumptions bounded_universe_graph_application.
Print Assumptions bounded_universe_graph_beta.
