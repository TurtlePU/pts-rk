(** Infinite codes use singleton-numeral tags 3*n+1. Recover their index
    with the bounded tripling graph and evaluate the bounded carrier graph. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax.
From PTSrkModel Require Import SetFunctions SetApplication CodeUniverses
  CountableCodes CardinalHierarchy HierarchyBounds SuppliedHierarchy
  BoundedFormulas BoundedGraphs BoundedCodeArithmetic BoundedIteration.
Import Bounded CodeUniverses.CodeUniverses.

(** Environment: output, code, tripling graph, carrier graph, omega. *)
Definition infinite_decode_certificate : Formula 5 :=
  ex (fsucc (fsucc (fsucc (fsucc fzero))))
    (ex (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))
      (conj (applicationF (fsucc (fsucc (fsucc (fsucc fzero)))) (fsucc fzero) fzero)
        (conj (singletonF (fsucc (fsucc (fsucc fzero))) fzero)
          (applicationF (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))
            (fsucc fzero) (fsucc (fsucc fzero)))))).
Definition infinite_decode_parameters H := fin_match numeral_tripling_graph
  (fin_match (bounded_carrier_graph H) (fin_match omega_codes (fun i : Fin 0 => match i with end))).
Definition bounded_infinite_decoder H := bounded_formula_graph infinite_decode_certificate
  (infinite_decode_parameters H) omega_codes H.

Section Decoding.
Variables W H : Ens.
Hypothesis HW : transitive_set W.
Hypothesis HO : INC omega_codes W.
Hypothesis HH : tower_envelope W H.

Theorem infinite_decode_certificate_correct n y :
  holds infinite_decode_certificate
    (fin_match y (fin_match (repr (infinite n)) (infinite_decode_parameters H))) <->
  EQ y (carrier n).
Proof.
  unfold infinite_decode_certificate. cbn [holds].
  setoid_rewrite application_correct. setoid_rewrite singleton_correct.
  cbn [infinite_decode_parameters fin_match]. split.
  - intros [q [Hq [z [Hz [HT [ES HC]]]]]].
    apply omega_membership in Hq as [k EQq].
    assert (HT' : application numeral_tripling_graph (numeral k) z) by
      (eapply application_arguments; [apply EQ_refl | exact EQq | apply EQ_refl | exact HT]).
    apply numeral_tripling_application in HT'.
    change (EQ (Sing (numeral (3*n))) (Sing z)) in ES.
    apply EQ_Sing_EQ in ES.
    assert (EN : EQ (numeral (3*n)) (numeral (3*k))) by (eapply EQ_tran; eassumption).
    apply numeral_injective in EN. assert (E : k = n) by lia; subst k.
    apply (bounded_carrier_graph_application W H HW HO HH n y).
    eapply application_arguments; [apply EQ_refl | exact EQq | apply EQ_refl | exact HC].
  - intro E. exists (numeral n). split; [apply numeral_in_omega |].
    exists (numeral (3*n)). split; [apply numeral_in_omega |]. split.
    + apply numeral_tripling_application, EQ_refl.
    + split; [apply EQ_refl |].
      apply (bounded_carrier_graph_application W H HW HO HH n y); exact E.
Qed.

Theorem bounded_infinite_decoder_application n y :
  application (bounded_infinite_decoder H) (repr (infinite n)) y <-> EQ y (carrier n).
Proof.
  unfold bounded_infinite_decoder. rewrite bounded_formula_graph_spec.
  rewrite infinite_decode_certificate_correct. split; [tauto |].
  intro E. split; [apply numeral_in_omega |]. split; [| exact E].
  exact (IN_sound_left (carrier n) y H (EQ_sym _ _ E) (envelope_carrier W H n HO HH)).
Qed.

Theorem bounded_infinite_decoder_beta n :
  EQ (apply_set (bounded_infinite_decoder H) (repr (infinite n))) (carrier n).
Proof.
  apply apply_set_value.
  - apply bounded_infinite_decoder_application, EQ_refl.
  - intros y Hy. apply bounded_infinite_decoder_application; exact Hy.
Qed.

Theorem bounded_infinite_decoder_agrees n :
  EQ (apply_set (bounded_infinite_decoder H) (repr (infinite n)))
    (decode (repr (infinite n))).
Proof.
  eapply EQ_tran; [apply bounded_infinite_decoder_beta |].
  apply EQ_sym, decode_infinite.
Qed.
End Decoding.
Print Assumptions infinite_decode_certificate_correct.
Print Assumptions bounded_infinite_decoder_application.
Print Assumptions bounded_infinite_decoder_beta.
Print Assumptions bounded_infinite_decoder_agrees.
