(** Sort tags 3*n+2 decode to the exact existing universe U n. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax.
From PTSrkModel Require Import SetFunctions SetApplication CodeUniverses
  CountableCodes CardinalHierarchy CodeHierarchyBounds BoundedFormulas
  BoundedGraphs BoundedCodeArithmetic BoundedUniverses.
Import Bounded CodeUniverses.CodeUniverses.

Definition sort_decode_certificate : Formula 5 :=
  ex (fsucc (fsucc (fsucc (fsucc fzero))))
    (ex (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))
      (ex (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))
        (conj (applicationF (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))
          (fsucc (fsucc fzero)) (fsucc fzero))
          (conj (singletonF fzero (fsucc fzero))
            (conj (singletonF (fsucc (fsucc (fsucc (fsucc fzero)))) fzero)
              (applicationF (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))
                (fsucc (fsucc fzero)) (fsucc (fsucc (fsucc fzero))))))))).
Definition sort_decode_parameters := fin_match numeral_tripling_graph
  (fin_match bounded_universe_graph (fin_match omega_codes (fun i : Fin 0 => match i with end))).
Definition bounded_sort_decoder := bounded_formula_graph sort_decode_certificate
  sort_decode_parameters omega_codes (Power omega_codes).

Theorem sort_decode_certificate_correct n y :
  holds sort_decode_certificate (fin_match y (fin_match (repr (sort n)) sort_decode_parameters)) <->
  EQ y (U n).
Proof.
  unfold sort_decode_certificate. cbn [holds].
  setoid_rewrite application_correct. setoid_rewrite singleton_correct.
  cbn [eq_rect sort_decode_parameters fin_match]. split.
  - intros [q [Hq [z [Hz [t [Ht [HT [ET [ES HU]]]]]]]]].
    apply omega_membership in Hq as [k EQq].
    assert (HT' : application numeral_tripling_graph (numeral k) z) by
      (eapply application_arguments; [apply EQ_refl | exact EQq | apply EQ_refl | exact HT]).
    apply numeral_tripling_application in HT'.
    assert (EX : EQ (Sing (Sing (numeral (3*n)))) (Sing (Sing z))).
    { eapply EQ_tran; [exact ES | apply Sing_sound; exact ET]. }
    apply EQ_Sing_EQ in EX. apply EQ_Sing_EQ in EX.
    assert (EN : EQ (numeral (3*n)) (numeral (3*k))) by (eapply EQ_tran; eassumption).
    apply numeral_injective in EN. assert (E : k = n) by lia; subst k.
    apply bounded_universe_graph_application.
    eapply application_arguments; [apply EQ_refl | exact EQq | apply EQ_refl | exact HU].
  - intro E. exists (numeral n). split; [apply numeral_in_omega |].
    exists (numeral (3*n)). split; [apply numeral_in_omega |].
    exists (numeral (S (3*n))). split; [apply numeral_in_omega |]. split.
    + apply numeral_tripling_application, EQ_refl.
    + split; [apply EQ_refl |]. split; [apply EQ_refl |].
      apply bounded_universe_graph_application; exact E.
Qed.

Theorem bounded_sort_decoder_application n y :
  application bounded_sort_decoder (repr (sort n)) y <-> EQ y (U n).
Proof.
  unfold bounded_sort_decoder. rewrite bounded_formula_graph_spec.
  rewrite sort_decode_certificate_correct. split; [tauto |].
  intro E. split; [apply numeral_in_omega |]. split; [| exact E].
  apply (IN_sound_left (U n) y _ (EQ_sym _ _ E)), INC_IN_Power, universe_subset_omega.
Qed.
Theorem bounded_sort_decoder_beta n :
  EQ (apply_set bounded_sort_decoder (repr (sort n))) (U n).
Proof.
  apply apply_set_value.
  - apply bounded_sort_decoder_application, EQ_refl.
  - intros y Hy. apply bounded_sort_decoder_application; exact Hy.
Qed.
Theorem bounded_sort_decoder_agrees n :
  EQ (apply_set bounded_sort_decoder (repr (sort n))) (decode (repr (sort n))).
Proof. eapply EQ_tran; [apply bounded_sort_decoder_beta | apply EQ_sym, decode_sort]. Qed.
Print Assumptions sort_decode_certificate_correct.
Print Assumptions bounded_sort_decoder_application.
Print Assumptions bounded_sort_decoder_beta.
Print Assumptions bounded_sort_decoder_agrees.
