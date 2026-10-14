(** A syntactic bounded-separation certificate for the existing inverse.
    This validates this predicate, not the complete BZC interpretation. *)
From ZFC Require Import Sets Axioms Cartesian.
From PTSrk Require Import Syntax.
From PTSrkModel Require Import SetFunctions SetBijections BoundedFormulas.
Import Bounded.

Definition reverseF {n} (A B f e : Fin n) :=
  ex A (ex (fsucc B)
    (conj (coupleF (fsucc (fsucc e)) fzero (fsucc fzero))
      (applicationF (fsucc (fsucc f)) (fsucc fzero) fzero))).
Definition bounded_reverse A B f e :=
  exists x, IN x A /\ exists y, IN y B /\ EQ e (Couple y x) /\ application f x y.
Lemma reverse_formula_correct {n} (r : Fin n -> Ens) A B f e :
  holds (reverseF A B f e) r <-> bounded_reverse (r A) (r B) (r f) (r e).
Proof.
  unfold reverseF, bounded_reverse. cbn [holds].
  setoid_rewrite couple_correct. setoid_rewrite application_correct. reflexivity.
Qed.
Lemma reverse_bounded_on_product A B f e : IN e (Prod B A) ->
  (reverse_edge f e <-> bounded_reverse A B f e).
Proof.
  intro He. split.
  - intros [x [y [E Hxy]]].
    pose proof (IN_sound_left e (Couple y x) (Prod B A) E He) as Hpair.
    destruct (Couple_Prod_IN _ _ _ _ Hpair) as [Hy Hx].
    exists x; split; [exact Hx |]. exists y; auto.
  - intros [x [Hx [y [Hy [E Hxy]]]]]. exists x, y; auto.
Qed.
Lemma bounded_reverse_extensional A B f e e' :
  bounded_reverse A B f e -> EQ e e' -> bounded_reverse A B f e'.
Proof.
  intros [x [Hx [y [Hy [E Hxy]]]]] E'.
  exists x; split; [exact Hx |]. exists y; split; [exact Hy |].
  split; [| exact Hxy]. eapply EQ_tran; [apply EQ_sym; exact E' | exact E].
Qed.

Definition empty_env (i : Fin 0) : Ens := match i with end.
Definition four_env A B f e := fin_match A (fin_match B (fin_match f (fin_match e empty_env))).
Definition reverse_certificate : Formula 4 :=
  reverseF fzero (fsucc fzero) (fsucc (fsucc fzero)) (fsucc (fsucc (fsucc fzero))).
Lemma reverse_certificate_correct A B f e :
  holds reverse_certificate (four_env A B f e) <-> bounded_reverse A B f e.
Proof. apply reverse_formula_correct. Qed.
Definition inverse_by_formula A B f :=
  Comp (Prod B A) (fun e => holds reverse_certificate (four_env A B f e)).
Theorem inverse_bounded_separation A B f : EQ (inverse A B f) (inverse_by_formula A B f).
Proof.
  apply INC_EQ.
  - intros e He. unfold inverse_by_formula. apply IN_P_Comp.
    + intros u v Hu E. apply reverse_certificate_correct in Hu.
      apply reverse_certificate_correct. eapply bounded_reverse_extensional; eassumption.
    + exact (Comp_INC _ _ _ He).
    + apply reverse_certificate_correct. apply reverse_bounded_on_product.
      * exact (Comp_INC _ _ _ He).
      * exact (IN_Comp_P _ _ _ (reverse_edge_extensional f) He).
  - intros e He. unfold inverse. apply IN_P_Comp.
    + apply reverse_edge_extensional.
    + exact (Comp_INC _ _ _ He).
    + apply (proj2 (reverse_bounded_on_product A B f e (Comp_INC _ _ _ He))).
      apply reverse_certificate_correct.
      eapply (IN_Comp_P (Prod B A) e (fun e => holds reverse_certificate (four_env A B f e)));
        [| exact He]. intros u v Hu E.
      apply reverse_certificate_correct in Hu. apply reverse_certificate_correct.
      eapply bounded_reverse_extensional; eassumption.
Qed.

Print Assumptions reverse_formula_correct.
Print Assumptions reverse_bounded_on_product.
Print Assumptions reverse_certificate_correct.
Print Assumptions inverse_bounded_separation.
Check reverse_certificate.
Check inverse_bounded_separation.
