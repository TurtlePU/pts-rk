(** Construct graph maps on Cartesian products without choosing representatives
    of the extensional set equality relation. *)
From ZFC Require Import Sets Axioms Cartesian.
From PTSrkModel Require Import SetFunctions SetApplication SetBijections ProductEmbedding.

Definition binary_extensional (f : Ens -> Ens -> Ens) :=
  forall x x' y y', EQ x x' -> EQ y y' -> EQ (f x y) (f x' y').
Definition cartesian_graph A B (f : Ens -> Ens -> Ens) :=
  sup (pi1 A * pi1 B) (fun p =>
    Couple (Couple (pi2 A (fst p)) (pi2 B (snd p)))
      (f (pi2 A (fst p)) (pi2 B (snd p)))).
Lemma cartesian_application A B f : binary_extensional f -> forall p z,
  application (cartesian_graph A B f) p z <->
  exists x, IN x A /\ exists y, IN y B /\ EQ p (Couple x y) /\ EQ z (f x y).
Proof.
  intros Hf p z. split.
  - intros [[i j] E]. exists (pi2 A i); split; [apply index_member |].
    exists (pi2 B j); split; [apply index_member |]. split;
      [exact (Couple_inj_left _ _ _ _ E) | exact (Couple_inj_right _ _ _ _ E)].
  - intros [x [Hx [y [Hy [Ep Ez]]]]].
    destruct (IN_EXType A x Hx) as [i Ei]. destruct (IN_EXType B y Hy) as [j Ej].
    exists (i,j). eapply EQ_tran; [apply Couple_sound_left | apply Couple_sound_right].
    + eapply EQ_tran; [exact Ep |].
      eapply EQ_tran; [apply Couple_sound_left; exact Ei | apply Couple_sound_right; exact Ej].
    + eapply EQ_tran; [exact Ez | apply Hf; assumption].
Qed.

Theorem cartesian_graph_injection A B C f : binary_extensional f ->
  (forall x y, IN x A -> IN y B -> IN (f x y) C) ->
  (forall x x' y y', IN x A -> IN x' A -> IN y B -> IN y' B ->
    EQ (f x y) (f x' y') -> EQ x x' /\ EQ y y') ->
  injection (Prod A B) C (cartesian_graph A B f).
Proof.
  intros Hf HT HI. split.
  - apply bounded_function_member.
    + intros e [[i j] E]. apply (IN_sound_left _ e _ (EQ_sym _ _ E)).
      apply Couple_IN_Prod.
      * apply Couple_IN_Prod; apply index_member.
      * apply HT; apply index_member.
    + split.
      * intros p Hp. destruct (IN_Prod_EXType _ _ _ Hp) as [x [y E]].
        pose proof (IN_sound_left p (Couple x y) _ (EQ_sym _ _ E) Hp) as Hxy.
        destruct (Couple_Prod_IN _ _ _ _ Hxy) as [Hx Hy].
        exists (f x y). apply (cartesian_application A B f Hf).
        exists x; split; [exact Hx |]. exists y; split; [exact Hy |].
        split; [apply EQ_sym; exact E | apply EQ_refl].
      * split.
        -- intros p z H. apply (cartesian_application A B f Hf) in H
             as [x [Hx [y [Hy [Ep Ez]]]]]. split.
           ++ apply (IN_sound_left (Couple x y) p _ (EQ_sym _ _ Ep)).
              apply Couple_IN_Prod; assumption.
           ++ apply (IN_sound_left (f x y) z C (EQ_sym _ _ Ez)). apply HT; assumption.
        -- intros p z z' H H'.
           apply (cartesian_application A B f Hf) in H as [x [Hx [y [Hy [Ep Ez]]]]].
           apply (cartesian_application A B f Hf) in H' as [x' [Hx' [y' [Hy' [Ep' Ez']]]]].
           pose proof (EQ_tran _ _ _ (EQ_sym _ _ Ep) Ep') as E.
           eapply EQ_tran; [exact Ez |]. eapply EQ_tran; [| apply EQ_sym; exact Ez'].
           apply Hf; [exact (Couple_inj_left _ _ _ _ E) | exact (Couple_inj_right _ _ _ _ E)].
  - intros p p' z H H'.
    apply (cartesian_application A B f Hf) in H as [x [Hx [y [Hy [Ep Ez]]]]].
    apply (cartesian_application A B f Hf) in H' as [x' [Hx' [y' [Hy' [Ep' Ez']]]]].
    destruct (HI x x' y y' Hx Hx' Hy Hy' (EQ_tran _ _ _ (EQ_sym _ _ Ez) Ez')) as [Ex Ey].
    eapply EQ_tran; [exact Ep |]. eapply EQ_tran; [| apply EQ_sym; exact Ep'].
    eapply EQ_tran; [apply Couple_sound_left; exact Ex | apply Couple_sound_right; exact Ey].
Qed.

Lemma cartesian_monotone A A' B B' : INC A A' -> INC B B' -> INC (Prod A B) (Prod A' B').
Proof.
  intros HA HB e He. destruct (IN_Prod_EXType _ _ _ He) as [x [y E]].
  pose proof (IN_sound_left e (Couple x y) _ (EQ_sym _ _ E) He) as Hxy.
  destruct (Couple_Prod_IN _ _ _ _ Hxy) as [Hx Hy].
  apply (IN_sound_left _ e _ E). apply Couple_IN_Prod; [apply HA | apply HB]; assumption.
Qed.
Lemma cartesian_extensional A A' B B' : EQ A A' -> EQ B B' -> EQ (Prod A B) (Prod A' B').
Proof.
  intros EA EB. apply INC_EQ; apply cartesian_monotone; apply EQ_INC;
    [exact EA | exact EB | apply EQ_sym; exact EA | apply EQ_sym; exact EB].
Qed.
Print Assumptions cartesian_graph_injection.
Print Assumptions cartesian_extensional.
