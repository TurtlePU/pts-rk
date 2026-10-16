(** Extensionality of semantic dependent products, with no change to PTS rules. *)
From ZFC Require Import Sets Axioms Cartesian.
From PTSrkModel Require Import SetFunctions SetApplication SetBijections CartesianMaps.

Lemma family_range_congruence A A' B B' : EQ A A' ->
  family_extensional B -> family_extensional B' ->
  (forall x, IN x A -> EQ (B x) (B' x)) -> EQ (family_range A B) (family_range A' B').
Proof.
  intros EA HB HB' HP. apply INC_EQ.
  - intros Y [i E]. pose proof (index_member A i) as Hi.
    destruct (IN_EXType A' (pi2 A i) (IN_sound_right _ _ _ EA Hi)) as [j Ej].
    exists j. eapply EQ_tran; [exact E |]. eapply EQ_tran; [apply HP; exact Hi | apply HB'; exact Ej].
  - intros Y [j E]. pose proof (IN_sound_right _ _ _ (EQ_sym _ _ EA) (index_member A' j)) as Hj.
    destruct (IN_EXType A (pi2 A' j) Hj) as [i Ei]. exists i.
    eapply EQ_tran; [exact E |]. eapply EQ_tran; [apply EQ_sym, HP; exact Hj | apply HB; exact Ei].
Qed.
Lemma function_laws_congruence A A' B B' f : EQ A A' ->
  (forall x, IN x A -> EQ (B x) (B' x)) ->
  function_laws A B f -> function_laws A' B' f.
Proof.
  intros EA HP [HT [HB HU]]. split.
  - intros x Hx; apply HT; exact (IN_sound_right _ _ _ (EQ_sym _ _ EA) Hx).
  - split; [| exact HU]. intros x y Hxy. destruct (HB x y Hxy) as [Hx Hy].
    split; [exact (IN_sound_right _ _ _ EA Hx) | exact (IN_sound_right _ _ _ (HP x Hx) Hy)].
Qed.
Theorem dependent_product_congruence A A' B B' : EQ A A' ->
  family_extensional B -> family_extensional B' ->
  (forall x, IN x A -> EQ (B x) (B' x)) ->
  EQ (dependent_product A B) (dependent_product A' B').
Proof.
  intros EA HB HB' HP.
  assert (ER : EQ (Power (Prod A (Union (family_range A B))))
    (Power (Prod A' (Union (family_range A' B'))))).
  { apply Power_sound, cartesian_extensional; [exact EA |].
    apply Union_sound, family_range_congruence; assumption. }
  apply INC_EQ; intros f Hf; apply IN_P_Comp.
  - intros g h H E; exact (function_laws_extensional A' B' g h H E).
  - exact (IN_sound_right _ _ _ ER (Comp_INC _ _ _ Hf)).
  - apply (function_laws_congruence A A' B B' f EA HP), dependent_product_elimination; exact Hf.
  - intros g h H E; exact (function_laws_extensional A B g h H E).
  - exact (IN_sound_right _ _ _ (EQ_sym _ _ ER) (Comp_INC _ _ _ Hf)).
  - eapply function_laws_congruence; [apply EQ_sym; exact EA | | apply dependent_product_elimination; exact Hf].
    intros x Hx; apply EQ_sym, HP; exact (IN_sound_right _ _ _ (EQ_sym _ _ EA) Hx).
Qed.
Theorem bijection_domain_equal A A' K f : EQ A A' -> bijection A K f -> bijection A' K f.
Proof.
  intros E [HT HB]; split; [| exact HB].
  apply (IN_sound_right f (dependent_product A (fun _ => K))).
  - apply dependent_product_congruence; [exact E | | |].
    + intros x y Exy; apply EQ_refl.
    + intros x y Exy; apply EQ_refl.
    + intros x Hx; apply EQ_refl.
  - exact HT.
Qed.
Print Assumptions dependent_product_congruence.
Print Assumptions bijection_domain_equal.
