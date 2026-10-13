(** Typed observation-prefix assembly through the four domain certificates. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting DirectRCodes DirectRKernel
  DirectRStructural DirectRLogic DirectRFiniteTables DirectRBinaryTables
  DirectRSeparation DirectRTelescopeArguments DirectRFiniteData DirectRFiniteBinaryDomain
  DirectRRelationTables DirectRFunctionalFiniteLaws DirectRFiniteUp DirectRUnary
  DirectRGuardedFiniteLaws DirectRFiniteTransitivity DirectRFiniteUnaryCongruence.
Import ListNotations.
Module FiniteDomainPrefix.
Import Codes Core Structural NegativeLogic FiniteTables BinaryTables TelescopeArguments FiniteData.
Definition binary_guard {n} (X op D : Term nat n) :=
  Π X (Arrow (app (shift D) V0)
    (Π (shift X) (Arrow (app (shift (shift D)) V0)
      (app (shift (shift D)) (app (app (shift (shift op)) (shift V0)) V0))))).
Lemma replace_binary_guard {m n} (f : Fin m -> Term nat n) X op D :
  replace f (binary_guard X op D) = binary_guard (replace f X) (replace f op) (replace f D).
Proof.
  unfold binary_guard.
  repeat first [rewrite replace_product |rewrite replace_arrow |
    rewrite replace_application |rewrite replace_shift]. reflexivity.
Qed.
Lemma binary_guard_closed q op :
  binary_guard (selector_type q) op (Separation.predicate q) =
  FiniteBinaryDomain.application_type q op.
Proof.
  unfold binary_guard.
  assert (HF : @shift nat 0 (selector_type q) = selector_type q).
  { unfold shift. apply rename_selector_type. }
  rewrite HF.
  assert (HC : forall c : closed_term, shift c = @lift_closed 1 c).
  { intro c. rewrite lift_closed_shift, lift_closed_zero. reflexivity. }
  rewrite !HC, <- !lift_closed_shift. reflexivity.
Qed.
Definition addition_annotation : Term nat 10 :=
  binary_guard (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))
    (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))
    (var (fsucc (fsucc (fsucc (fsucc fzero))))).
Definition multiplication_annotation : Term nat 11 :=
  binary_guard (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))
    (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))
    (var (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))).
Theorem domain_prefix_matches_source body :
  assemble (npis (firstn 12 observation_fields) body) [] =
  option_map (fun B => telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation B)))))
    (assemble body [103;102;101;100;7;6;5;4;3;2;1;0]).
Proof.
  cbn [npis firstn observation_fields fold_right fst snd assemble lookup Nat.eqb].
  destruct (assemble body [103;102;101;100;7;6;5;4;3;2;1;0]); reflexivity.
Qed.
Lemma addition_annotation_specialized q p0 p1 :
  replace (extend p1 (extend p0 (data_substitution q))) addition_annotation =
  FiniteBinaryDomain.application_type q (capped_addition q).
Proof.
  unfold addition_annotation. rewrite replace_binary_guard.
  change (binary_guard (selector_type q) (capped_addition q) (Separation.predicate q) =
    FiniteBinaryDomain.application_type q (capped_addition q)).
  apply binary_guard_closed.
Qed.
Lemma multiplication_annotation_specialized q p0 p1 p2 :
  replace (extend p2 (extend p1 (extend p0 (data_substitution q)))) multiplication_annotation =
  FiniteBinaryDomain.application_type q (capped_multiplication q).
Proof.
  unfold multiplication_annotation. rewrite replace_binary_guard.
  change (binary_guard (selector_type q) (capped_multiplication q) (Separation.predicate q) =
    FiniteBinaryDomain.application_type q (capped_multiplication q)).
  apply binary_guard_closed.
Qed.
Theorem domain_specialization q f (B : Term nat 12) : 0 < q ->
  Typed ε f (telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation B))))) ->
  exists p0 p1 p2 p3,
    Typed ε p0 (replace (data_substitution q) initial_annotation) /\
    Typed ε p1 (replace (extend p0 (data_substitution q)) step_annotation) /\
    Typed ε p2 (replace (extend p1 (extend p0 (data_substitution q))) addition_annotation) /\
    Typed ε p3 (replace (extend p2 (extend p1 (extend p0 (data_substitution q)))) multiplication_annotation) /\
    Typed ε (app (app (app (app (table_apply f (data_arguments q)) p0) p1) p2) p3)
      (replace (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))) B).
Proof.
  intros Hq Hf. destruct (step_specialization q f _ Hq Hf) as [p0 [p1 [Hp0 [Hp1 H1]]]].
  destruct (FiniteBinaryDomain.addition_certificate q Hq) as [p2 Hp2].
  destruct (FiniteBinaryDomain.multiplication_certificate q Hq) as [p3 Hp3].
  rewrite <- (addition_annotation_specialized q p0 p1) in Hp2.
  rewrite <- (multiplication_annotation_specialized q p0 p1 p2) in Hp3.
  exists p0, p1, p2, p3. split; [exact Hp0 |]. split; [exact Hp1 |].
  split; [exact Hp2 |]. split; [exact Hp3 |].
  rewrite replace_product in H1. pose proof (tApp H1 Hp2) as H2.
  rewrite substitute_transpose, replace_product in H2. pose proof (tApp H2 Hp3) as H3.
  rewrite substitute_transpose in H3. exact H3.
Qed.
(** The next source field is guarded equality reflexivity. Keep its raw
    predicate/table applications, including all lambda annotations. *)
Definition reflexivity_guard {n} (X D R : Term nat n) :=
  Π X (Arrow (app (shift D) V0)
    (Neg (app (app (shift R) V0) V0))).
Lemma replace_reflexivity_guard {m n} (f : Fin m -> Term nat n) X D R :
  replace f (reflexivity_guard X D R) =
  reflexivity_guard (replace f X) (replace f D) (replace f R).
Proof.
  unfold reflexivity_guard, Neg.
  repeat first [rewrite replace_product |rewrite replace_arrow |
    rewrite replace_application |rewrite replace_shift |rewrite replace_lift_closed].
  reflexivity.
Qed.
Definition reflexivity_application_type q r : closed_term :=
  Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
    (Neg (app (app (lift_closed (RelationTables.relation_table q r)) V0) V0))).
Lemma relation_application_typed {n} (Γ : Ctx nat n) q r u v :
  Typed Γ u (selector_type q) -> Typed Γ v (selector_type q) ->
  Typed Γ (app (app (lift_closed (RelationTables.relation_table q r)) u) v) (𝓤 1).
Proof.
  intros Hu Hv.
  pose proof (lift_closed_typed Γ _ _ (RelationTables.relation_table_typed q r)) as HR.
  unfold lift_closed at 2 in HR. rewrite !rename_arrow, !rename_selector_type in HR.
  eapply arrow_application; [eapply arrow_application; [exact HR |exact Hu] |exact Hv].
Qed.
Lemma relation_application_beta {n} q r (u v : Term nat n) :
  app (app (lift_closed (RelationTables.relation_table q r)) u) v =ᵝ
  RelationTables.relation_at q r u v.
Proof.
  unfold RelationTables.relation_table, lift_closed. cbn [rename].
  rewrite !rename_selector_type, rename_as_replace, RelationTables.replace_relation_at.
  eapply beta_trans; [eapply beta_app; [apply beta_contract |reflexivity] |].
  unfold subst at 1. cbn [replace].
  rewrite replace_selector_type, RelationTables.replace_relation_at.
  change (app (lam (selector_type q) (RelationTables.relation_at q r (shift u) V0)) v =ᵝ
    RelationTables.relation_at q r u v).
  eapply beta_trans; [apply beta_contract |].
  unfold subst. rewrite RelationTables.replace_relation_at, replace_shift_substitution.
  reflexivity.
Qed.
Lemma reflexivity_application_typed q r : 0 < q ->
  Typed ε (reflexivity_application_type q r) (𝓤 5).
Proof.
  intro Hq. destruct q as [|q]; [lia |]. unfold reflexivity_application_type.
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 2).
  - apply Separation.predicate_application; [exact Hq |apply GuardedFiniteLaws.selector_newest].
  - apply neg_formation, relation_application_typed; apply GuardedFiniteLaws.selector_newest.
Qed.
Lemma reflexivity_application_beta q r :
  reflexivity_application_type q r =ᵝ FunctionalFiniteLaws.reflexivity_type q r.
Proof.
  unfold reflexivity_application_type, FunctionalFiniteLaws.reflexivity_type.
  apply beta_pi; [reflexivity |]. apply Unary.arrow_beta;
    [apply Separation.predicate_beta |].
  apply FiniteUp.neg_beta, relation_application_beta.
Qed.
Theorem reflexivity_application_certificate q r : 0 < q ->
  (forall i, i < q -> r i i = true) -> Realizes (reflexivity_application_type q r).
Proof.
  intros Hq Hr. eapply FiniteUp.inhabited_conversion.
  - exact (FunctionalFiniteLaws.reflexivity_realized q r Hq Hr).
  - apply reflexivity_application_typed; exact Hq.
  - symmetry. apply reflexivity_application_beta.
Qed.
Definition reflexivity_annotation : Term nat 12 :=
  reflexivity_guard
    (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))
    (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))
    (var (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))).
Lemma reflexivity_annotation_specialized q p0 p1 p2 p3 :
  replace (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))
    reflexivity_annotation = reflexivity_application_type q Nat.eqb.
Proof.
  unfold reflexivity_annotation. rewrite replace_reflexivity_guard.
  change (reflexivity_guard (selector_type q) (Separation.predicate q)
    (RelationTables.relation_table q Nat.eqb) = reflexivity_application_type q Nat.eqb).
  unfold reflexivity_guard, reflexivity_application_type.
  rewrite !lift_closed_shift, !lift_closed_zero. reflexivity.
Qed.
Theorem reflexivity_prefix_matches_source body :
  assemble (npis (firstn 13 observation_fields) body) [] =
  option_map (fun B => telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation
      (Π multiplication_annotation (Π reflexivity_annotation B))))))
    (assemble body [104;103;102;101;100;7;6;5;4;3;2;1;0]).
Proof.
  cbn [npis firstn observation_fields fold_right fst snd assemble lookup Nat.eqb].
  destruct (assemble body [104;103;102;101;100;7;6;5;4;3;2;1;0]); reflexivity.
Qed.
Theorem reflexivity_specialization q f (B : Term nat 13) : 0 < q ->
  Typed ε f (telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation
      (Π multiplication_annotation (Π reflexivity_annotation B)))))) ->
  exists p0 p1 p2 p3 p4,
    Typed ε p4 (replace (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))
      reflexivity_annotation) /\
    Typed ε (app (app (app (app (app (table_apply f (data_arguments q)) p0) p1) p2) p3) p4)
      (replace (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))) B).
Proof.
  intros Hq Hf.
  destruct (domain_specialization q f _ Hq Hf) as [p0 [p1 [p2 [p3 [H0 [H1 [H2 [H3 Hf4]]]]]]]].
  destruct (reflexivity_application_certificate q Nat.eqb Hq
    (fun i _ => Nat.eqb_refl i)) as [p4 Hp4].
  rewrite <- (reflexivity_annotation_specialized q p0 p1 p2 p3) in Hp4.
  exists p0, p1, p2, p3, p4. split; [exact Hp4 |].
  rewrite replace_product in Hf4. pose proof (tApp Hf4 Hp4) as Hf5.
  rewrite substitute_transpose in Hf5. exact Hf5.
Qed.
Definition symmetry_guard {n} (X D R : Term nat n) :=
  Π X (Arrow (app (shift D) V0)
    (Π (shift X) (Arrow (app (shift (shift D)) V0)
      (Arrow (Neg (app (app (shift (shift R)) (shift V0)) V0))
        (Neg (app (app (shift (shift R)) V0) (shift V0))))))).
Lemma replace_symmetry_guard {m n} (f : Fin m -> Term nat n) X D R :
  replace f (symmetry_guard X D R) =
  symmetry_guard (replace f X) (replace f D) (replace f R).
Proof.
  unfold symmetry_guard, Neg.
  repeat first [rewrite replace_product |rewrite replace_arrow |
    rewrite replace_application |rewrite replace_shift |rewrite replace_lift_closed].
  reflexivity.
Qed.
Definition symmetry_application_type q r : closed_term :=
  Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
    (Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
      (Arrow (Neg (app (app (lift_closed (RelationTables.relation_table q r)) (shift V0)) V0))
        (Neg (app (app (lift_closed (RelationTables.relation_table q r)) V0) (shift V0))))))).
Lemma symmetry_application_typed q r : 0 < q ->
  Typed ε (symmetry_application_type q r) (𝓤 5).
Proof.
  intro Hq. destruct q as [|q]; [lia |]. unfold symmetry_application_type.
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 5).
  - apply Separation.predicate_application; [exact Hq |apply GuardedFiniteLaws.selector_newest].
  - apply (tPi (b:=5) (selector_type_formation (S q) _)).
    apply (arrow_formation _ _ _ 4 3).
    + apply Separation.predicate_application; [exact Hq |apply GuardedFiniteLaws.selector_newest].
    + apply (arrow_formation _ _ _ 2 2); apply neg_formation, relation_application_typed;
        first [apply GuardedFiniteLaws.selector_newest |
          apply GuardedFiniteLaws.selector_weaken, GuardedFiniteLaws.selector_newest].
Qed.
Lemma symmetry_application_beta q r :
  symmetry_application_type q r =ᵝ FunctionalFiniteLaws.symmetry_type q r.
Proof.
  unfold symmetry_application_type, FunctionalFiniteLaws.symmetry_type,
    FunctionalFiniteLaws.symmetry_body.
  do 2 (apply beta_pi; [reflexivity |]; apply Unary.arrow_beta;
    [apply Separation.predicate_beta |]).
  apply Unary.arrow_beta; apply FiniteUp.neg_beta, relation_application_beta.
Qed.
Theorem symmetry_application_certificate q r : 0 < q ->
  (forall i j, i < q -> j < q -> r i j = true -> r j i = true) ->
  Realizes (symmetry_application_type q r).
Proof.
  intros Hq Hr. eapply FiniteUp.inhabited_conversion.
  - exact (FunctionalFiniteLaws.symmetry_realized q r Hq Hr).
  - apply symmetry_application_typed; exact Hq.
  - symmetry. apply symmetry_application_beta.
Qed.
Definition symmetry_annotation : Term nat 13 :=
  symmetry_guard
    (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))
    (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))
    (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))).
Lemma symmetry_annotation_specialized q p0 p1 p2 p3 p4 :
  replace (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))
    symmetry_annotation = symmetry_application_type q Nat.eqb.
Proof.
  unfold symmetry_annotation. rewrite replace_symmetry_guard.
  change (symmetry_guard (selector_type q) (Separation.predicate q)
    (RelationTables.relation_table q Nat.eqb) = symmetry_application_type q Nat.eqb).
  unfold symmetry_guard, symmetry_application_type.
  assert (HF : @shift nat 0 (selector_type q) = selector_type q).
  { unfold shift. apply rename_selector_type. }
  rewrite HF.
  assert (HC : forall c : closed_term, shift c = @lift_closed 1 c).
  { intro c. rewrite lift_closed_shift, lift_closed_zero. reflexivity. }
  rewrite !HC, <- !lift_closed_shift. reflexivity.
Qed.
Theorem symmetry_prefix_matches_source body :
  assemble (npis (firstn 14 observation_fields) body) [] =
  option_map (fun B => telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation
      (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation B)))))))
    (assemble body [105;104;103;102;101;100;7;6;5;4;3;2;1;0]).
Proof.
  cbn [npis firstn observation_fields fold_right fst snd assemble lookup Nat.eqb].
  destruct (assemble body [105;104;103;102;101;100;7;6;5;4;3;2;1;0]); reflexivity.
Qed.
Theorem symmetry_specialization q f (B : Term nat 14) : 0 < q ->
  Typed ε f (telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation
      (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation B))))))) ->
  exists p0 p1 p2 p3 p4 p5,
    Typed ε p5 (replace (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))
      symmetry_annotation) /\
    Typed ε (app (app (app (app (app (app (table_apply f (data_arguments q)) p0) p1) p2) p3) p4) p5)
      (replace (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))) B).
Proof.
  intros Hq Hf.
  destruct (reflexivity_specialization q f _ Hq Hf) as [p0 [p1 [p2 [p3 [p4 [Hp4 Hf5]]]]]].
  assert (Hr : forall i j, i < q -> j < q -> Nat.eqb i j = true -> Nat.eqb j i = true).
  { intros i j Hi Hj H. rewrite Nat.eqb_sym. exact H. }
  destruct (symmetry_application_certificate q Nat.eqb Hq Hr) as [p5 Hp5].
  rewrite <- (symmetry_annotation_specialized q p0 p1 p2 p3 p4) in Hp5.
  exists p0, p1, p2, p3, p4, p5. split; [exact Hp5 |].
  rewrite replace_product in Hf5. pose proof (tApp Hf5 Hp5) as Hf6.
  rewrite substitute_transpose in Hf6. exact Hf6.
Qed.
Definition transitivity_guard {n} (X D R : Term nat n) :=
  Π X (Arrow (app (shift D) V0)
    (Π (shift X) (Arrow (app (shift (shift D)) V0)
      (Π (shift (shift X)) (Arrow (app (shift (shift (shift D))) V0)
        (Arrow (Neg (app (app (shift (shift (shift R))) (shift (shift V0))) (shift V0)))
          (Arrow (Neg (app (app (shift (shift (shift R))) (shift V0)) V0))
            (Neg (app (app (shift (shift (shift R))) (shift (shift V0))) V0))))))))).
Lemma replace_transitivity_guard {m n} (f : Fin m -> Term nat n) X D R :
  replace f (transitivity_guard X D R) =
  transitivity_guard (replace f X) (replace f D) (replace f R).
Proof.
  unfold transitivity_guard, Neg.
  repeat first [rewrite replace_product |rewrite replace_arrow |
    rewrite replace_application |rewrite replace_shift |rewrite replace_lift_closed].
  reflexivity.
Qed.
Definition transitivity_application_type q r : closed_term :=
  Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
    (Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
      (Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
        (Arrow (Neg (app (app (lift_closed (RelationTables.relation_table q r)) (shift (shift V0))) (shift V0)))
          (Arrow (Neg (app (app (lift_closed (RelationTables.relation_table q r)) (shift V0)) V0))
            (Neg (app (app (lift_closed (RelationTables.relation_table q r)) (shift (shift V0))) V0))))))))).
Lemma transitivity_application_typed q r : 0 < q ->
  Typed ε (transitivity_application_type q r) (𝓤 5).
Proof.
  intro Hq. destruct q as [|q]; [lia |]. unfold transitivity_application_type.
  do 2 (apply (tPi (b:=5) (selector_type_formation (S q) _));
    apply (arrow_formation _ _ _ 4 5);
    [apply Separation.predicate_application; [exact Hq |apply GuardedFiniteLaws.selector_newest] |]).
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 3).
  - apply Separation.predicate_application; [exact Hq |apply GuardedFiniteLaws.selector_newest].
  - apply (arrow_formation _ _ _ 2 3).
    + apply neg_formation, relation_application_typed;
        repeat apply GuardedFiniteLaws.selector_weaken; apply GuardedFiniteLaws.selector_newest.
    + apply (arrow_formation _ _ _ 2 2); apply neg_formation, relation_application_typed;
        repeat apply GuardedFiniteLaws.selector_weaken; apply GuardedFiniteLaws.selector_newest.
Qed.
Lemma transitivity_application_beta q r :
  transitivity_application_type q r =ᵝ FiniteTransitivity.expanded_type q r.
Proof.
  unfold transitivity_application_type, FiniteTransitivity.expanded_type, FiniteTransitivity.body.
  do 3 (apply beta_pi; [reflexivity |]; apply Unary.arrow_beta;
    [apply Separation.predicate_beta |]).
  apply Unary.arrow_beta; [apply FiniteUp.neg_beta, relation_application_beta |].
  apply Unary.arrow_beta; apply FiniteUp.neg_beta, relation_application_beta.
Qed.
Theorem transitivity_application_certificate q r : 0 < q ->
  (forall i j k, i < q -> j < q -> k < q ->
    r i j = true -> r j k = true -> r i k = true) ->
  Realizes (transitivity_application_type q r).
Proof.
  intros Hq Hr. eapply FiniteUp.inhabited_conversion.
  - exact (FiniteTransitivity.expanded_transitivity_realized q r Hq Hr).
  - apply transitivity_application_typed; exact Hq.
  - symmetry. apply transitivity_application_beta.
Qed.
Definition transitivity_annotation : Term nat 14 :=
  transitivity_guard (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))
    (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))
    (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))).
Lemma transitivity_annotation_specialized q p0 p1 p2 p3 p4 p5 :
  replace (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))
    transitivity_annotation = transitivity_application_type q Nat.eqb.
Proof.
  unfold transitivity_annotation. rewrite replace_transitivity_guard.
  change (transitivity_guard (selector_type q) (Separation.predicate q)
    (RelationTables.relation_table q Nat.eqb) = transitivity_application_type q Nat.eqb).
  unfold transitivity_guard, transitivity_application_type.
  assert (HF : forall n, @shift nat n (selector_type q) = selector_type q).
  { intro n. unfold shift. apply rename_selector_type. }
  rewrite !HF.
  assert (HC : forall c : closed_term, shift c = @lift_closed 1 c).
  { intro c. rewrite lift_closed_shift, lift_closed_zero. reflexivity. }
  rewrite !HC, <- !lift_closed_shift. reflexivity.
Qed.
Theorem transitivity_prefix_matches_source body :
  assemble (npis (firstn 15 observation_fields) body) [] =
  option_map (fun B => telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation
      (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation B))))))))
    (assemble body [106;105;104;103;102;101;100;7;6;5;4;3;2;1;0]).
Proof.
  cbn [npis firstn observation_fields fold_right fst snd assemble lookup Nat.eqb].
  destruct (assemble body [106;105;104;103;102;101;100;7;6;5;4;3;2;1;0]); reflexivity.
Qed.
Theorem transitivity_specialization q f (B : Term nat 15) : 0 < q ->
  Typed ε f (telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation
      (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation B)))))))) ->
  exists p0 p1 p2 p3 p4 p5 p6,
    Typed ε p6 (replace (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))
      transitivity_annotation) /\
    Typed ε (app (app (app (app (app (app (app (table_apply f (data_arguments q)) p0) p1) p2) p3) p4) p5) p6)
      (replace (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))) B).
Proof.
  intros Hq Hf.
  destruct (symmetry_specialization q f _ Hq Hf) as [p0 [p1 [p2 [p3 [p4 [p5 [Hp5 Hf6]]]]]]].
  assert (Hr : forall i j k, i < q -> j < q -> k < q ->
    Nat.eqb i j = true -> Nat.eqb j k = true -> Nat.eqb i k = true).
  { intros i j k Hi Hj Hk Hij Hjk. apply Nat.eqb_eq in Hij, Hjk.
    apply Nat.eqb_eq. congruence. }
  destruct (transitivity_application_certificate q Nat.eqb Hq Hr) as [p6 Hp6].
  rewrite <- (transitivity_annotation_specialized q p0 p1 p2 p3 p4 p5) in Hp6.
  exists p0, p1, p2, p3, p4, p5, p6. split; [exact Hp6 |].
  rewrite replace_product in Hf6. pose proof (tApp Hf6 Hp6) as Hf7.
  rewrite substitute_transpose in Hf7. exact Hf7.
Qed.
Definition unary_congruence_guard {n} (X D R op : Term nat n) :=
  Π X (Arrow (app (shift D) V0)
    (Π (shift X) (Arrow (app (shift (shift D)) V0)
      (Arrow (Neg (app (app (shift (shift R)) (shift V0)) V0))
        (Neg (app (app (shift (shift R)) (app (shift (shift op)) (shift V0)))
          (app (shift (shift op)) V0))))))).
Lemma replace_unary_congruence_guard {m n} (f : Fin m -> Term nat n) X D R op :
  replace f (unary_congruence_guard X D R op) =
  unary_congruence_guard (replace f X) (replace f D) (replace f R) (replace f op).
Proof.
  unfold unary_congruence_guard, Neg.
  repeat first [rewrite replace_product |rewrite replace_arrow |
    rewrite replace_application |rewrite replace_shift |rewrite replace_lift_closed].
  reflexivity.
Qed.
Definition unary_congruence_application_type q op : closed_term :=
  Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
    (Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
      (Arrow (Neg (app (app (lift_closed (RelationTables.relation_table q Nat.eqb)) (shift V0)) V0))
        (Neg (app (app (lift_closed (RelationTables.relation_table q Nat.eqb))
          (app (lift_closed op) (shift V0))) (app (lift_closed op) V0))))))).
Lemma unary_congruence_application_typed q op : 0 < q ->
  Typed ε op (Arrow (selector_type q) (selector_type q)) ->
  Typed ε (unary_congruence_application_type q op) (𝓤 5).
Proof.
  intros Hq Hop. destruct q as [|q]; [lia |]. unfold unary_congruence_application_type.
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 5).
  - apply Separation.predicate_application; [exact Hq |apply GuardedFiniteLaws.selector_newest].
  - apply (tPi (b:=5) (selector_type_formation (S q) _)).
    apply (arrow_formation _ _ _ 4 3).
    + apply Separation.predicate_application; [exact Hq |apply GuardedFiniteLaws.selector_newest].
    + apply (arrow_formation _ _ _ 2 2).
      * apply neg_formation, relation_application_typed;
          repeat apply GuardedFiniteLaws.selector_weaken; apply GuardedFiniteLaws.selector_newest.
      * apply neg_formation, relation_application_typed;
          apply FiniteUnaryCongruence.output_typed; [exact Hop | |exact Hop |];
          repeat apply GuardedFiniteLaws.selector_weaken; apply GuardedFiniteLaws.selector_newest.
Qed.
Lemma unary_congruence_application_beta q op :
  unary_congruence_application_type q op =ᵝ FiniteUnaryCongruence.expanded_type q op.
Proof.
  unfold unary_congruence_application_type, FiniteUnaryCongruence.expanded_type,
    FiniteUnaryCongruence.body, FiniteUnaryCongruence.output.
  do 2 (apply beta_pi; [reflexivity |]; apply Unary.arrow_beta;
    [apply Separation.predicate_beta |]).
  apply Unary.arrow_beta; apply FiniteUp.neg_beta, relation_application_beta.
Qed.
Theorem successor_application_certificate q : 0 < q ->
  Realizes (unary_congruence_application_type q (capped_successor q)).
Proof.
  intro Hq. eapply FiniteUp.inhabited_conversion.
  - exact (FiniteUnaryCongruence.successor_congruence_realized q Hq).
  - apply unary_congruence_application_typed; [exact Hq |apply capped_successor_typed].
  - symmetry. apply unary_congruence_application_beta.
Qed.
Definition successor_annotation : Term nat 15 :=
  unary_congruence_guard (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))
    (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))).
Lemma successor_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 :
  replace (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))) successor_annotation =
  unary_congruence_application_type q (capped_successor q).
Proof.
  unfold successor_annotation. rewrite replace_unary_congruence_guard.
  change (unary_congruence_guard (selector_type q) (Separation.predicate q)
    (RelationTables.relation_table q Nat.eqb) (capped_successor q) =
    unary_congruence_application_type q (capped_successor q)).
  unfold unary_congruence_guard, unary_congruence_application_type.
  assert (HF : @shift nat 0 (selector_type q) = selector_type q).
  { unfold shift. apply rename_selector_type. }
  rewrite HF.
  assert (HC : forall c : closed_term, shift c = @lift_closed 1 c).
  { intro c. rewrite lift_closed_shift, lift_closed_zero. reflexivity. }
  rewrite !HC, <- !lift_closed_shift. reflexivity.
Qed.
Theorem successor_prefix_matches_source body :
  assemble (npis (firstn 16 observation_fields) body) [] =
  option_map (fun B => telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation B)))))))))
    (assemble body [107;106;105;104;103;102;101;100;7;6;5;4;3;2;1;0]).
Proof.
  cbn [npis firstn observation_fields fold_right fst snd assemble lookup Nat.eqb].
  destruct (assemble body [107;106;105;104;103;102;101;100;7;6;5;4;3;2;1;0]); reflexivity.
Qed.
Theorem successor_specialization q f (B : Term nat 16) : 0 < q ->
  Typed ε f (telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation B))))))))) ->
  exists p0 p1 p2 p3 p4 p5 p6 p7,
    Typed ε p7 (replace (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))) successor_annotation) /\
    Typed ε (app (app (app (app (app (app (app (app (table_apply f (data_arguments q)) p0) p1) p2) p3) p4) p5) p6) p7)
      (replace (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))) B).
Proof.
  intros Hq Hf.
  destruct (transitivity_specialization q f _ Hq Hf)
    as [p0 [p1 [p2 [p3 [p4 [p5 [p6 [Hp6 Hf7]]]]]]]].
  destruct (successor_application_certificate q Hq) as [p7 Hp7].
  rewrite <- (successor_annotation_specialized q p0 p1 p2 p3 p4 p5 p6) in Hp7.
  exists p0, p1, p2, p3, p4, p5, p6, p7. split; [exact Hp7 |].
  rewrite replace_product in Hf7. pose proof (tApp Hf7 Hp7) as Hf8.
  rewrite substitute_transpose in Hf8. exact Hf8.
Qed.
End FiniteDomainPrefix.
