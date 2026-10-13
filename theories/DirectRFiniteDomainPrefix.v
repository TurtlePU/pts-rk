(** Typed observation-prefix assembly through the four domain certificates. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting DirectRCodes DirectRKernel
  DirectRStructural DirectRLogic DirectRFiniteTables DirectRBinaryTables
  DirectRSeparation DirectRTelescopeArguments DirectRFiniteData DirectRFiniteBinaryDomain
  DirectRRelationTables DirectRFunctionalFiniteLaws DirectRFiniteUp DirectRUnary
  DirectRGuardedFiniteLaws.
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
End FiniteDomainPrefix.
