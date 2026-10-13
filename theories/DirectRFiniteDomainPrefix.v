(** Typed observation-prefix assembly through the four domain certificates. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting DirectRCodes DirectRKernel
  DirectRStructural DirectRLogic DirectRFiniteTables DirectRBinaryTables
  DirectRSeparation DirectRTelescopeArguments DirectRFiniteData DirectRFiniteBinaryDomain
  DirectRRelationTables DirectRFunctionalFiniteLaws DirectRFiniteUp DirectRUnary
  DirectRGuardedFiniteLaws DirectRFiniteTransitivity DirectRFiniteUnaryCongruence
  DirectRFiniteBinaryCongruence DirectRFiniteCongruence DirectRFiniteExpressions
  DirectRFiniteZeroLaws DirectRFiniteRecursionLaws DirectRFiniteOrderLaws.
Import ListNotations.
Module FiniteDomainPrefix.
Import Codes Core Structural NegativeLogic FiniteTables BinaryTables TelescopeArguments FiniteData.
Lemma prefix_option_map_compose {A B C} (f : B -> C) (g : A -> B) x :
  option_map f (option_map g x) = option_map (fun y => f (g y)) x.
Proof. destruct x; reflexivity. Qed.
Lemma assemble_prefix_step name A rest body env (T : Term nat (length env)) :
  assemble A env = Some T ->
  assemble (npis ((name,A)::rest) body) env =
  option_map (fun B => Π T B) (assemble (npis rest body) (name::env)).
Proof.
  intro H.
  change ((match assemble A env with
    | Some A' => match assemble (npis rest body) (name::env) with
      | Some B => Some (Π A' B) | None => None end
    | None => None end) =
    option_map (fun B => Π T B) (assemble (npis rest body) (name::env))).
  rewrite H. destruct (assemble (npis rest body) (name::env)); reflexivity.
Qed.
Lemma assemble_prefix_congr {l} name A rest body env
  (T : Term nat (length env)) (F : Term nat l -> Term nat (length (name::env))) result :
  assemble A env = Some T ->
  assemble (npis rest body) (name::env) = option_map F result ->
  assemble (npis ((name,A)::rest) body) env =
    option_map (fun B => Π T (F B)) result.
Proof.
  intros HA HB. rewrite (assemble_prefix_step name A rest body env T HA), HB.
  apply prefix_option_map_compose.
Qed.
Lemma prefix_option_map_id {A} (x : option A) : x = option_map (fun y => y) x.
Proof. destruct x; reflexivity. Qed.
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
  cbn [firstn observation_fields].
  repeat (eapply assemble_prefix_congr; [reflexivity |]).
  apply prefix_option_map_id.
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
  cbn [firstn observation_fields].
  repeat (eapply assemble_prefix_congr; [reflexivity |]).
  apply prefix_option_map_id.
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
  cbn [firstn observation_fields].
  repeat (eapply assemble_prefix_congr; [reflexivity |]).
  apply prefix_option_map_id.
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
  cbn [firstn observation_fields].
  repeat (eapply assemble_prefix_congr; [reflexivity |]).
  apply prefix_option_map_id.
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
  cbn [firstn observation_fields].
  repeat (eapply assemble_prefix_congr; [reflexivity |]).
  apply prefix_option_map_id.
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
Definition binary_congruence_guard {n} (X D R op : Term nat n) :=
  (Π X (Arrow (app (shift D) V0)
      (Π (shift X) (Arrow (app (shift (shift D)) V0)
      (Π (shift (shift X)) (Arrow (app (shift (shift (shift D))) V0)
      (Π (shift (shift (shift X))) (Arrow (app (shift (shift (shift (shift D)))) V0)
      (Arrow (Neg (app (app (shift (shift (shift (shift R)))) (shift (shift (shift V0)))) (shift (shift V0)))) (Arrow (Neg (app (app (shift (shift (shift (shift R)))) (shift V0)) V0)) (Neg (app (app (shift (shift (shift (shift R)))) (app (app (shift (shift (shift (shift op)))) (shift (shift (shift V0)))) (shift V0))) (app (app (shift (shift (shift (shift op)))) (shift (shift V0))) V0))))))))))))).
Lemma replace_binary_congruence_guard {m n} (f : Fin m -> Term nat n) X D R op :
  replace f (binary_congruence_guard X D R op) =
  binary_congruence_guard (replace f X) (replace f D) (replace f R) (replace f op).
Proof.
  unfold binary_congruence_guard, Neg.
  repeat first [rewrite replace_product |rewrite replace_arrow |
    rewrite replace_application |rewrite replace_shift |rewrite replace_lift_closed].
  reflexivity.
Qed.
Definition binary_congruence_application_type q op : closed_term :=
  (Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
      (Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
      (Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
      (Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
      (Arrow (Neg (app (app (lift_closed (RelationTables.relation_table q Nat.eqb)) (shift (shift (shift V0)))) (shift (shift V0)))) (Arrow (Neg (app (app (lift_closed (RelationTables.relation_table q Nat.eqb)) (shift V0)) V0)) (Neg (app (app (lift_closed (RelationTables.relation_table q Nat.eqb)) (app (app (lift_closed op) (shift (shift (shift V0)))) (shift V0))) (app (app (lift_closed op) (shift (shift V0))) V0))))))))))))).
Lemma binary_congruence_application_typed q op : 0 < q ->
  Typed ε op (FiniteBinaryCongruence.operation_type q) ->
  Typed ε (binary_congruence_application_type q op) (𝓤 5).
Proof.
  intros Hq Hop. destruct q as [|q]; [lia |]. unfold binary_congruence_application_type.
  do 3 (apply (tPi (b:=5) (selector_type_formation (S q) _));
    apply (arrow_formation _ _ _ 4 5);
    [apply Separation.predicate_application; [exact Hq |apply GuardedFiniteLaws.selector_newest] |]).
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 3).
  - apply Separation.predicate_application; [exact Hq |apply GuardedFiniteLaws.selector_newest].
  - apply (arrow_formation _ _ _ 2 3).
    + apply neg_formation, relation_application_typed;
        repeat apply GuardedFiniteLaws.selector_weaken; apply GuardedFiniteLaws.selector_newest.
    + apply (arrow_formation _ _ _ 2 2).
      * apply neg_formation, relation_application_typed;
          repeat apply GuardedFiniteLaws.selector_weaken; apply GuardedFiniteLaws.selector_newest.
      * apply neg_formation, relation_application_typed;
          apply FiniteBinaryCongruence.output_typed; [exact Hop | | |exact Hop | |];
          repeat apply GuardedFiniteLaws.selector_weaken; apply GuardedFiniteLaws.selector_newest.
Qed.
Lemma binary_congruence_application_beta q op :
  binary_congruence_application_type q op =ᵝ FiniteBinaryCongruence.expanded_type q op.
Proof.
  unfold binary_congruence_application_type, FiniteBinaryCongruence.expanded_type,
    FiniteBinaryCongruence.body, FiniteBinaryCongruence.output.
  do 4 (apply beta_pi; [reflexivity |]; apply Unary.arrow_beta;
    [apply Separation.predicate_beta |]).
  apply Unary.arrow_beta; [apply FiniteUp.neg_beta, relation_application_beta |].
  apply Unary.arrow_beta; apply FiniteUp.neg_beta, relation_application_beta.
Qed.
Theorem addition_congruence_application_certificate q : 0 < q ->
  Realizes (binary_congruence_application_type q (capped_addition q)).
Proof.
  intro Hq. eapply FiniteUp.inhabited_conversion.
  - exact (FiniteBinaryCongruence.addition_congruence_realized q Hq).
  - apply binary_congruence_application_typed; [exact Hq |apply capped_addition_typed].
  - symmetry. apply binary_congruence_application_beta.
Qed.
Theorem multiplication_congruence_application_certificate q : 0 < q ->
  Realizes (binary_congruence_application_type q (capped_multiplication q)).
Proof.
  intro Hq. eapply FiniteUp.inhabited_conversion.
  - exact (FiniteBinaryCongruence.multiplication_congruence_realized q Hq).
  - apply binary_congruence_application_typed; [exact Hq |apply capped_multiplication_typed].
  - symmetry. apply binary_congruence_application_beta.
Qed.
Definition addition_congruence_annotation : Term nat 16 :=
  binary_congruence_guard (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))).
Lemma addition_congruence_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 :
  replace (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))) addition_congruence_annotation =
  binary_congruence_application_type q (capped_addition q).
Proof.
  unfold addition_congruence_annotation. rewrite replace_binary_congruence_guard.
  change (binary_congruence_guard (selector_type q) (Separation.predicate q)
    (RelationTables.relation_table q Nat.eqb) (capped_addition q) =
    binary_congruence_application_type q (capped_addition q)).
  unfold binary_congruence_guard, binary_congruence_application_type.
  assert (HF : forall n, @shift nat n (selector_type q) = selector_type q).
  { intro n. unfold shift. apply rename_selector_type. }
  rewrite !HF.
  assert (HC : forall c : closed_term, shift c = @lift_closed 1 c).
  { intro c. rewrite lift_closed_shift, lift_closed_zero. reflexivity. }
  rewrite !HC, <- !lift_closed_shift. reflexivity.
Qed.
Theorem addition_congruence_prefix_matches_source body :
  assemble (npis (firstn 17 observation_fields) body) [] =
  option_map (fun B => telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation B))))))))))
    (assemble body [108;107;106;105;104;103;102;101;100;7;6;5;4;3;2;1;0]).
Proof.
  cbn [firstn observation_fields].
  repeat (eapply assemble_prefix_congr; [reflexivity |]).
  apply prefix_option_map_id.
Qed.
Theorem addition_congruence_specialization q f (B : Term nat 17) : 0 < q ->
  Typed ε f (telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation B)))))))))) ->
  exists p0 p1 p2 p3 p4 p5 p6 p7 p8,
    Typed ε p8 (replace (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))) addition_congruence_annotation) /\
    Typed ε (app (app (app (app (app (app (app (app (app (table_apply f (data_arguments q)) p0) p1) p2) p3) p4) p5) p6) p7) p8) (replace (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))) B).
Proof.
  intros Hq Hf.
  destruct (successor_specialization q f _ Hq Hf)
    as [p0 [p1 [p2 [p3 [p4 [p5 [p6 [p7 [Hp Hfnext]]]]]]]]].
  destruct (addition_congruence_application_certificate q Hq) as [p8 Hpnew].
  rewrite <- (addition_congruence_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7) in Hpnew.
  exists p0, p1, p2, p3, p4, p5, p6, p7, p8. split; [exact Hpnew |].
  rewrite replace_product in Hfnext. pose proof (tApp Hfnext Hpnew) as Hfinal.
  rewrite substitute_transpose in Hfinal. exact Hfinal.
Qed.
Definition multiplication_congruence_annotation : Term nat 17 :=
  binary_congruence_guard (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))).
Lemma multiplication_congruence_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 p8 :
  replace (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))) multiplication_congruence_annotation =
  binary_congruence_application_type q (capped_multiplication q).
Proof.
  unfold multiplication_congruence_annotation. rewrite replace_binary_congruence_guard.
  change (binary_congruence_guard (selector_type q) (Separation.predicate q)
    (RelationTables.relation_table q Nat.eqb) (capped_multiplication q) =
    binary_congruence_application_type q (capped_multiplication q)).
  unfold binary_congruence_guard, binary_congruence_application_type.
  assert (HF : forall n, @shift nat n (selector_type q) = selector_type q).
  { intro n. unfold shift. apply rename_selector_type. }
  rewrite !HF.
  assert (HC : forall c : closed_term, shift c = @lift_closed 1 c).
  { intro c. rewrite lift_closed_shift, lift_closed_zero. reflexivity. }
  rewrite !HC, <- !lift_closed_shift. reflexivity.
Qed.
Theorem multiplication_congruence_prefix_matches_source body :
  assemble (npis (firstn 18 observation_fields) body) [] =
  option_map (fun B => telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation B)))))))))))
    (assemble body [109;108;107;106;105;104;103;102;101;100;7;6;5;4;3;2;1;0]).
Proof.
  cbn [firstn observation_fields].
  repeat (eapply assemble_prefix_congr; [reflexivity |]).
  apply prefix_option_map_id.
Qed.
Theorem multiplication_congruence_specialization q f (B : Term nat 18) : 0 < q ->
  Typed ε f (telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation B))))))))))) ->
  exists p0 p1 p2 p3 p4 p5 p6 p7 p8 p9,
    Typed ε p9 (replace (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))) multiplication_congruence_annotation) /\
    Typed ε (app (app (app (app (app (app (app (app (app (app (table_apply f (data_arguments q)) p0) p1) p2) p3) p4) p5) p6) p7) p8) p9) (replace (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))))) B).
Proof.
  intros Hq Hf.
  destruct (addition_congruence_specialization q f _ Hq Hf)
    as [p0 [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [Hp Hfnext]]]]]]]]]].
  destruct (multiplication_congruence_application_certificate q Hq) as [p9 Hpnew].
  rewrite <- (multiplication_congruence_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 p8) in Hpnew.
  exists p0, p1, p2, p3, p4, p5, p6, p7, p8, p9. split; [exact Hpnew |].
  rewrite replace_product in Hfnext. pose proof (tApp Hfnext Hpnew) as Hfinal.
  rewrite substitute_transpose in Hfinal. exact Hfinal.
Qed.
Definition order_congruence_guard {n} (X D R C : Term nat n) :=
  (Π X (Arrow (app (shift D) V0)
      (Π (shift X) (Arrow (app (shift (shift D)) V0)
      (Π (shift (shift X)) (Arrow (app (shift (shift (shift D))) V0)
      (Π (shift (shift (shift X))) (Arrow (app (shift (shift (shift (shift D)))) V0)
      (Arrow (Neg (app (app (shift (shift (shift (shift R)))) (shift (shift (shift V0)))) (shift (shift V0)))) (Arrow (Neg (app (app (shift (shift (shift (shift R)))) (shift V0)) V0)) (Arrow (Neg (app (app (shift (shift (shift (shift C)))) (shift (shift (shift V0)))) (shift V0))) (Neg (app (app (shift (shift (shift (shift C)))) (shift (shift V0))) V0))))))))))))).
Lemma replace_order_congruence_guard {m n} (f : Fin m -> Term nat n) X D R C :
  replace f (order_congruence_guard X D R C) =
  order_congruence_guard (replace f X) (replace f D) (replace f R) (replace f C).
Proof.
  unfold order_congruence_guard, Neg.
  repeat first [rewrite replace_product |rewrite replace_arrow |
    rewrite replace_application |rewrite replace_shift |rewrite replace_lift_closed].
  reflexivity.
Qed.
Definition order_congruence_application_type q : closed_term :=
  (Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
      (Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
      (Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
      (Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
      (Arrow (Neg (app (app (lift_closed (RelationTables.relation_table q Nat.eqb)) (shift (shift (shift V0)))) (shift (shift V0)))) (Arrow (Neg (app (app (lift_closed (RelationTables.relation_table q Nat.eqb)) (shift V0)) V0)) (Arrow (Neg (app (app (lift_closed (RelationTables.relation_table q Nat.leb)) (shift (shift (shift V0)))) (shift V0))) (Neg (app (app (lift_closed (RelationTables.relation_table q Nat.leb)) (shift (shift V0))) V0))))))))))))).
Lemma order_congruence_application_typed q : 0 < q ->
  Typed ε (order_congruence_application_type q) (𝓤 5).
Proof.
  intro Hq. destruct q as [|q]; [lia |]. unfold order_congruence_application_type.
  do 3 (apply (tPi (b:=5) (selector_type_formation (S q) _));
    apply (arrow_formation _ _ _ 4 5);
    [apply Separation.predicate_application; [exact Hq |apply GuardedFiniteLaws.selector_newest] |]).
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 3).
  - apply Separation.predicate_application; [exact Hq |apply GuardedFiniteLaws.selector_newest].
  - do 2 (apply (arrow_formation _ _ _ 2 3);
      [apply neg_formation, relation_application_typed;
        repeat apply GuardedFiniteLaws.selector_weaken; apply GuardedFiniteLaws.selector_newest |]).
    apply (arrow_formation _ _ _ 2 2); apply neg_formation, relation_application_typed;
      repeat apply GuardedFiniteLaws.selector_weaken; apply GuardedFiniteLaws.selector_newest.
Qed.
Lemma order_congruence_application_beta q :
  order_congruence_application_type q =ᵝ FiniteCongruence.expanded_type q Nat.leb.
Proof.
  unfold order_congruence_application_type, FiniteCongruence.expanded_type, FiniteCongruence.body.
  do 4 (apply beta_pi; [reflexivity |]; apply Unary.arrow_beta;
    [apply Separation.predicate_beta |]).
  do 2 (apply Unary.arrow_beta; [apply FiniteUp.neg_beta, relation_application_beta |]).
  apply Unary.arrow_beta; apply FiniteUp.neg_beta, relation_application_beta.
Qed.
Theorem order_congruence_application_certificate q : 0 < q ->
  Realizes (order_congruence_application_type q).
Proof.
  intro Hq. eapply FiniteUp.inhabited_conversion.
  - exact (FiniteCongruence.order_congruence_realized q Hq).
  - apply order_congruence_application_typed; exact Hq.
  - symmetry. apply order_congruence_application_beta.
Qed.
Theorem order_reflexivity_application_certificate q : 0 < q ->
  Realizes (reflexivity_application_type q Nat.leb).
Proof.
  intro Hq. apply reflexivity_application_certificate; [exact Hq |].
  intros i Hi. apply Nat.leb_refl.
Qed.
Theorem order_transitivity_application_certificate q : 0 < q ->
  Realizes (transitivity_application_type q Nat.leb).
Proof.
  intro Hq. apply transitivity_application_certificate; [exact Hq |].
  intros i j k Hi Hj Hk Hij Hjk. apply Nat.leb_le in Hij, Hjk.
  apply Nat.leb_le. lia.
Qed.
Definition order_congruence_annotation : Term nat 18 :=
  order_congruence_guard (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))).
Lemma order_congruence_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 :
  replace (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))))) order_congruence_annotation = order_congruence_application_type q.
Proof.
  unfold order_congruence_annotation. rewrite replace_order_congruence_guard.
  change (order_congruence_guard (selector_type q) (Separation.predicate q)
    (RelationTables.relation_table q Nat.eqb) (RelationTables.relation_table q Nat.leb) = order_congruence_application_type q).
  unfold order_congruence_guard, order_congruence_application_type.
  assert (HF : forall n, @shift nat n (selector_type q) = selector_type q).
  { intro n. unfold shift. apply rename_selector_type. }
  rewrite !HF.
  assert (HC : forall c : closed_term, shift c = @lift_closed 1 c).
  { intro c. rewrite lift_closed_shift, lift_closed_zero. reflexivity. }
  rewrite !HC, <- !lift_closed_shift. reflexivity.
Qed.
Theorem order_congruence_prefix_matches_source body :
  assemble (npis (firstn 19 observation_fields) body) [] =
  option_map (fun B => telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation (Π order_congruence_annotation B))))))))))))
    (assemble body [110;109;108;107;106;105;104;103;102;101;100;7;6;5;4;3;2;1;0]).
Proof.
  cbn [firstn observation_fields].
  repeat (eapply assemble_prefix_congr; [reflexivity |]).
  apply prefix_option_map_id.
Qed.
Theorem order_congruence_specialization q f (B : Term nat 19) : 0 < q ->
  Typed ε f (telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation (Π order_congruence_annotation B)))))))))))) ->
  exists p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10,
    Typed ε p10 (replace (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))))) order_congruence_annotation) /\
    Typed ε (app (app (app (app (app (app (app (app (app (app (app (table_apply f (data_arguments q)) p0) p1) p2) p3) p4) p5) p6) p7) p8) p9) p10) (replace (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))))) B).
Proof.
  intros Hq Hf.
  destruct (multiplication_congruence_specialization q f _ Hq Hf)
    as [p0 [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [Hp Hfnext]]]]]]]]]]].
  destruct (order_congruence_application_certificate q Hq) as [p10 Hpnew].
  rewrite <- (order_congruence_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 p8 p9) in Hpnew.
  exists p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10. split; [exact Hpnew |].
  rewrite replace_product in Hfnext. pose proof (tApp Hfnext Hpnew) as Hfinal.
  rewrite substitute_transpose in Hfinal. exact Hfinal.
Qed.
Definition order_reflexivity_annotation : Term nat 19 :=
  reflexivity_guard (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))).
Lemma order_reflexivity_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 :
  replace (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))))) order_reflexivity_annotation = reflexivity_application_type q Nat.leb.
Proof.
  unfold order_reflexivity_annotation. rewrite replace_reflexivity_guard.
  change (reflexivity_guard (selector_type q) (Separation.predicate q)
    (RelationTables.relation_table q Nat.leb) = reflexivity_application_type q Nat.leb).
  unfold reflexivity_guard, reflexivity_application_type.
  rewrite !lift_closed_shift, !lift_closed_zero. reflexivity.
Qed.
Theorem order_reflexivity_prefix_matches_source body :
  assemble (npis (firstn 20 observation_fields) body) [] =
  option_map (fun B => telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation (Π order_congruence_annotation (Π order_reflexivity_annotation B)))))))))))))
    (assemble body [111;110;109;108;107;106;105;104;103;102;101;100;7;6;5;4;3;2;1;0]).
Proof.
  cbn [firstn observation_fields].
  repeat (eapply assemble_prefix_congr; [reflexivity |]).
  apply prefix_option_map_id.
Qed.
Theorem order_reflexivity_specialization q f (B : Term nat 20) : 0 < q ->
  Typed ε f (telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation (Π order_congruence_annotation (Π order_reflexivity_annotation B))))))))))))) ->
  exists p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11,
    Typed ε p11 (replace (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))))) order_reflexivity_annotation) /\
    Typed ε (app (app (app (app (app (app (app (app (app (app (app (app (table_apply f (data_arguments q)) p0) p1) p2) p3) p4) p5) p6) p7) p8) p9) p10) p11) (replace (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))))))) B).
Proof.
  intros Hq Hf.
  destruct (order_congruence_specialization q f _ Hq Hf)
    as [p0 [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [Hp Hfnext]]]]]]]]]]]].
  destruct (order_reflexivity_application_certificate q Hq) as [p11 Hpnew].
  rewrite <- (order_reflexivity_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10) in Hpnew.
  exists p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11. split; [exact Hpnew |].
  rewrite replace_product in Hfnext. pose proof (tApp Hfnext Hpnew) as Hfinal.
  rewrite substitute_transpose in Hfinal. exact Hfinal.
Qed.
Definition order_transitivity_annotation : Term nat 20 :=
  transitivity_guard (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))).
Lemma order_transitivity_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 :
  replace (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))))))) order_transitivity_annotation = transitivity_application_type q Nat.leb.
Proof.
  unfold order_transitivity_annotation. rewrite replace_transitivity_guard.
  change (transitivity_guard (selector_type q) (Separation.predicate q)
    (RelationTables.relation_table q Nat.leb) = transitivity_application_type q Nat.leb).
  unfold transitivity_guard, transitivity_application_type.
  assert (HF : forall n, @shift nat n (selector_type q) = selector_type q).
  { intro n. unfold shift. apply rename_selector_type. }
  rewrite !HF.
  assert (HC : forall c : closed_term, shift c = @lift_closed 1 c).
  { intro c. rewrite lift_closed_shift, lift_closed_zero. reflexivity. }
  rewrite !HC, <- !lift_closed_shift. reflexivity.
Qed.
Theorem order_transitivity_prefix_matches_source body :
  assemble (npis (firstn 21 observation_fields) body) [] =
  option_map (fun B => telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation (Π order_congruence_annotation (Π order_reflexivity_annotation (Π order_transitivity_annotation B))))))))))))))
    (assemble body [112;111;110;109;108;107;106;105;104;103;102;101;100;7;6;5;4;3;2;1;0]).
Proof.
  cbn [firstn observation_fields].
  repeat (eapply assemble_prefix_congr; [reflexivity |]).
  apply prefix_option_map_id.
Qed.
Theorem order_transitivity_specialization q f (B : Term nat 21) : 0 < q ->
  Typed ε f (telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation (Π order_congruence_annotation (Π order_reflexivity_annotation (Π order_transitivity_annotation B)))))))))))))) ->
  exists p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12,
    Typed ε p12 (replace (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))))))) order_transitivity_annotation) /\
    Typed ε (app (app (app (app (app (app (app (app (app (app (app (app (app (table_apply f (data_arguments q)) p0) p1) p2) p3) p4) p5) p6) p7) p8) p9) p10) p11) p12) (replace (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))))))) B).
Proof.
  intros Hq Hf.
  destruct (order_reflexivity_specialization q f _ Hq Hf)
    as [p0 [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [Hp Hfnext]]]]]]]]]]]]].
  destruct (order_transitivity_application_certificate q Hq) as [p12 Hpnew].
  rewrite <- (order_transitivity_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11) in Hpnew.
  exists p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12. split; [exact Hpnew |].
  rewrite replace_product in Hfnext. pose proof (tApp Hfnext Hpnew) as Hfinal.
  rewrite substitute_transpose in Hfinal. exact Hfinal.
Qed.
Definition expression_application_atom {n} q r l h (u v : Term nat n) :=
  Neg (app (app (lift_closed (RelationTables.relation_table q r))
    (FiniteExpressions.denote q l u v)) (FiniteExpressions.denote q h u v)).
Lemma expression_application_atom_typed {n} (Γ : Ctx nat n) q r l h u v :
  Typed Γ u (selector_type q) -> Typed Γ v (selector_type q) ->
  Typed Γ (expression_application_atom q r l h u v) (𝓤 2).
Proof.
  intros Hu Hv. apply neg_formation, relation_application_typed;
    apply FiniteExpressions.denote_typed; assumption.
Qed.
Lemma expression_application_atom_beta {n} q r l h (u v : Term nat n) :
  expression_application_atom q r l h u v =ᵝ
  Neg (RelationTables.relation_at q r
    (FiniteExpressions.denote q l u v) (FiniteExpressions.denote q h u v)).
Proof. apply FiniteUp.neg_beta, relation_application_beta. Qed.
Definition addition_zero_guard {n} (X z s a m D R : Term nat n) :=
  (Π X (Arrow (app (shift D) V0)
      (Neg (app (app (shift R) (app (app (shift a) (shift z)) V0)) V0)))).
Lemma replace_addition_zero_guard {j n} (f : Fin j -> Term nat n) X z s a m D R :
  replace f (addition_zero_guard X z s a m D R) =
  addition_zero_guard (replace f X) (replace f z) (replace f s) (replace f a)
    (replace f m) (replace f D) (replace f R).
Proof.
  unfold addition_zero_guard, Neg.
  repeat first [rewrite replace_product |rewrite replace_arrow |
    rewrite replace_application |rewrite replace_shift |rewrite replace_lift_closed].
  reflexivity.
Qed.
Definition addition_zero_application_type q : closed_term :=
  (Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
      (expression_application_atom q Nat.eqb (FiniteExpressions.addition FiniteExpressions.zero FiniteExpressions.first) FiniteExpressions.first V0 V0))).
Lemma addition_zero_application_typed q : 0 < q ->
  Typed ε (addition_zero_application_type q) (𝓤 5).
Proof.
  intro Hq. destruct q as [|q]; [lia |]. unfold addition_zero_application_type.

  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 2).
  - apply Separation.predicate_application; [exact Hq |apply GuardedFiniteLaws.selector_newest].
  - apply expression_application_atom_typed;
      repeat apply GuardedFiniteLaws.selector_weaken; apply GuardedFiniteLaws.selector_newest.
Qed.
Lemma addition_zero_application_beta q :
  addition_zero_application_type q =ᵝ FiniteZeroLaws.expanded_type q (capped_addition q) false false.
Proof.
  unfold addition_zero_application_type, FiniteZeroLaws.expanded_type, FiniteZeroLaws.body.
  do 1 (apply beta_pi; [reflexivity |]; apply Unary.arrow_beta;
    [apply Separation.predicate_beta |]).
  apply FiniteUp.neg_beta.
  unfold expression_application_atom, FiniteZeroLaws.lhs, FiniteZeroLaws.argument, FiniteBinaryCongruence.output. cbn [negb FiniteExpressions.denote].
  apply relation_application_beta.
Qed.
Theorem addition_zero_application_certificate q : 0 < q ->
  Realizes (addition_zero_application_type q).
Proof.
  intro Hq. eapply FiniteUp.inhabited_conversion.
  - exact (FiniteZeroLaws.addition_zero_realized q Hq).
  - apply addition_zero_application_typed; exact Hq.
  - symmetry. apply addition_zero_application_beta.
Qed.
Definition addition_zero_annotation : Term nat 21 :=
  addition_zero_guard (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))).
Lemma addition_zero_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 :
  replace (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))))))) addition_zero_annotation = addition_zero_application_type q.
Proof.
  unfold addition_zero_annotation. rewrite replace_addition_zero_guard.
  change (addition_zero_guard (selector_type q) (point q 0) (capped_successor q)
    (capped_addition q) (capped_multiplication q) (Separation.predicate q)
    (RelationTables.relation_table q Nat.eqb) = addition_zero_application_type q).
  unfold addition_zero_guard, addition_zero_application_type, expression_application_atom.
  cbn [FiniteExpressions.denote].

  assert (HC : forall c : closed_term, shift c = @lift_closed 1 c).
  { intro c. rewrite lift_closed_shift, lift_closed_zero. reflexivity. }
  rewrite !HC, <- ?lift_closed_shift, <- ?lift_closed_shift. reflexivity.
Qed.
Theorem addition_zero_prefix_matches_source body :
  assemble (npis (firstn 22 observation_fields) body) [] =
  option_map (fun B => telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation (Π order_congruence_annotation (Π order_reflexivity_annotation (Π order_transitivity_annotation (Π addition_zero_annotation B)))))))))))))))
    (assemble body [113;112;111;110;109;108;107;106;105;104;103;102;101;100;7;6;5;4;3;2;1;0]).
Proof.
  cbn [firstn observation_fields].
  repeat (eapply assemble_prefix_congr; [reflexivity |]).
  apply prefix_option_map_id.
Qed.
Theorem addition_zero_specialization q f (B : Term nat 22) : 0 < q ->
  Typed ε f (telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation (Π order_congruence_annotation (Π order_reflexivity_annotation (Π order_transitivity_annotation (Π addition_zero_annotation B))))))))))))))) ->
  exists p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13,
    Typed ε p13 (replace (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))))))) addition_zero_annotation) /\
    Typed ε (app (app (app (app (app (app (app (app (app (app (app (app (app (app (table_apply f (data_arguments q)) p0) p1) p2) p3) p4) p5) p6) p7) p8) p9) p10) p11) p12) p13) (replace (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))))))))) B).
Proof.
  intros Hq Hf.
  destruct (order_transitivity_specialization q f _ Hq Hf)
    as [p0 [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [Hp Hfnext]]]]]]]]]]]]]].
  destruct (addition_zero_application_certificate q Hq) as [p13 Hpnew].
  rewrite <- (addition_zero_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12) in Hpnew.
  exists p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13. split; [exact Hpnew |].
  rewrite replace_product in Hfnext. pose proof (tApp Hfnext Hpnew) as Hfinal.
  rewrite substitute_transpose in Hfinal. exact Hfinal.
Qed.
Definition addition_successor_guard {n} (X z s a m D R : Term nat n) :=
  (Π X (Arrow (app (shift D) V0)
      (Π (shift X) (Arrow (app (shift (shift D)) V0)
      (Neg (app (app (shift (shift R)) (app (app (shift (shift a)) (app (shift (shift s)) (shift V0))) V0)) (app (shift (shift s)) (app (app (shift (shift a)) (shift V0)) V0)))))))).
Lemma replace_addition_successor_guard {j n} (f : Fin j -> Term nat n) X z s a m D R :
  replace f (addition_successor_guard X z s a m D R) =
  addition_successor_guard (replace f X) (replace f z) (replace f s) (replace f a)
    (replace f m) (replace f D) (replace f R).
Proof.
  unfold addition_successor_guard, Neg.
  repeat first [rewrite replace_product |rewrite replace_arrow |
    rewrite replace_application |rewrite replace_shift |rewrite replace_lift_closed].
  reflexivity.
Qed.
Definition addition_successor_application_type q : closed_term :=
  (Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
      (Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
      (expression_application_atom q Nat.eqb (FiniteExpressions.addition (FiniteExpressions.successor FiniteExpressions.first) FiniteExpressions.second) (FiniteExpressions.successor (FiniteExpressions.addition FiniteExpressions.first FiniteExpressions.second)) (shift V0) V0))))).
Lemma addition_successor_application_typed q : 0 < q ->
  Typed ε (addition_successor_application_type q) (𝓤 5).
Proof.
  intro Hq. destruct q as [|q]; [lia |]. unfold addition_successor_application_type.
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 5);
    [apply Separation.predicate_application; [exact Hq |apply GuardedFiniteLaws.selector_newest] |].
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 2).
  - apply Separation.predicate_application; [exact Hq |apply GuardedFiniteLaws.selector_newest].
  - apply expression_application_atom_typed;
      repeat apply GuardedFiniteLaws.selector_weaken; apply GuardedFiniteLaws.selector_newest.
Qed.
Lemma addition_successor_application_beta q :
  addition_successor_application_type q =ᵝ FiniteRecursionLaws.expanded_type q (FiniteExpressions.addition (FiniteExpressions.successor FiniteExpressions.first) FiniteExpressions.second) (FiniteExpressions.successor (FiniteExpressions.addition FiniteExpressions.first FiniteExpressions.second)).
Proof.
  unfold addition_successor_application_type, FiniteRecursionLaws.expanded_type, FiniteRecursionLaws.body.
  do 2 (apply beta_pi; [reflexivity |]; apply Unary.arrow_beta;
    [apply Separation.predicate_beta |]).
  apply FiniteUp.neg_beta.

  apply relation_application_beta.
Qed.
Theorem addition_successor_application_certificate q : 0 < q ->
  Realizes (addition_successor_application_type q).
Proof.
  intro Hq. eapply FiniteUp.inhabited_conversion.
  - exact (FiniteRecursionLaws.addition_successor_realized q Hq).
  - apply addition_successor_application_typed; exact Hq.
  - symmetry. apply addition_successor_application_beta.
Qed.
Definition addition_successor_annotation : Term nat 22 :=
  addition_successor_guard (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))).
Lemma addition_successor_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 :
  replace (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))))))))) addition_successor_annotation = addition_successor_application_type q.
Proof.
  unfold addition_successor_annotation. rewrite replace_addition_successor_guard.
  change (addition_successor_guard (selector_type q) (point q 0) (capped_successor q)
    (capped_addition q) (capped_multiplication q) (Separation.predicate q)
    (RelationTables.relation_table q Nat.eqb) = addition_successor_application_type q).
  unfold addition_successor_guard, addition_successor_application_type, expression_application_atom.
  cbn [FiniteExpressions.denote].
  assert (HF : forall n, @shift nat n (selector_type q) = selector_type q).
  { intro n. unfold shift. apply rename_selector_type. } rewrite !HF.
  assert (HC : forall c : closed_term, shift c = @lift_closed 1 c).
  { intro c. rewrite lift_closed_shift, lift_closed_zero. reflexivity. }
  rewrite !HC, <- ?lift_closed_shift, <- ?lift_closed_shift. reflexivity.
Qed.
Theorem addition_successor_prefix_matches_source body :
  assemble (npis (firstn 23 observation_fields) body) [] =
  option_map (fun B => telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation (Π order_congruence_annotation (Π order_reflexivity_annotation (Π order_transitivity_annotation (Π addition_zero_annotation (Π addition_successor_annotation B))))))))))))))))
    (assemble body [114;113;112;111;110;109;108;107;106;105;104;103;102;101;100;7;6;5;4;3;2;1;0]).
Proof.
  cbn [firstn observation_fields].
  repeat (eapply assemble_prefix_congr; [reflexivity |]).
  apply prefix_option_map_id.
Qed.
Theorem addition_successor_specialization q f (B : Term nat 23) : 0 < q ->
  Typed ε f (telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation (Π order_congruence_annotation (Π order_reflexivity_annotation (Π order_transitivity_annotation (Π addition_zero_annotation (Π addition_successor_annotation B)))))))))))))))) ->
  exists p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14,
    Typed ε p14 (replace (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))))))))) addition_successor_annotation) /\
    Typed ε (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (table_apply f (data_arguments q)) p0) p1) p2) p3) p4) p5) p6) p7) p8) p9) p10) p11) p12) p13) p14) (replace (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))))))))) B).
Proof.
  intros Hq Hf.
  destruct (addition_zero_specialization q f _ Hq Hf)
    as [p0 [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [Hp Hfnext]]]]]]]]]]]]]]].
  destruct (addition_successor_application_certificate q Hq) as [p14 Hpnew].
  rewrite <- (addition_successor_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13) in Hpnew.
  exists p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14. split; [exact Hpnew |].
  rewrite replace_product in Hfnext. pose proof (tApp Hfnext Hpnew) as Hfinal.
  rewrite substitute_transpose in Hfinal. exact Hfinal.
Qed.
Definition multiplication_zero_left_guard {n} (X z s a m D R : Term nat n) :=
  (Π X (Arrow (app (shift D) V0)
      (Neg (app (app (shift R) (app (app (shift m) (shift z)) V0)) (shift z))))).
Lemma replace_multiplication_zero_left_guard {j n} (f : Fin j -> Term nat n) X z s a m D R :
  replace f (multiplication_zero_left_guard X z s a m D R) =
  multiplication_zero_left_guard (replace f X) (replace f z) (replace f s) (replace f a)
    (replace f m) (replace f D) (replace f R).
Proof.
  unfold multiplication_zero_left_guard, Neg.
  repeat first [rewrite replace_product |rewrite replace_arrow |
    rewrite replace_application |rewrite replace_shift |rewrite replace_lift_closed].
  reflexivity.
Qed.
Definition multiplication_zero_left_application_type q : closed_term :=
  (Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
      (expression_application_atom q Nat.eqb (FiniteExpressions.multiplication FiniteExpressions.zero FiniteExpressions.first) FiniteExpressions.zero V0 V0))).
Lemma multiplication_zero_left_application_typed q : 0 < q ->
  Typed ε (multiplication_zero_left_application_type q) (𝓤 5).
Proof.
  intro Hq. destruct q as [|q]; [lia |]. unfold multiplication_zero_left_application_type.

  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 2).
  - apply Separation.predicate_application; [exact Hq |apply GuardedFiniteLaws.selector_newest].
  - apply expression_application_atom_typed;
      repeat apply GuardedFiniteLaws.selector_weaken; apply GuardedFiniteLaws.selector_newest.
Qed.
Lemma multiplication_zero_left_application_beta q :
  multiplication_zero_left_application_type q =ᵝ FiniteZeroLaws.expanded_type q (capped_multiplication q) false true.
Proof.
  unfold multiplication_zero_left_application_type, FiniteZeroLaws.expanded_type, FiniteZeroLaws.body.
  do 1 (apply beta_pi; [reflexivity |]; apply Unary.arrow_beta;
    [apply Separation.predicate_beta |]).
  apply FiniteUp.neg_beta.
  unfold expression_application_atom, FiniteZeroLaws.lhs, FiniteZeroLaws.argument, FiniteBinaryCongruence.output. cbn [negb FiniteExpressions.denote].
  apply relation_application_beta.
Qed.
Theorem multiplication_zero_left_application_certificate q : 0 < q ->
  Realizes (multiplication_zero_left_application_type q).
Proof.
  intro Hq. eapply FiniteUp.inhabited_conversion.
  - exact (FiniteZeroLaws.multiplication_zero_left_realized q Hq).
  - apply multiplication_zero_left_application_typed; exact Hq.
  - symmetry. apply multiplication_zero_left_application_beta.
Qed.
Definition multiplication_zero_left_annotation : Term nat 23 :=
  multiplication_zero_left_guard (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))).
Lemma multiplication_zero_left_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 :
  replace (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))))))))) multiplication_zero_left_annotation = multiplication_zero_left_application_type q.
Proof.
  unfold multiplication_zero_left_annotation. rewrite replace_multiplication_zero_left_guard.
  change (multiplication_zero_left_guard (selector_type q) (point q 0) (capped_successor q)
    (capped_addition q) (capped_multiplication q) (Separation.predicate q)
    (RelationTables.relation_table q Nat.eqb) = multiplication_zero_left_application_type q).
  unfold multiplication_zero_left_guard, multiplication_zero_left_application_type, expression_application_atom.
  cbn [FiniteExpressions.denote].

  assert (HC : forall c : closed_term, shift c = @lift_closed 1 c).
  { intro c. rewrite lift_closed_shift, lift_closed_zero. reflexivity. }
  rewrite !HC, <- ?lift_closed_shift, <- ?lift_closed_shift. reflexivity.
Qed.
Theorem multiplication_zero_left_prefix_matches_source body :
  assemble (npis (firstn 24 observation_fields) body) [] =
  option_map (fun B => telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation (Π order_congruence_annotation (Π order_reflexivity_annotation (Π order_transitivity_annotation (Π addition_zero_annotation (Π addition_successor_annotation (Π multiplication_zero_left_annotation B)))))))))))))))))
    (assemble body [115;114;113;112;111;110;109;108;107;106;105;104;103;102;101;100;7;6;5;4;3;2;1;0]).
Proof.
  cbn [firstn observation_fields].
  repeat (eapply assemble_prefix_congr; [reflexivity |]).
  apply prefix_option_map_id.
Qed.
Theorem multiplication_zero_left_specialization q f (B : Term nat 24) : 0 < q ->
  Typed ε f (telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation (Π order_congruence_annotation (Π order_reflexivity_annotation (Π order_transitivity_annotation (Π addition_zero_annotation (Π addition_successor_annotation (Π multiplication_zero_left_annotation B))))))))))))))))) ->
  exists p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15,
    Typed ε p15 (replace (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))))))))) multiplication_zero_left_annotation) /\
    Typed ε (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (table_apply f (data_arguments q)) p0) p1) p2) p3) p4) p5) p6) p7) p8) p9) p10) p11) p12) p13) p14) p15) (replace (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))))))))))) B).
Proof.
  intros Hq Hf.
  destruct (addition_successor_specialization q f _ Hq Hf)
    as [p0 [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [p14 [Hp Hfnext]]]]]]]]]]]]]]]].
  destruct (multiplication_zero_left_application_certificate q Hq) as [p15 Hpnew].
  rewrite <- (multiplication_zero_left_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14) in Hpnew.
  exists p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15. split; [exact Hpnew |].
  rewrite replace_product in Hfnext. pose proof (tApp Hfnext Hpnew) as Hfinal.
  rewrite substitute_transpose in Hfinal. exact Hfinal.
Qed.
Definition multiplication_successor_guard {n} (X z s a m D R : Term nat n) :=
  (Π X (Arrow (app (shift D) V0)
      (Π (shift X) (Arrow (app (shift (shift D)) V0)
      (Neg (app (app (shift (shift R)) (app (app (shift (shift m)) (app (shift (shift s)) (shift V0))) V0)) (app (app (shift (shift a)) V0) (app (app (shift (shift m)) (shift V0)) V0)))))))).
Lemma replace_multiplication_successor_guard {j n} (f : Fin j -> Term nat n) X z s a m D R :
  replace f (multiplication_successor_guard X z s a m D R) =
  multiplication_successor_guard (replace f X) (replace f z) (replace f s) (replace f a)
    (replace f m) (replace f D) (replace f R).
Proof.
  unfold multiplication_successor_guard, Neg.
  repeat first [rewrite replace_product |rewrite replace_arrow |
    rewrite replace_application |rewrite replace_shift |rewrite replace_lift_closed].
  reflexivity.
Qed.
Definition multiplication_successor_application_type q : closed_term :=
  (Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
      (Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
      (expression_application_atom q Nat.eqb (FiniteExpressions.multiplication (FiniteExpressions.successor FiniteExpressions.first) FiniteExpressions.second) (FiniteExpressions.addition FiniteExpressions.second (FiniteExpressions.multiplication FiniteExpressions.first FiniteExpressions.second)) (shift V0) V0))))).
Lemma multiplication_successor_application_typed q : 0 < q ->
  Typed ε (multiplication_successor_application_type q) (𝓤 5).
Proof.
  intro Hq. destruct q as [|q]; [lia |]. unfold multiplication_successor_application_type.
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 5);
    [apply Separation.predicate_application; [exact Hq |apply GuardedFiniteLaws.selector_newest] |].
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 2).
  - apply Separation.predicate_application; [exact Hq |apply GuardedFiniteLaws.selector_newest].
  - apply expression_application_atom_typed;
      repeat apply GuardedFiniteLaws.selector_weaken; apply GuardedFiniteLaws.selector_newest.
Qed.
Lemma multiplication_successor_application_beta q :
  multiplication_successor_application_type q =ᵝ FiniteRecursionLaws.expanded_type q (FiniteExpressions.multiplication (FiniteExpressions.successor FiniteExpressions.first) FiniteExpressions.second) (FiniteExpressions.addition FiniteExpressions.second (FiniteExpressions.multiplication FiniteExpressions.first FiniteExpressions.second)).
Proof.
  unfold multiplication_successor_application_type, FiniteRecursionLaws.expanded_type, FiniteRecursionLaws.body.
  do 2 (apply beta_pi; [reflexivity |]; apply Unary.arrow_beta;
    [apply Separation.predicate_beta |]).
  apply FiniteUp.neg_beta.

  apply relation_application_beta.
Qed.
Theorem multiplication_successor_application_certificate q : 0 < q ->
  Realizes (multiplication_successor_application_type q).
Proof.
  intro Hq. eapply FiniteUp.inhabited_conversion.
  - exact (FiniteRecursionLaws.multiplication_successor_realized q Hq).
  - apply multiplication_successor_application_typed; exact Hq.
  - symmetry. apply multiplication_successor_application_beta.
Qed.
Definition multiplication_successor_annotation : Term nat 24 :=
  multiplication_successor_guard (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))).
Lemma multiplication_successor_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 :
  replace (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))))))))))) multiplication_successor_annotation = multiplication_successor_application_type q.
Proof.
  unfold multiplication_successor_annotation. rewrite replace_multiplication_successor_guard.
  change (multiplication_successor_guard (selector_type q) (point q 0) (capped_successor q)
    (capped_addition q) (capped_multiplication q) (Separation.predicate q)
    (RelationTables.relation_table q Nat.eqb) = multiplication_successor_application_type q).
  unfold multiplication_successor_guard, multiplication_successor_application_type, expression_application_atom.
  cbn [FiniteExpressions.denote].
  assert (HF : forall n, @shift nat n (selector_type q) = selector_type q).
  { intro n. unfold shift. apply rename_selector_type. } rewrite !HF.
  assert (HC : forall c : closed_term, shift c = @lift_closed 1 c).
  { intro c. rewrite lift_closed_shift, lift_closed_zero. reflexivity. }
  rewrite !HC, <- ?lift_closed_shift, <- ?lift_closed_shift. reflexivity.
Qed.
Theorem multiplication_successor_prefix_matches_source body :
  assemble (npis (firstn 25 observation_fields) body) [] =
  option_map (fun B => telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation (Π order_congruence_annotation (Π order_reflexivity_annotation (Π order_transitivity_annotation (Π addition_zero_annotation (Π addition_successor_annotation (Π multiplication_zero_left_annotation (Π multiplication_successor_annotation B))))))))))))))))))
    (assemble body [116;115;114;113;112;111;110;109;108;107;106;105;104;103;102;101;100;7;6;5;4;3;2;1;0]).
Proof.
  cbn [firstn observation_fields].
  repeat (eapply assemble_prefix_congr; [reflexivity |]).
  apply prefix_option_map_id.
Qed.
Theorem multiplication_successor_specialization q f (B : Term nat 25) : 0 < q ->
  Typed ε f (telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation (Π order_congruence_annotation (Π order_reflexivity_annotation (Π order_transitivity_annotation (Π addition_zero_annotation (Π addition_successor_annotation (Π multiplication_zero_left_annotation (Π multiplication_successor_annotation B)))))))))))))))))) ->
  exists p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16,
    Typed ε p16 (replace (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))))))))))) multiplication_successor_annotation) /\
    Typed ε (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (table_apply f (data_arguments q)) p0) p1) p2) p3) p4) p5) p6) p7) p8) p9) p10) p11) p12) p13) p14) p15) p16) (replace (extend p16 (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))))))))))) B).
Proof.
  intros Hq Hf.
  destruct (multiplication_zero_left_specialization q f _ Hq Hf)
    as [p0 [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [p14 [p15 [Hp Hfnext]]]]]]]]]]]]]]]]].
  destruct (multiplication_successor_application_certificate q Hq) as [p16 Hpnew].
  rewrite <- (multiplication_successor_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15) in Hpnew.
  exists p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16. split; [exact Hpnew |].
  rewrite replace_product in Hfnext. pose proof (tApp Hfnext Hpnew) as Hfinal.
  rewrite substitute_transpose in Hfinal. exact Hfinal.
Qed.
Definition multiplication_zero_right_guard {n} (X z s a m D R : Term nat n) :=
  (Π X (Arrow (app (shift D) V0)
      (Neg (app (app (shift R) (app (app (shift m) V0) (shift z))) (shift z))))).
Lemma replace_multiplication_zero_right_guard {j n} (f : Fin j -> Term nat n) X z s a m D R :
  replace f (multiplication_zero_right_guard X z s a m D R) =
  multiplication_zero_right_guard (replace f X) (replace f z) (replace f s) (replace f a)
    (replace f m) (replace f D) (replace f R).
Proof.
  unfold multiplication_zero_right_guard, Neg.
  repeat first [rewrite replace_product |rewrite replace_arrow |
    rewrite replace_application |rewrite replace_shift |rewrite replace_lift_closed].
  reflexivity.
Qed.
Definition multiplication_zero_right_application_type q : closed_term :=
  (Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
      (expression_application_atom q Nat.eqb (FiniteExpressions.multiplication FiniteExpressions.first FiniteExpressions.zero) FiniteExpressions.zero V0 V0))).
Lemma multiplication_zero_right_application_typed q : 0 < q ->
  Typed ε (multiplication_zero_right_application_type q) (𝓤 5).
Proof.
  intro Hq. destruct q as [|q]; [lia |]. unfold multiplication_zero_right_application_type.

  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 2).
  - apply Separation.predicate_application; [exact Hq |apply GuardedFiniteLaws.selector_newest].
  - apply expression_application_atom_typed;
      repeat apply GuardedFiniteLaws.selector_weaken; apply GuardedFiniteLaws.selector_newest.
Qed.
Lemma multiplication_zero_right_application_beta q :
  multiplication_zero_right_application_type q =ᵝ FiniteZeroLaws.expanded_type q (capped_multiplication q) true true.
Proof.
  unfold multiplication_zero_right_application_type, FiniteZeroLaws.expanded_type, FiniteZeroLaws.body.
  do 1 (apply beta_pi; [reflexivity |]; apply Unary.arrow_beta;
    [apply Separation.predicate_beta |]).
  apply FiniteUp.neg_beta.
  unfold expression_application_atom, FiniteZeroLaws.lhs, FiniteZeroLaws.argument, FiniteBinaryCongruence.output. cbn [negb FiniteExpressions.denote].
  apply relation_application_beta.
Qed.
Theorem multiplication_zero_right_application_certificate q : 0 < q ->
  Realizes (multiplication_zero_right_application_type q).
Proof.
  intro Hq. eapply FiniteUp.inhabited_conversion.
  - exact (FiniteZeroLaws.multiplication_zero_right_realized q Hq).
  - apply multiplication_zero_right_application_typed; exact Hq.
  - symmetry. apply multiplication_zero_right_application_beta.
Qed.
Definition multiplication_zero_right_annotation : Term nat 25 :=
  multiplication_zero_right_guard (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))).
Lemma multiplication_zero_right_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 :
  replace (extend p16 (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))))))))))) multiplication_zero_right_annotation = multiplication_zero_right_application_type q.
Proof.
  unfold multiplication_zero_right_annotation. rewrite replace_multiplication_zero_right_guard.
  change (multiplication_zero_right_guard (selector_type q) (point q 0) (capped_successor q)
    (capped_addition q) (capped_multiplication q) (Separation.predicate q)
    (RelationTables.relation_table q Nat.eqb) = multiplication_zero_right_application_type q).
  unfold multiplication_zero_right_guard, multiplication_zero_right_application_type, expression_application_atom.
  cbn [FiniteExpressions.denote].

  assert (HC : forall c : closed_term, shift c = @lift_closed 1 c).
  { intro c. rewrite lift_closed_shift, lift_closed_zero. reflexivity. }
  rewrite !HC, <- ?lift_closed_shift, <- ?lift_closed_shift. reflexivity.
Qed.
Theorem multiplication_zero_right_prefix_matches_source body :
  assemble (npis (firstn 26 observation_fields) body) [] =
  option_map (fun B => telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation (Π order_congruence_annotation (Π order_reflexivity_annotation (Π order_transitivity_annotation (Π addition_zero_annotation (Π addition_successor_annotation (Π multiplication_zero_left_annotation (Π multiplication_successor_annotation (Π multiplication_zero_right_annotation B)))))))))))))))))))
    (assemble body [117;116;115;114;113;112;111;110;109;108;107;106;105;104;103;102;101;100;7;6;5;4;3;2;1;0]).
Proof.
  cbn [firstn observation_fields].
  repeat (eapply assemble_prefix_congr; [reflexivity |]).
  apply prefix_option_map_id.
Qed.
Theorem multiplication_zero_right_specialization q f (B : Term nat 26) : 0 < q ->
  Typed ε f (telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation (Π order_congruence_annotation (Π order_reflexivity_annotation (Π order_transitivity_annotation (Π addition_zero_annotation (Π addition_successor_annotation (Π multiplication_zero_left_annotation (Π multiplication_successor_annotation (Π multiplication_zero_right_annotation B))))))))))))))))))) ->
  exists p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17,
    Typed ε p17 (replace (extend p16 (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))))))))))) multiplication_zero_right_annotation) /\
    Typed ε (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (table_apply f (data_arguments q)) p0) p1) p2) p3) p4) p5) p6) p7) p8) p9) p10) p11) p12) p13) p14) p15) p16) p17) (replace (extend p17 (extend p16 (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))))))))))))) B).
Proof.
  intros Hq Hf.
  destruct (multiplication_successor_specialization q f _ Hq Hf)
    as [p0 [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [p14 [p15 [p16 [Hp Hfnext]]]]]]]]]]]]]]]]]].
  destruct (multiplication_zero_right_application_certificate q Hq) as [p17 Hpnew].
  rewrite <- (multiplication_zero_right_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16) in Hpnew.
  exists p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17. split; [exact Hpnew |].
  rewrite replace_product in Hfnext. pose proof (tApp Hfnext Hpnew) as Hfinal.
  rewrite substitute_transpose in Hfinal. exact Hfinal.
Qed.
Definition successor_order_guard {n} (X z s a m D R : Term nat n) :=
  (Π X (Arrow (app (shift D) V0)
      (Neg (app (app (shift R) V0) (app (shift s) V0))))).
Lemma replace_successor_order_guard {j n} (f : Fin j -> Term nat n) X z s a m D R :
  replace f (successor_order_guard X z s a m D R) =
  successor_order_guard (replace f X) (replace f z) (replace f s) (replace f a)
    (replace f m) (replace f D) (replace f R).
Proof.
  unfold successor_order_guard, Neg.
  repeat first [rewrite replace_product |rewrite replace_arrow |
    rewrite replace_application |rewrite replace_shift |rewrite replace_lift_closed].
  reflexivity.
Qed.
Definition successor_order_application_type q : closed_term :=
  (Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
      (expression_application_atom q Nat.leb FiniteExpressions.first (FiniteExpressions.successor FiniteExpressions.first) V0 V0))).
Lemma successor_order_application_typed q : 0 < q ->
  Typed ε (successor_order_application_type q) (𝓤 5).
Proof.
  intro Hq. destruct q as [|q]; [lia |]. unfold successor_order_application_type.

  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 2).
  - apply Separation.predicate_application; [exact Hq |apply GuardedFiniteLaws.selector_newest].
  - apply expression_application_atom_typed;
      repeat apply GuardedFiniteLaws.selector_weaken; apply GuardedFiniteLaws.selector_newest.
Qed.
Lemma successor_order_application_beta q :
  successor_order_application_type q =ᵝ FiniteOrderLaws.unary_type q (FiniteOrderLaws.comparison FiniteExpressions.first (FiniteExpressions.successor FiniteExpressions.first)).
Proof.
  unfold successor_order_application_type, FiniteOrderLaws.unary_type, FiniteOrderLaws.body.
  do 1 (apply beta_pi; [reflexivity |]; apply Unary.arrow_beta;
    [apply Separation.predicate_beta |]).
  apply FiniteUp.neg_beta.
  cbn [FiniteOrderLaws.atom].
  apply relation_application_beta.
Qed.
Theorem successor_order_application_certificate q : 0 < q ->
  Realizes (successor_order_application_type q).
Proof.
  intro Hq. eapply FiniteUp.inhabited_conversion.
  - exact (FiniteOrderLaws.successor_order_realized q Hq).
  - apply successor_order_application_typed; exact Hq.
  - symmetry. apply successor_order_application_beta.
Qed.
Definition successor_order_annotation : Term nat 26 :=
  successor_order_guard (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))).
Lemma successor_order_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 :
  replace (extend p17 (extend p16 (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))))))))))))) successor_order_annotation = successor_order_application_type q.
Proof.
  unfold successor_order_annotation. rewrite replace_successor_order_guard.
  change (successor_order_guard (selector_type q) (point q 0) (capped_successor q)
    (capped_addition q) (capped_multiplication q) (Separation.predicate q)
    (RelationTables.relation_table q Nat.leb) = successor_order_application_type q).
  unfold successor_order_guard, successor_order_application_type, expression_application_atom.
  cbn [FiniteExpressions.denote].

  assert (HC : forall c : closed_term, shift c = @lift_closed 1 c).
  { intro c. rewrite lift_closed_shift, lift_closed_zero. reflexivity. }
  rewrite !HC, <- ?lift_closed_shift, <- ?lift_closed_shift. reflexivity.
Qed.
Theorem successor_order_prefix_matches_source body :
  assemble (npis (firstn 27 observation_fields) body) [] =
  option_map (fun B => telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation (Π order_congruence_annotation (Π order_reflexivity_annotation (Π order_transitivity_annotation (Π addition_zero_annotation (Π addition_successor_annotation (Π multiplication_zero_left_annotation (Π multiplication_successor_annotation (Π multiplication_zero_right_annotation (Π successor_order_annotation B))))))))))))))))))))
    (assemble body [118;117;116;115;114;113;112;111;110;109;108;107;106;105;104;103;102;101;100;7;6;5;4;3;2;1;0]).
Proof.
  cbn [firstn observation_fields].
  repeat (eapply assemble_prefix_congr; [reflexivity |]).
  apply prefix_option_map_id.
Qed.
Theorem successor_order_specialization q f (B : Term nat 27) : 0 < q ->
  Typed ε f (telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation (Π order_congruence_annotation (Π order_reflexivity_annotation (Π order_transitivity_annotation (Π addition_zero_annotation (Π addition_successor_annotation (Π multiplication_zero_left_annotation (Π multiplication_successor_annotation (Π multiplication_zero_right_annotation (Π successor_order_annotation B)))))))))))))))))))) ->
  exists p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18,
    Typed ε p18 (replace (extend p17 (extend p16 (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))))))))))))) successor_order_annotation) /\
    Typed ε (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (table_apply f (data_arguments q)) p0) p1) p2) p3) p4) p5) p6) p7) p8) p9) p10) p11) p12) p13) p14) p15) p16) p17) p18) (replace (extend p18 (extend p17 (extend p16 (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))))))))))))) B).
Proof.
  intros Hq Hf.
  destruct (multiplication_zero_right_specialization q f _ Hq Hf)
    as [p0 [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [p14 [p15 [p16 [p17 [Hp Hfnext]]]]]]]]]]]]]]]]]]].
  destruct (successor_order_application_certificate q Hq) as [p18 Hpnew].
  rewrite <- (successor_order_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17) in Hpnew.
  exists p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18. split; [exact Hpnew |].
  rewrite replace_product in Hfnext. pose proof (tApp Hfnext Hpnew) as Hfinal.
  rewrite substitute_transpose in Hfinal. exact Hfinal.
Qed.
Definition addition_order_left_guard {n} (X z s a m D R : Term nat n) :=
  (Π X (Arrow (app (shift D) V0)
      (Π (shift X) (Arrow (app (shift (shift D)) V0)
      (Neg (app (app (shift (shift R)) (shift V0)) (app (app (shift (shift a)) (shift V0)) V0))))))).
Lemma replace_addition_order_left_guard {j n} (f : Fin j -> Term nat n) X z s a m D R :
  replace f (addition_order_left_guard X z s a m D R) =
  addition_order_left_guard (replace f X) (replace f z) (replace f s) (replace f a)
    (replace f m) (replace f D) (replace f R).
Proof.
  unfold addition_order_left_guard, Neg.
  repeat first [rewrite replace_product |rewrite replace_arrow |
    rewrite replace_application |rewrite replace_shift |rewrite replace_lift_closed].
  reflexivity.
Qed.
Definition addition_order_left_application_type q : closed_term :=
  (Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
      (Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
      (expression_application_atom q Nat.leb FiniteExpressions.first (FiniteExpressions.addition FiniteExpressions.first FiniteExpressions.second) (shift V0) V0))))).
Lemma addition_order_left_application_typed q : 0 < q ->
  Typed ε (addition_order_left_application_type q) (𝓤 5).
Proof.
  intro Hq. destruct q as [|q]; [lia |]. unfold addition_order_left_application_type.
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 5);
    [apply Separation.predicate_application; [exact Hq |apply GuardedFiniteLaws.selector_newest] |].
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 2).
  - apply Separation.predicate_application; [exact Hq |apply GuardedFiniteLaws.selector_newest].
  - apply expression_application_atom_typed;
      repeat apply GuardedFiniteLaws.selector_weaken; apply GuardedFiniteLaws.selector_newest.
Qed.
Lemma addition_order_left_application_beta q :
  addition_order_left_application_type q =ᵝ FiniteOrderLaws.binary_type q (FiniteOrderLaws.comparison FiniteExpressions.first (FiniteExpressions.addition FiniteExpressions.first FiniteExpressions.second)).
Proof.
  unfold addition_order_left_application_type, FiniteOrderLaws.binary_type, FiniteOrderLaws.body.
  do 2 (apply beta_pi; [reflexivity |]; apply Unary.arrow_beta;
    [apply Separation.predicate_beta |]).
  apply FiniteUp.neg_beta.
  cbn [FiniteOrderLaws.atom].
  apply relation_application_beta.
Qed.
Theorem addition_order_left_application_certificate q : 0 < q ->
  Realizes (addition_order_left_application_type q).
Proof.
  intro Hq. eapply FiniteUp.inhabited_conversion.
  - exact (FiniteOrderLaws.addition_order_left_realized q Hq).
  - apply addition_order_left_application_typed; exact Hq.
  - symmetry. apply addition_order_left_application_beta.
Qed.
Definition addition_order_left_annotation : Term nat 27 :=
  addition_order_left_guard (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))).
Lemma addition_order_left_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 :
  replace (extend p18 (extend p17 (extend p16 (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))))))))))))) addition_order_left_annotation = addition_order_left_application_type q.
Proof.
  unfold addition_order_left_annotation. rewrite replace_addition_order_left_guard.
  change (addition_order_left_guard (selector_type q) (point q 0) (capped_successor q)
    (capped_addition q) (capped_multiplication q) (Separation.predicate q)
    (RelationTables.relation_table q Nat.leb) = addition_order_left_application_type q).
  unfold addition_order_left_guard, addition_order_left_application_type, expression_application_atom.
  cbn [FiniteExpressions.denote].
  assert (HF : forall n, @shift nat n (selector_type q) = selector_type q).
  { intro n. unfold shift. apply rename_selector_type. } rewrite !HF.
  assert (HC : forall c : closed_term, shift c = @lift_closed 1 c).
  { intro c. rewrite lift_closed_shift, lift_closed_zero. reflexivity. }
  rewrite !HC, <- ?lift_closed_shift, <- ?lift_closed_shift. reflexivity.
Qed.
Theorem addition_order_left_prefix_matches_source body :
  assemble (npis (firstn 28 observation_fields) body) [] =
  option_map (fun B => telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation (Π order_congruence_annotation (Π order_reflexivity_annotation (Π order_transitivity_annotation (Π addition_zero_annotation (Π addition_successor_annotation (Π multiplication_zero_left_annotation (Π multiplication_successor_annotation (Π multiplication_zero_right_annotation (Π successor_order_annotation (Π addition_order_left_annotation B)))))))))))))))))))))
    (assemble body [119;118;117;116;115;114;113;112;111;110;109;108;107;106;105;104;103;102;101;100;7;6;5;4;3;2;1;0]).
Proof.
  cbn [firstn observation_fields].
  repeat (eapply assemble_prefix_congr; [reflexivity |]).
  apply prefix_option_map_id.
Qed.
Theorem addition_order_left_specialization q f (B : Term nat 28) : 0 < q ->
  Typed ε f (telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation (Π order_congruence_annotation (Π order_reflexivity_annotation (Π order_transitivity_annotation (Π addition_zero_annotation (Π addition_successor_annotation (Π multiplication_zero_left_annotation (Π multiplication_successor_annotation (Π multiplication_zero_right_annotation (Π successor_order_annotation (Π addition_order_left_annotation B))))))))))))))))))))) ->
  exists p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19,
    Typed ε p19 (replace (extend p18 (extend p17 (extend p16 (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))))))))))))) addition_order_left_annotation) /\
    Typed ε (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (table_apply f (data_arguments q)) p0) p1) p2) p3) p4) p5) p6) p7) p8) p9) p10) p11) p12) p13) p14) p15) p16) p17) p18) p19) (replace (extend p19 (extend p18 (extend p17 (extend p16 (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))))))))))))))) B).
Proof.
  intros Hq Hf.
  destruct (successor_order_specialization q f _ Hq Hf)
    as [p0 [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [p14 [p15 [p16 [p17 [p18 [Hp Hfnext]]]]]]]]]]]]]]]]]]]].
  destruct (addition_order_left_application_certificate q Hq) as [p19 Hpnew].
  rewrite <- (addition_order_left_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18) in Hpnew.
  exists p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19. split; [exact Hpnew |].
  rewrite replace_product in Hfnext. pose proof (tApp Hfnext Hpnew) as Hfinal.
  rewrite substitute_transpose in Hfinal. exact Hfinal.
Qed.
Definition addition_order_right_guard {n} (X z s a m D R : Term nat n) :=
  (Π X (Arrow (app (shift D) V0)
      (Π (shift X) (Arrow (app (shift (shift D)) V0)
      (Neg (app (app (shift (shift R)) V0) (app (app (shift (shift a)) (shift V0)) V0))))))).
Lemma replace_addition_order_right_guard {j n} (f : Fin j -> Term nat n) X z s a m D R :
  replace f (addition_order_right_guard X z s a m D R) =
  addition_order_right_guard (replace f X) (replace f z) (replace f s) (replace f a)
    (replace f m) (replace f D) (replace f R).
Proof.
  unfold addition_order_right_guard, Neg.
  repeat first [rewrite replace_product |rewrite replace_arrow |
    rewrite replace_application |rewrite replace_shift |rewrite replace_lift_closed].
  reflexivity.
Qed.
Definition addition_order_right_application_type q : closed_term :=
  (Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
      (Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
      (expression_application_atom q Nat.leb FiniteExpressions.second (FiniteExpressions.addition FiniteExpressions.first FiniteExpressions.second) (shift V0) V0))))).
Lemma addition_order_right_application_typed q : 0 < q ->
  Typed ε (addition_order_right_application_type q) (𝓤 5).
Proof.
  intro Hq. destruct q as [|q]; [lia |]. unfold addition_order_right_application_type.
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 5);
    [apply Separation.predicate_application; [exact Hq |apply GuardedFiniteLaws.selector_newest] |].
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 2).
  - apply Separation.predicate_application; [exact Hq |apply GuardedFiniteLaws.selector_newest].
  - apply expression_application_atom_typed;
      repeat apply GuardedFiniteLaws.selector_weaken; apply GuardedFiniteLaws.selector_newest.
Qed.
Lemma addition_order_right_application_beta q :
  addition_order_right_application_type q =ᵝ FiniteOrderLaws.binary_type q (FiniteOrderLaws.comparison FiniteExpressions.second (FiniteExpressions.addition FiniteExpressions.first FiniteExpressions.second)).
Proof.
  unfold addition_order_right_application_type, FiniteOrderLaws.binary_type, FiniteOrderLaws.body.
  do 2 (apply beta_pi; [reflexivity |]; apply Unary.arrow_beta;
    [apply Separation.predicate_beta |]).
  apply FiniteUp.neg_beta.
  cbn [FiniteOrderLaws.atom].
  apply relation_application_beta.
Qed.
Theorem addition_order_right_application_certificate q : 0 < q ->
  Realizes (addition_order_right_application_type q).
Proof.
  intro Hq. eapply FiniteUp.inhabited_conversion.
  - exact (FiniteOrderLaws.addition_order_right_realized q Hq).
  - apply addition_order_right_application_typed; exact Hq.
  - symmetry. apply addition_order_right_application_beta.
Qed.
Definition addition_order_right_annotation : Term nat 28 :=
  addition_order_right_guard (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))))).
Lemma addition_order_right_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 :
  replace (extend p19 (extend p18 (extend p17 (extend p16 (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))))))))))))))) addition_order_right_annotation = addition_order_right_application_type q.
Proof.
  unfold addition_order_right_annotation. rewrite replace_addition_order_right_guard.
  change (addition_order_right_guard (selector_type q) (point q 0) (capped_successor q)
    (capped_addition q) (capped_multiplication q) (Separation.predicate q)
    (RelationTables.relation_table q Nat.leb) = addition_order_right_application_type q).
  unfold addition_order_right_guard, addition_order_right_application_type, expression_application_atom.
  cbn [FiniteExpressions.denote].
  assert (HF : forall n, @shift nat n (selector_type q) = selector_type q).
  { intro n. unfold shift. apply rename_selector_type. } rewrite !HF.
  assert (HC : forall c : closed_term, shift c = @lift_closed 1 c).
  { intro c. rewrite lift_closed_shift, lift_closed_zero. reflexivity. }
  rewrite !HC, <- ?lift_closed_shift, <- ?lift_closed_shift. reflexivity.
Qed.
Theorem addition_order_right_prefix_matches_source body :
  assemble (npis (firstn 29 observation_fields) body) [] =
  option_map (fun B => telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation (Π order_congruence_annotation (Π order_reflexivity_annotation (Π order_transitivity_annotation (Π addition_zero_annotation (Π addition_successor_annotation (Π multiplication_zero_left_annotation (Π multiplication_successor_annotation (Π multiplication_zero_right_annotation (Π successor_order_annotation (Π addition_order_left_annotation (Π addition_order_right_annotation B))))))))))))))))))))))
    (assemble body [120;119;118;117;116;115;114;113;112;111;110;109;108;107;106;105;104;103;102;101;100;7;6;5;4;3;2;1;0]).
Proof.
  cbn [firstn observation_fields].
  repeat (eapply assemble_prefix_congr; [reflexivity |]).
  apply prefix_option_map_id.
Qed.
Theorem addition_order_right_specialization q f (B : Term nat 29) : 0 < q ->
  Typed ε f (telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation (Π order_congruence_annotation (Π order_reflexivity_annotation (Π order_transitivity_annotation (Π addition_zero_annotation (Π addition_successor_annotation (Π multiplication_zero_left_annotation (Π multiplication_successor_annotation (Π multiplication_zero_right_annotation (Π successor_order_annotation (Π addition_order_left_annotation (Π addition_order_right_annotation B)))))))))))))))))))))) ->
  exists p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20,
    Typed ε p20 (replace (extend p19 (extend p18 (extend p17 (extend p16 (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))))))))))))))) addition_order_right_annotation) /\
    Typed ε (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (table_apply f (data_arguments q)) p0) p1) p2) p3) p4) p5) p6) p7) p8) p9) p10) p11) p12) p13) p14) p15) p16) p17) p18) p19) p20) (replace (extend p20 (extend p19 (extend p18 (extend p17 (extend p16 (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))))))))))))))) B).
Proof.
  intros Hq Hf.
  destruct (addition_order_left_specialization q f _ Hq Hf)
    as [p0 [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [p14 [p15 [p16 [p17 [p18 [p19 [Hp Hfnext]]]]]]]]]]]]]]]]]]]]].
  destruct (addition_order_right_application_certificate q Hq) as [p20 Hpnew].
  rewrite <- (addition_order_right_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19) in Hpnew.
  exists p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20. split; [exact Hpnew |].
  rewrite replace_product in Hfnext. pose proof (tApp Hfnext Hpnew) as Hfinal.
  rewrite substitute_transpose in Hfinal. exact Hfinal.
Qed.
Definition multiplication_order_left_guard {n} (X z s a m D R : Term nat n) :=
  (Π X (Arrow (app (shift D) V0)
      (Π (shift X) (Arrow (app (shift (shift D)) V0)
      (Arrow (Neg (app (app (shift (shift R)) (app (shift (shift s)) (shift (shift z)))) V0)) (Neg (app (app (shift (shift R)) (shift V0)) (app (app (shift (shift m)) (shift V0)) V0)))))))).
Lemma replace_multiplication_order_left_guard {j n} (f : Fin j -> Term nat n) X z s a m D R :
  replace f (multiplication_order_left_guard X z s a m D R) =
  multiplication_order_left_guard (replace f X) (replace f z) (replace f s) (replace f a)
    (replace f m) (replace f D) (replace f R).
Proof.
  unfold multiplication_order_left_guard, Neg.
  repeat first [rewrite replace_product |rewrite replace_arrow |
    rewrite replace_application |rewrite replace_shift |rewrite replace_lift_closed].
  reflexivity.
Qed.
Definition multiplication_order_left_application_type q : closed_term :=
  (Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
      (Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
      (Arrow (expression_application_atom q Nat.leb (FiniteExpressions.successor FiniteExpressions.zero) FiniteExpressions.second (shift V0) V0) (expression_application_atom q Nat.leb FiniteExpressions.first (FiniteExpressions.multiplication FiniteExpressions.first FiniteExpressions.second) (shift V0) V0)))))).
Lemma multiplication_order_left_application_typed q : 0 < q ->
  Typed ε (multiplication_order_left_application_type q) (𝓤 5).
Proof.
  intro Hq. destruct q as [|q]; [lia |]. unfold multiplication_order_left_application_type.
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 5);
    [apply Separation.predicate_application; [exact Hq |apply GuardedFiniteLaws.selector_newest] |].
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 3).
  - apply Separation.predicate_application; [exact Hq |apply GuardedFiniteLaws.selector_newest].
  - apply (arrow_formation _ _ _ 2 2); apply expression_application_atom_typed;
      repeat apply GuardedFiniteLaws.selector_weaken; apply GuardedFiniteLaws.selector_newest.
Qed.
Lemma multiplication_order_left_application_beta q :
  multiplication_order_left_application_type q =ᵝ FiniteOrderLaws.binary_type q (FiniteOrderLaws.conditional (FiniteExpressions.successor FiniteExpressions.zero) FiniteExpressions.second FiniteExpressions.first (FiniteExpressions.multiplication FiniteExpressions.first FiniteExpressions.second)).
Proof.
  unfold multiplication_order_left_application_type, FiniteOrderLaws.binary_type, FiniteOrderLaws.body.
  do 2 (apply beta_pi; [reflexivity |]; apply Unary.arrow_beta;
    [apply Separation.predicate_beta |]).
  apply Unary.arrow_beta; apply FiniteUp.neg_beta.
  all: cbn [FiniteOrderLaws.atom]; apply relation_application_beta.
Qed.
Theorem multiplication_order_left_application_certificate q : 0 < q ->
  Realizes (multiplication_order_left_application_type q).
Proof.
  intro Hq. eapply FiniteUp.inhabited_conversion.
  - exact (FiniteOrderLaws.multiplication_order_left_realized q Hq).
  - apply multiplication_order_left_application_typed; exact Hq.
  - symmetry. apply multiplication_order_left_application_beta.
Qed.
Definition multiplication_order_left_annotation : Term nat 29 :=
  multiplication_order_left_guard (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))))).
Lemma multiplication_order_left_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 :
  replace (extend p20 (extend p19 (extend p18 (extend p17 (extend p16 (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))))))))))))))) multiplication_order_left_annotation = multiplication_order_left_application_type q.
Proof.
  unfold multiplication_order_left_annotation. rewrite replace_multiplication_order_left_guard.
  change (multiplication_order_left_guard (selector_type q) (point q 0) (capped_successor q)
    (capped_addition q) (capped_multiplication q) (Separation.predicate q)
    (RelationTables.relation_table q Nat.leb) = multiplication_order_left_application_type q).
  unfold multiplication_order_left_guard, multiplication_order_left_application_type, expression_application_atom.
  cbn [FiniteExpressions.denote].
  assert (HF : forall n, @shift nat n (selector_type q) = selector_type q).
  { intro n. unfold shift. apply rename_selector_type. } rewrite !HF.
  assert (HC : forall c : closed_term, shift c = @lift_closed 1 c).
  { intro c. rewrite lift_closed_shift, lift_closed_zero. reflexivity. }
  rewrite !HC, <- ?lift_closed_shift, <- ?lift_closed_shift. reflexivity.
Qed.
Theorem multiplication_order_left_prefix_matches_source body :
  assemble (npis (firstn 30 observation_fields) body) [] =
  option_map (fun B => telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation (Π order_congruence_annotation (Π order_reflexivity_annotation (Π order_transitivity_annotation (Π addition_zero_annotation (Π addition_successor_annotation (Π multiplication_zero_left_annotation (Π multiplication_successor_annotation (Π multiplication_zero_right_annotation (Π successor_order_annotation (Π addition_order_left_annotation (Π addition_order_right_annotation (Π multiplication_order_left_annotation B)))))))))))))))))))))))
    (assemble body [121;120;119;118;117;116;115;114;113;112;111;110;109;108;107;106;105;104;103;102;101;100;7;6;5;4;3;2;1;0]).
Proof.
  cbn [firstn observation_fields].
  repeat (eapply assemble_prefix_congr; [reflexivity |]).
  apply prefix_option_map_id.
Qed.
Theorem multiplication_order_left_specialization q f (B : Term nat 30) : 0 < q ->
  Typed ε f (telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation (Π order_congruence_annotation (Π order_reflexivity_annotation (Π order_transitivity_annotation (Π addition_zero_annotation (Π addition_successor_annotation (Π multiplication_zero_left_annotation (Π multiplication_successor_annotation (Π multiplication_zero_right_annotation (Π successor_order_annotation (Π addition_order_left_annotation (Π addition_order_right_annotation (Π multiplication_order_left_annotation B))))))))))))))))))))))) ->
  exists p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21,
    Typed ε p21 (replace (extend p20 (extend p19 (extend p18 (extend p17 (extend p16 (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))))))))))))))) multiplication_order_left_annotation) /\
    Typed ε (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (table_apply f (data_arguments q)) p0) p1) p2) p3) p4) p5) p6) p7) p8) p9) p10) p11) p12) p13) p14) p15) p16) p17) p18) p19) p20) p21) (replace (extend p21 (extend p20 (extend p19 (extend p18 (extend p17 (extend p16 (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))))))))))))))))) B).
Proof.
  intros Hq Hf.
  destruct (addition_order_right_specialization q f _ Hq Hf)
    as [p0 [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [p14 [p15 [p16 [p17 [p18 [p19 [p20 [Hp Hfnext]]]]]]]]]]]]]]]]]]]]]].
  destruct (multiplication_order_left_application_certificate q Hq) as [p21 Hpnew].
  rewrite <- (multiplication_order_left_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20) in Hpnew.
  exists p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21. split; [exact Hpnew |].
  rewrite replace_product in Hfnext. pose proof (tApp Hfnext Hpnew) as Hfinal.
  rewrite substitute_transpose in Hfinal. exact Hfinal.
Qed.
Definition multiplication_order_right_guard {n} (X z s a m D R : Term nat n) :=
  (Π X (Arrow (app (shift D) V0)
      (Π (shift X) (Arrow (app (shift (shift D)) V0)
      (Arrow (Neg (app (app (shift (shift R)) (app (shift (shift s)) (shift (shift z)))) (shift V0))) (Neg (app (app (shift (shift R)) V0) (app (app (shift (shift m)) (shift V0)) V0)))))))).
Lemma replace_multiplication_order_right_guard {j n} (f : Fin j -> Term nat n) X z s a m D R :
  replace f (multiplication_order_right_guard X z s a m D R) =
  multiplication_order_right_guard (replace f X) (replace f z) (replace f s) (replace f a)
    (replace f m) (replace f D) (replace f R).
Proof.
  unfold multiplication_order_right_guard, Neg.
  repeat first [rewrite replace_product |rewrite replace_arrow |
    rewrite replace_application |rewrite replace_shift |rewrite replace_lift_closed].
  reflexivity.
Qed.
Definition multiplication_order_right_application_type q : closed_term :=
  (Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
      (Π (selector_type q) (Arrow (app (lift_closed (Separation.predicate q)) V0)
      (Arrow (expression_application_atom q Nat.leb (FiniteExpressions.successor FiniteExpressions.zero) FiniteExpressions.first (shift V0) V0) (expression_application_atom q Nat.leb FiniteExpressions.second (FiniteExpressions.multiplication FiniteExpressions.first FiniteExpressions.second) (shift V0) V0)))))).
Lemma multiplication_order_right_application_typed q : 0 < q ->
  Typed ε (multiplication_order_right_application_type q) (𝓤 5).
Proof.
  intro Hq. destruct q as [|q]; [lia |]. unfold multiplication_order_right_application_type.
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 5);
    [apply Separation.predicate_application; [exact Hq |apply GuardedFiniteLaws.selector_newest] |].
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 3).
  - apply Separation.predicate_application; [exact Hq |apply GuardedFiniteLaws.selector_newest].
  - apply (arrow_formation _ _ _ 2 2); apply expression_application_atom_typed;
      repeat apply GuardedFiniteLaws.selector_weaken; apply GuardedFiniteLaws.selector_newest.
Qed.
Lemma multiplication_order_right_application_beta q :
  multiplication_order_right_application_type q =ᵝ FiniteOrderLaws.binary_type q (FiniteOrderLaws.conditional (FiniteExpressions.successor FiniteExpressions.zero) FiniteExpressions.first FiniteExpressions.second (FiniteExpressions.multiplication FiniteExpressions.first FiniteExpressions.second)).
Proof.
  unfold multiplication_order_right_application_type, FiniteOrderLaws.binary_type, FiniteOrderLaws.body.
  do 2 (apply beta_pi; [reflexivity |]; apply Unary.arrow_beta;
    [apply Separation.predicate_beta |]).
  apply Unary.arrow_beta; apply FiniteUp.neg_beta.
  all: cbn [FiniteOrderLaws.atom]; apply relation_application_beta.
Qed.
Theorem multiplication_order_right_application_certificate q : 0 < q ->
  Realizes (multiplication_order_right_application_type q).
Proof.
  intro Hq. eapply FiniteUp.inhabited_conversion.
  - exact (FiniteOrderLaws.multiplication_order_right_realized q Hq).
  - apply multiplication_order_right_application_typed; exact Hq.
  - symmetry. apply multiplication_order_right_application_beta.
Qed.
Definition multiplication_order_right_annotation : Term nat 30 :=
  multiplication_order_right_guard (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))))))))) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))))))))))))))))).
Lemma multiplication_order_right_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 :
  replace (extend p21 (extend p20 (extend p19 (extend p18 (extend p17 (extend p16 (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))))))))))))))))) multiplication_order_right_annotation = multiplication_order_right_application_type q.
Proof.
  unfold multiplication_order_right_annotation. rewrite replace_multiplication_order_right_guard.
  change (multiplication_order_right_guard (selector_type q) (point q 0) (capped_successor q)
    (capped_addition q) (capped_multiplication q) (Separation.predicate q)
    (RelationTables.relation_table q Nat.leb) = multiplication_order_right_application_type q).
  unfold multiplication_order_right_guard, multiplication_order_right_application_type, expression_application_atom.
  cbn [FiniteExpressions.denote].
  assert (HF : forall n, @shift nat n (selector_type q) = selector_type q).
  { intro n. unfold shift. apply rename_selector_type. } rewrite !HF.
  assert (HC : forall c : closed_term, shift c = @lift_closed 1 c).
  { intro c. rewrite lift_closed_shift, lift_closed_zero. reflexivity. }
  rewrite !HC, <- ?lift_closed_shift, <- ?lift_closed_shift. reflexivity.
Qed.
Theorem multiplication_order_right_prefix_matches_source body :
  assemble (npis (firstn 31 observation_fields) body) [] =
  option_map (fun B => telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation (Π order_congruence_annotation (Π order_reflexivity_annotation (Π order_transitivity_annotation (Π addition_zero_annotation (Π addition_successor_annotation (Π multiplication_zero_left_annotation (Π multiplication_successor_annotation (Π multiplication_zero_right_annotation (Π successor_order_annotation (Π addition_order_left_annotation (Π addition_order_right_annotation (Π multiplication_order_left_annotation (Π multiplication_order_right_annotation B))))))))))))))))))))))))
    (assemble body [122;121;120;119;118;117;116;115;114;113;112;111;110;109;108;107;106;105;104;103;102;101;100;7;6;5;4;3;2;1;0]).
Proof.
  cbn [firstn observation_fields].
  repeat (eapply assemble_prefix_congr; [reflexivity |]).
  apply prefix_option_map_id.
Qed.
Theorem multiplication_order_right_specialization q f (B : Term nat 31) : 0 < q ->
  Typed ε f (telescope_product data_telescope
    (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation (Π order_congruence_annotation (Π order_reflexivity_annotation (Π order_transitivity_annotation (Π addition_zero_annotation (Π addition_successor_annotation (Π multiplication_zero_left_annotation (Π multiplication_successor_annotation (Π multiplication_zero_right_annotation (Π successor_order_annotation (Π addition_order_left_annotation (Π addition_order_right_annotation (Π multiplication_order_left_annotation (Π multiplication_order_right_annotation B)))))))))))))))))))))))) ->
  exists p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22,
    Typed ε p22 (replace (extend p21 (extend p20 (extend p19 (extend p18 (extend p17 (extend p16 (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))))))))))))))))) multiplication_order_right_annotation) /\
    Typed ε (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (table_apply f (data_arguments q)) p0) p1) p2) p3) p4) p5) p6) p7) p8) p9) p10) p11) p12) p13) p14) p15) p16) p17) p18) p19) p20) p21) p22) (replace (extend p22 (extend p21 (extend p20 (extend p19 (extend p18 (extend p17 (extend p16 (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))))))))))))))))) B).
Proof.
  intros Hq Hf.
  destruct (multiplication_order_left_specialization q f _ Hq Hf)
    as [p0 [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [p14 [p15 [p16 [p17 [p18 [p19 [p20 [p21 [Hp Hfnext]]]]]]]]]]]]]]]]]]]]]]].
  destruct (multiplication_order_right_application_certificate q Hq) as [p22 Hpnew].
  rewrite <- (multiplication_order_right_annotation_specialized q p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21) in Hpnew.
  exists p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22. split; [exact Hpnew |].
  rewrite replace_product in Hfnext. pose proof (tApp Hfnext Hpnew) as Hfinal.
  rewrite substitute_transpose in Hfinal. exact Hfinal.
Qed.
(** Public connection to the original full named observation telescope. *)
Theorem full_observation_specialization q body T f : 0 < q ->
  assemble (nAllObs body) [] = Some T -> Typed ε f T ->
  exists B p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22,
    assemble body [122;121;120;119;118;117;116;115;114;113;112;111;110;109;108;107;106;105;104;103;102;101;100;7;6;5;4;3;2;1;0] = Some B /\
    Typed ε (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (table_apply f (data_arguments q)) p0) p1) p2) p3) p4) p5) p6) p7) p8) p9) p10) p11) p12) p13) p14) p15) p16) p17) p18) p19) p20) p21) p22)
      (replace (extend p22 (extend p21 (extend p20 (extend p19 (extend p18 (extend p17 (extend p16 (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))))))))))))))))) B).
Proof.
  intros Hq HT Hf.
  pose proof (multiplication_order_right_prefix_matches_source body) as Hprefix.
  change (assemble (nAllObs body) [] =
    option_map (fun B => telescope_product data_telescope (Π initial_annotation (Π step_annotation (Π addition_annotation (Π multiplication_annotation (Π reflexivity_annotation (Π symmetry_annotation (Π transitivity_annotation (Π successor_annotation (Π addition_congruence_annotation (Π multiplication_congruence_annotation (Π order_congruence_annotation (Π order_reflexivity_annotation (Π order_transitivity_annotation (Π addition_zero_annotation (Π addition_successor_annotation (Π multiplication_zero_left_annotation (Π multiplication_successor_annotation (Π multiplication_zero_right_annotation (Π successor_order_annotation (Π addition_order_left_annotation (Π addition_order_right_annotation (Π multiplication_order_left_annotation (Π multiplication_order_right_annotation B))))))))))))))))))))))))
      (assemble body [122;121;120;119;118;117;116;115;114;113;112;111;110;109;108;107;106;105;104;103;102;101;100;7;6;5;4;3;2;1;0])) in Hprefix.
  rewrite HT in Hprefix.
  destruct (assemble body [122;121;120;119;118;117;116;115;114;113;112;111;110;109;108;107;106;105;104;103;102;101;100;7;6;5;4;3;2;1;0]) as [B|] eqn:HB; [|discriminate].
  cbn [option_map] in Hprefix. inversion Hprefix; subst T.
  destruct (multiplication_order_right_specialization q f B Hq Hf)
    as [p0 [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [p14 [p15 [p16 [p17 [p18 [p19 [p20 [p21 [p22 [Hp Hfinal]]]]]]]]]]]]]]]]]]]]]]]].
  exists B, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22. split; [reflexivity |exact Hfinal].
Qed.
(** The complete closed certificate family is constructed without a typed
    observation term as a premise. This is the reusable finite instance. *)
Theorem observation_certificates q : 0 < q ->
  exists p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22,
    Typed ε p0 (replace (data_substitution q) initial_annotation) /\
    Typed ε p1 (replace (extend p0 (data_substitution q)) step_annotation) /\
    Typed ε p2 (replace (extend p1 (extend p0 (data_substitution q))) addition_annotation) /\
    Typed ε p3 (replace (extend p2 (extend p1 (extend p0 (data_substitution q)))) multiplication_annotation) /\
    Typed ε p4 (replace (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))) reflexivity_annotation) /\
    Typed ε p5 (replace (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))) symmetry_annotation) /\
    Typed ε p6 (replace (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))) transitivity_annotation) /\
    Typed ε p7 (replace (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))) successor_annotation) /\
    Typed ε p8 (replace (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))) addition_congruence_annotation) /\
    Typed ε p9 (replace (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))) multiplication_congruence_annotation) /\
    Typed ε p10 (replace (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))))) order_congruence_annotation) /\
    Typed ε p11 (replace (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))))) order_reflexivity_annotation) /\
    Typed ε p12 (replace (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))))))) order_transitivity_annotation) /\
    Typed ε p13 (replace (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))))))) addition_zero_annotation) /\
    Typed ε p14 (replace (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))))))))) addition_successor_annotation) /\
    Typed ε p15 (replace (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))))))))) multiplication_zero_left_annotation) /\
    Typed ε p16 (replace (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))))))))))) multiplication_successor_annotation) /\
    Typed ε p17 (replace (extend p16 (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))))))))))) multiplication_zero_right_annotation) /\
    Typed ε p18 (replace (extend p17 (extend p16 (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))))))))))))) successor_order_annotation) /\
    Typed ε p19 (replace (extend p18 (extend p17 (extend p16 (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))))))))))))) addition_order_left_annotation) /\
    Typed ε p20 (replace (extend p19 (extend p18 (extend p17 (extend p16 (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))))))))))))))) addition_order_right_annotation) /\
    Typed ε p21 (replace (extend p20 (extend p19 (extend p18 (extend p17 (extend p16 (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))))))))))))))) multiplication_order_left_annotation) /\
    Typed ε p22 (replace (extend p21 (extend p20 (extend p19 (extend p18 (extend p17 (extend p16 (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q))))))))))))))))))))))) multiplication_order_right_annotation).
Proof.
  intro Hq.
  assert (Hsym : forall i j, i < q -> j < q -> Nat.eqb i j = true -> Nat.eqb j i = true).
  { intros i j Hi Hj H. rewrite Nat.eqb_sym. exact H. }
  assert (Htrans : forall i j k, i < q -> j < q -> k < q ->
    Nat.eqb i j = true -> Nat.eqb j k = true -> Nat.eqb i k = true).
  { intros i j k Hi Hj Hk Hij Hjk. apply Nat.eqb_eq in Hij, Hjk.
    apply Nat.eqb_eq. congruence. }
  destruct (Separation.initial_certificate q Hq) as [p0 H0].
  destruct (Separation.step_certificate q Hq) as [p1 H1].
  destruct (FiniteBinaryDomain.addition_certificate q Hq) as [p2 H2].
  destruct (FiniteBinaryDomain.multiplication_certificate q Hq) as [p3 H3].
  destruct (reflexivity_application_certificate q Nat.eqb Hq (fun i _ => Nat.eqb_refl i)) as [p4 H4].
  destruct (symmetry_application_certificate q Nat.eqb Hq Hsym) as [p5 H5].
  destruct (transitivity_application_certificate q Nat.eqb Hq Htrans) as [p6 H6].
  destruct (successor_application_certificate q Hq) as [p7 H7].
  destruct (addition_congruence_application_certificate q Hq) as [p8 H8].
  destruct (multiplication_congruence_application_certificate q Hq) as [p9 H9].
  destruct (order_congruence_application_certificate q Hq) as [p10 H10].
  destruct (order_reflexivity_application_certificate q Hq) as [p11 H11].
  destruct (order_transitivity_application_certificate q Hq) as [p12 H12].
  destruct (addition_zero_application_certificate q Hq) as [p13 H13].
  destruct (addition_successor_application_certificate q Hq) as [p14 H14].
  destruct (multiplication_zero_left_application_certificate q Hq) as [p15 H15].
  destruct (multiplication_successor_application_certificate q Hq) as [p16 H16].
  destruct (multiplication_zero_right_application_certificate q Hq) as [p17 H17].
  destruct (successor_order_application_certificate q Hq) as [p18 H18].
  destruct (addition_order_left_application_certificate q Hq) as [p19 H19].
  destruct (addition_order_right_application_certificate q Hq) as [p20 H20].
  destruct (multiplication_order_left_application_certificate q Hq) as [p21 H21].
  destruct (multiplication_order_right_application_certificate q Hq) as [p22 H22].
  exists p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22.
  split; [exact H0 |].
  split; [rewrite step_annotation_specialized; exact H1 |].
  split; [rewrite addition_annotation_specialized; exact H2 |].
  split; [rewrite multiplication_annotation_specialized; exact H3 |].
  split; [rewrite reflexivity_annotation_specialized; exact H4 |].
  split; [rewrite symmetry_annotation_specialized; exact H5 |].
  split; [rewrite transitivity_annotation_specialized; exact H6 |].
  split; [rewrite successor_annotation_specialized; exact H7 |].
  split; [rewrite addition_congruence_annotation_specialized; exact H8 |].
  split; [rewrite multiplication_congruence_annotation_specialized; exact H9 |].
  split; [rewrite order_congruence_annotation_specialized; exact H10 |].
  split; [rewrite order_reflexivity_annotation_specialized; exact H11 |].
  split; [rewrite order_transitivity_annotation_specialized; exact H12 |].
  split; [rewrite addition_zero_annotation_specialized; exact H13 |].
  split; [rewrite addition_successor_annotation_specialized; exact H14 |].
  split; [rewrite multiplication_zero_left_annotation_specialized; exact H15 |].
  split; [rewrite multiplication_successor_annotation_specialized; exact H16 |].
  split; [rewrite multiplication_zero_right_annotation_specialized; exact H17 |].
  split; [rewrite successor_order_annotation_specialized; exact H18 |].
  split; [rewrite addition_order_left_annotation_specialized; exact H19 |].
  split; [rewrite addition_order_right_annotation_specialized; exact H20 |].
  split; [rewrite multiplication_order_left_annotation_specialized; exact H21 |].
  rewrite multiplication_order_right_annotation_specialized. exact H22.
Qed.
Definition law_telescope : telescope 8 31 :=
  (tel_cons 4 initial_annotation (tel_cons 5 step_annotation (tel_cons 5 addition_annotation (tel_cons 5 multiplication_annotation (tel_cons 5 reflexivity_annotation (tel_cons 5 symmetry_annotation (tel_cons 5 transitivity_annotation (tel_cons 5 successor_annotation (tel_cons 5 addition_congruence_annotation (tel_cons 5 multiplication_congruence_annotation (tel_cons 5 order_congruence_annotation (tel_cons 5 order_reflexivity_annotation (tel_cons 5 order_transitivity_annotation (tel_cons 5 addition_zero_annotation (tel_cons 5 addition_successor_annotation (tel_cons 5 multiplication_zero_left_annotation (tel_cons 5 multiplication_successor_annotation (tel_cons 5 multiplication_zero_right_annotation (tel_cons 5 successor_order_annotation (tel_cons 5 addition_order_left_annotation (tel_cons 5 addition_order_right_annotation (tel_cons 5 multiplication_order_left_annotation (tel_cons 5 multiplication_order_right_annotation tel_nil))))))))))))))))))))))).
Theorem observation_arguments q : 0 < q ->
  exists ps τ, length ps = 23 /\
    arguments ε law_telescope (data_substitution q) ps τ.
Proof.
  intro Hq. destruct (observation_certificates q Hq)
    as [p0 [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [p14 [p15 [p16 [p17 [p18 [p19 [p20 [p21 [p22 [H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 H22]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
  exists [p0;p1;p2;p3;p4;p5;p6;p7;p8;p9;p10;p11;p12;p13;p14;p15;p16;p17;p18;p19;p20;p21;p22], (extend p22 (extend p21 (extend p20 (extend p19 (extend p18 (extend p17 (extend p16 (extend p15 (extend p14 (extend p13 (extend p12 (extend p11 (extend p10 (extend p9 (extend p8 (extend p7 (extend p6 (extend p5 (extend p4 (extend p3 (extend p2 (extend p1 (extend p0 (data_substitution q)))))))))))))))))))))))). split; [reflexivity |].
  unfold law_telescope. repeat (econstructor; [eassumption |]). constructor.
Qed.
End FiniteDomainPrefix.
