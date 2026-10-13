(** The eight finite observation data arguments, in the original dependent
    order. This is a checked prefix, not yet the twenty-three law arguments. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R.functional Require Import DirectRCodes.
From Interpretation_of_R Require Import DirectRKernel DirectRStructural DirectRLogic
  DirectRFiniteTables DirectRBinaryTables DirectRRelationTables DirectRFiniteCertificates
  DirectRTelescopeArguments.
Import ListNotations.
Module FiniteData.
Import Codes Core Structural NegativeLogic FiniteTables BinaryTables RelationTables TelescopeArguments.
Definition data_telescope : telescope 0 8 :=
  tel_cons 0 (𝓤 1)
  (tel_cons 1 V0
  (tel_cons 2 (Arrow (shift V0) (shift V0))
  (tel_cons 2 (Arrow (shift (shift V0)) (Arrow (shift (shift V0)) (shift (shift V0))))
  (tel_cons 2 (Arrow (shift (shift (shift V0)))
    (Arrow (shift (shift (shift V0))) (shift (shift (shift V0)))))
  (tel_cons 2 (Arrow (shift (shift (shift (shift V0)))) (𝓤 4))
  (tel_cons 2 (Arrow (shift (shift (shift (shift (shift V0)))))
    (Arrow (shift (shift (shift (shift (shift V0))))) (𝓤 1)))
  (tel_cons 2 (Arrow (shift (shift (shift (shift (shift (shift V0))))))
    (Arrow (shift (shift (shift (shift (shift (shift V0)))))) (𝓤 1))) tel_nil))))))).

(** This equality is with the actual named source prefix, not a newly chosen
    observation signature. It holds for an arbitrary remaining named body. *)
Theorem data_prefix_matches_source body :
  assemble (npis (firstn 8 observation_fields) body) [] =
  option_map (telescope_product data_telescope) (assemble body [7;6;5;4;3;2;1;0]).
Proof.
  cbn [npis firstn observation_fields fold_right fst snd assemble lookup Nat.eqb].
  destruct (assemble body [7;6;5;4;3;2;1;0]); reflexivity.
Qed.
Definition data_arguments q : list closed_term :=
  [selector_type q; point q 0; capped_successor q; capped_addition q;
   capped_multiplication q; FiniteCertificates.predicate q;
   relation_table q Nat.eqb; relation_table q Nat.leb].
Definition data_substitution q : Fin 8 -> closed_term :=
  extend (relation_table q Nat.leb) (extend (relation_table q Nat.eqb)
    (extend (FiniteCertificates.predicate q) (extend (capped_multiplication q)
      (extend (capped_addition q) (extend (capped_successor q)
        (extend (point q 0) (extend (selector_type q) empty))))))).
Theorem data_arguments_typed q : 0 < q ->
  arguments ε data_telescope empty (data_arguments q) (data_substitution q).
Proof.
  intro Hq. unfold data_telescope, data_arguments, data_substitution.
  apply arguments_cons.
  - change (Typed ε (selector_type q) (𝓤 1)). destruct q; [lia |apply selector_type_formation].
  - apply arguments_cons.
    + change (Typed ε (point q 0) (selector_type q)). apply point_typed.
    + apply arguments_cons.
      * rewrite !replace_arrow.
        change (Typed ε (capped_successor q) (Arrow (selector_type q) (selector_type q))).
        apply capped_successor_typed.
      * apply arguments_cons.
        -- rewrite !replace_arrow. change (Typed ε (capped_addition q)
             (Arrow (selector_type q) (Arrow (selector_type q) (selector_type q)))).
           apply capped_addition_typed.
        -- apply arguments_cons.
           ++ rewrite !replace_arrow. change (Typed ε (capped_multiplication q)
                (Arrow (selector_type q) (Arrow (selector_type q) (selector_type q)))).
              apply capped_multiplication_typed.
           ++ apply arguments_cons.
              ** rewrite !replace_arrow. change (Typed ε (FiniteCertificates.predicate q) (Arrow (selector_type q) (𝓤 4))).
                 apply FiniteCertificates.predicate_typed. exact Hq.
              ** apply arguments_cons.
                 --- rewrite !replace_arrow. change (Typed ε (relation_table q Nat.eqb)
                       (Arrow (selector_type q) (Arrow (selector_type q) (𝓤 1)))).
                     apply relation_table_typed.
                 --- apply arguments_cons.
                     +++ rewrite !replace_arrow. change (Typed ε (relation_table q Nat.leb)
                           (Arrow (selector_type q) (Arrow (selector_type q) (𝓤 1)))).
                         apply relation_table_typed.
                     +++ apply arguments_nil.
Qed.
Theorem data_specialization q f (B : Term nat 8) : 0 < q ->
  Typed ε f (telescope_product data_telescope B) ->
  Typed ε (table_apply f (data_arguments q)) (replace (data_substitution q) B).
Proof.
  intros Hq Hf. eapply arguments_application; [apply data_arguments_typed; exact Hq |].
  rewrite (replace_ext empty (@var nat 0)) by (intro i; exact (match i with end)).
  rewrite replace_var. exact Hf.
Qed.
Definition initial_annotation : Term nat 8 :=
  app (shift (shift V0)) (shift (shift (shift (shift (shift (shift V0)))))).
Theorem initial_prefix_matches_source body :
  assemble (npis (firstn 9 observation_fields) body) [] =
  option_map (fun B => telescope_product data_telescope (Π initial_annotation B))
    (assemble body [100;7;6;5;4;3;2;1;0]).
Proof.
  cbn [npis firstn observation_fields fold_right fst snd assemble lookup Nat.eqb].
  destruct (assemble body [100;7;6;5;4;3;2;1;0]); reflexivity.
Qed.
Theorem initial_specialization q f (B : Term nat 9) : 0 < q ->
  Typed ε f (telescope_product data_telescope (Π initial_annotation B)) ->
  exists p,
    Typed ε p (replace (data_substitution q) initial_annotation) /\
    Typed ε (app (table_apply f (data_arguments q)) p)
      (replace (extend p (data_substitution q)) B).
Proof.
  intros Hq Hf. pose proof (data_specialization q f _ Hq Hf) as Hdata.
  destruct (FiniteCertificates.initial_certificate q Hq) as [p Hp].
  exists p. split; [exact Hp |].
  rewrite replace_product in Hdata.
  pose proof (tApp Hdata Hp) as H. rewrite substitute_transpose in H. exact H.
Qed.
Definition step_annotation : Term nat 9 :=
  FiniteCertificates.step_guard (shift (shift (shift (shift (shift (shift (shift (shift V0))))))))
    (shift (shift (shift (shift (shift (shift V0)))))) (shift (shift (shift V0))).
Theorem step_prefix_matches_source body :
  assemble (npis (firstn 10 observation_fields) body) [] =
  option_map (fun B => telescope_product data_telescope
    (Π initial_annotation (Π step_annotation B)))
    (assemble body [101;100;7;6;5;4;3;2;1;0]).
Proof.
  cbn [npis firstn observation_fields fold_right fst snd assemble lookup Nat.eqb].
  destruct (assemble body [101;100;7;6;5;4;3;2;1;0]); reflexivity.
Qed.
Lemma step_annotation_specialized q p :
  replace (extend p (data_substitution q)) step_annotation = FiniteCertificates.step_type q.
Proof.
  unfold step_annotation, FiniteCertificates.step_guard. rewrite replace_product, replace_arrow,
    !replace_application.
  cbn [replace shift rename V0 extend fin_match transpose weak data_substitution].
  change (Π (selector_type q)
    (Arrow (app (shift (FiniteCertificates.predicate q)) V0)
      (app (shift (FiniteCertificates.predicate q)) (app (shift (capped_successor q)) V0))) =
    FiniteCertificates.step_type q).
  assert (Hshift : forall c : closed_term, shift c = @lift_closed 1 c).
  { intro c. rewrite lift_closed_shift, lift_closed_zero. reflexivity. }
  rewrite !Hshift. reflexivity.
Qed.
Theorem step_specialization q f (B : Term nat 10) : 0 < q ->
  Typed ε f (telescope_product data_telescope (Π initial_annotation (Π step_annotation B))) ->
  exists p0 p1,
    Typed ε p0 (replace (data_substitution q) initial_annotation) /\
    Typed ε p1 (replace (extend p0 (data_substitution q)) step_annotation) /\
    Typed ε (app (app (table_apply f (data_arguments q)) p0) p1)
      (replace (extend p1 (extend p0 (data_substitution q))) B).
Proof.
  intros Hq Hf. destruct (initial_specialization q f _ Hq Hf) as [p0 [Hp0 H0]].
  destruct (FiniteCertificates.step_certificate q Hq) as [p1 Hp1].
  rewrite <- (step_annotation_specialized q p0) in Hp1.
  exists p0, p1. split; [exact Hp0 |]. split; [exact Hp1 |].
  rewrite replace_product in H0. pose proof (tApp H0 Hp1) as H.
  rewrite substitute_transpose in H. exact H.
Qed.
End FiniteData.
