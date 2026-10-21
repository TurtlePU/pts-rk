From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import ChurchSyntax TypedHOASFaithful
  PHOASTelescope TarskiPalette.
Import Context.

(** A reusable finite block of independently realized field families.
    Every family refers to the ORIGINAL base context, not to the added
    fields. Both the base realization and the new values are actual CLOSED
    original terms with independent original typing proofs. This builder
    does not generate the field families or assume a source quoter. *)
Module RealizedSignature.
Module CS := ChurchSyntax.ChurchSyntax.
Module TF := TypedHOASFaithful.TypedHOASFaithful.
Module PT := PHOASTelescope.PHOASTelescope.
Module PL := TarskiPalette.TarskiPalette.

Definition context count {m} (G : Ctx nat m) (sig : nat -> Term nat m) :=
  PL.block count 0 G sig.
Definition inherited count {m} (t : Term nat m) : Term nat (count+m) :=
  rename (@up count m) t.
Definition field count {m} (i : Fin count) : Term nat (count+m) :=
  var (CS.front i).
Definition closed_fill count {m} (base : Fin m -> Term nat 0)
    (values : nat -> Term nat 0) : Fin (count+m) -> Term nat 0 :=
  PL.fill_block count 0 base values.
Definition fill count {m n} (base : Fin m -> Term nat 0)
    (values : nat -> Term nat 0) (i : Fin (count+m)) : Term nat n :=
  PT.lift_closed (closed_fill count base values i).

Theorem context_wf count m (G : Ctx nat m) sig ranks :
  @wf nat RankSorts m G ->
  (forall j, j < count -> @typ nat RankSorts m G (sig j) (𝓤 (ranks j))) ->
  @wf nat RankSorts _ (context count G sig).
Proof.
  intros HG HF; unfold context; apply PL.block_wf with (rank := ranks);
    [exact HG | intros; apply HF; lia].
Qed.

Theorem context_normal count m (G : Ctx nat m) sig :
  PT.normal_context G = true ->
  (forall j, j < count -> normalb (sig j) = true) ->
  PT.normal_context (context count G sig) = true.
Proof.
  intros HG HF; unfold context; apply PL.block_normal;
    [exact HG | intros; apply HF; lia].
Qed.

Theorem inherited_typed count m (G : Ctx nat m) sig t T :
  @typ nat RankSorts m G t T ->
  @typ nat RankSorts _ (context count G sig) (inherited count t) (inherited count T).
Proof. apply PL.block_source_typing. Qed.

Theorem field_typed count m (G : Ctx nat m) sig (i : Fin count) :
  @typ nat RankSorts _ (context count G sig) (@field count m i)
    (inherited count (sig (CS.fin_index i))).
Proof. exact (PL.block_front_typing count i 0 m G sig). Qed.

Theorem closed_fill_typed count m (G : Ctx nat m) sig base values :
  TypedSub G ε base ->
  (forall j, j < count -> @typ nat RankSorts 0 ε (values j) (replace base (sig j))) ->
  TypedSub (context count G sig) ε (closed_fill count base values).
Proof.
  intros HB HV; apply PL.fill_block_typed; [exact HB | intros; apply HV; lia].
Qed.

Theorem fill_typed count m (G : Ctx nat m) sig base values n (H : Ctx nat n) :
  TypedSub G ε base ->
  (forall j, j < count -> @typ nat RankSorts 0 ε (values j) (replace base (sig j))) ->
  TypedSub (context count G sig) H (@fill count m n base values).
Proof.
  intros HB HV i; unfold fill, PT.lift_closed; rewrite <- rename_replace.
  apply typing_rename with (G := ε).
  - intro j; inversion j.
  - apply closed_fill_typed; assumption.
Qed.

Theorem fill_field count m n base values (i : Fin count) :
  replace (@fill count m n base values) (@field count m i) =
    PT.lift_closed (values (CS.fin_index i)).
Proof.
  unfold field; cbn [replace]; unfold fill, closed_fill.
  rewrite PL.fill_block_front; reflexivity.
Qed.

Theorem fill_inherited count m n base values (t : Term nat m) :
  replace (@fill count m n base values) (inherited count t) =
    PT.lift_closed (replace base t).
Proof.
  unfold inherited; rewrite replace_rename; unfold fill, PT.lift_closed.
  rewrite rename_replace; apply replace_ext; intro i.
  unfold closed_fill; rewrite PL.fill_block_source; reflexivity.
Qed.

Theorem fill_replace count m n p base values (sigma : Fin n -> Term nat p) i :
  replace sigma (@fill count m n base values i) = @fill count m p base values i.
Proof. apply PT.lift_closed_replace. Qed.

Theorem filled_field_normal count m n base values (i : Fin count) :
  normalb (values (CS.fin_index i)) = true ->
  normalb (replace (@fill count m n base values) (@field count m i)) = true.
Proof. intro H; rewrite fill_field; unfold PT.lift_closed; rewrite TF.normalb_rename; exact H. Qed.

Theorem filled_typing count m (G : Ctx nat m) sig base values n (H : Ctx nat n) t T :
  TypedSub G ε base ->
  (forall j, j < count -> @typ nat RankSorts 0 ε (values j) (replace base (sig j))) ->
  @typ nat RankSorts _ (context count G sig) t T ->
  @typ nat RankSorts n H (replace (fill count base values) t) (replace (fill count base values) T).
Proof. intros HB HV HT; eapply typing_replace; [exact HT | apply fill_typed; assumption]. Qed.

Theorem close_typing count m (G : Ctx nat m) sig ranks t T :
  @wf nat RankSorts m G ->
  (forall j, j < count -> @typ nat RankSorts m G (sig j) (𝓤 (ranks j))) ->
  @typ nat RankSorts _ (context count G sig) t T ->
  @typ nat RankSorts 0 ε (PT.close_term (context count G sig) t)
    (PT.close_type (context count G sig) T).
Proof.
  intros HG HF HT; apply PT.close_typing; [apply context_wf with (ranks := ranks); assumption | exact HT].
Qed.

Theorem close_normal count m (G : Ctx nat m) sig t :
  PT.normal_context G = true ->
  (forall j, j < count -> normalb (sig j) = true) ->
  normalb t = true -> normalb (PT.close_term (context count G sig) t) = true.
Proof.
  intros HG HF Ht; apply PT.close_normal; [apply context_normal; assumption | exact Ht].
Qed.

(** Actual applications of the closed package recover its literal
    instantiated body. This is ordinary telescope application, not a
    claimed interpretation of source syntax. *)
Theorem run_closed_recovers count m (G : Ctx nat m) sig base values n t :
  reduces_to nat n
    (PT.run (context count G sig) (@fill count m n base values)
      (PT.lift_closed (PT.close_term (context count G sig) t)))
    (replace (fill count base values) t).
Proof. apply PT.run_closed_term. Qed.

Theorem run_typed count m (G : Ctx nat m) sig base values n (H : Ctx nat n) q T :
  TypedSub G ε base ->
  (forall j, j < count -> @typ nat RankSorts 0 ε (values j) (replace base (sig j))) ->
  @typ nat RankSorts n H q (PT.lift_closed (PT.close_type (context count G sig) T)) ->
  @typ nat RankSorts n H (PT.run (context count G sig) (fill count base values) q)
    (replace (fill count base values) T).
Proof.
  intros HB HV HQ; apply PT.run_typing; [apply fill_typed; assumption | exact HQ].
Qed.

Print Assumptions context_wf.
Print Assumptions context_normal.
Print Assumptions inherited_typed.
Print Assumptions field_typed.
Print Assumptions closed_fill_typed.
Print Assumptions fill_typed.
Print Assumptions fill_field.
Print Assumptions fill_inherited.
Print Assumptions fill_replace.
Print Assumptions filled_field_normal.
Print Assumptions filled_typing.
Print Assumptions close_typing.
Print Assumptions close_normal.
Print Assumptions run_closed_recovers.
Print Assumptions run_typed.
End RealizedSignature.
