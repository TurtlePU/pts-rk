From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting DefEq.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import CheckedContextualFields TarskiPalette
  ChurchSyntax ChurchSyntaxFaithful PHOASTelescope TypedHOASFaithful
  ContextualTelescope ContextualEqualityExtension CheckedEqualityFields.
Import Context ListNotations.

(** Deterministic equality-only DAG layers indexed solely by a finite vector
    of NUMERIC budgets and an independently fixed realized base signature.
    Previous syntax is embedded, never regenerated or merged. *)
Module CheckedEqualityLayers.
Module CF := CheckedContextualFields.CheckedContextualFields.
Module PL := TarskiPalette.TarskiPalette.
Module CS := ChurchSyntax.ChurchSyntax.
Module SF := ChurchSyntaxFaithful.
Module PT := PHOASTelescope.PHOASTelescope.
Module TF := TypedHOASFaithful.TypedHOASFaithful.
Module CT := ContextualTelescope.ContextualTelescope.
Module CX := ContextualEqualityExtension.ContextualEqualityExtension.
Module EF := CheckedEqualityFields.CheckedEqualityFields.

Record budget := Budget { length_bound : nat; node_bound : nat; literal_bound : nat }.
Record realization : Type := Realization {
  width : nat;
  signature : Ctx nat width;
  identity_fill : Fin width -> Term nat 0;
  signature_wf : @wf nat RankSorts width signature;
  signature_normal : PT.normal_context signature = true;
  identity_typed : TypedSub signature ε identity_fill
}.

Definition extend (b : budget) (R : realization) : realization.
Proof.
  refine {| width := CF.count (length_bound b) (node_bound b) (literal_bound b) (signature R) (identity_fill R) + width R;
    signature := CF.context (length_bound b) (node_bound b) (literal_bound b) (signature R) (identity_fill R);
    identity_fill := CF.fill (length_bound b) (node_bound b) (literal_bound b) (signature R) (identity_fill R) |}.
  - apply CF.context_wf, signature_wf.
  - apply CF.context_normal; [apply signature_wf | apply signature_normal].
  - apply CF.fill_typed; [apply signature_wf | apply identity_typed].
Defined.
Definition insertion b R : Fin (width R) -> Fin (width (extend b R)) := up.

Theorem extend_typing b R t T :
  @typ nat RankSorts _ (signature R) t T ->
  @typ nat RankSorts _ (signature (extend b R)) (rename (insertion b R) t) (rename (insertion b R) T).
Proof. intro H; apply PL.block_source_typing; exact H. Qed.
Theorem insertion_typed b R : TypedRen (signature R) (signature (extend b R)) (insertion b R).
Proof.
  intro i; rewrite replace_as_rename.
  change (typ (signature (extend b R)) (rename (insertion b R) (var i))
    (rename (insertion b R) (signature R !! i))).
  apply extend_typing, typ_var.
Qed.
Theorem insertion_fill b R i : identity_fill (extend b R) (insertion b R i) = identity_fill R i.
Proof. apply CF.fill_source. Qed.
Theorem insertion_injective b R i j : insertion b R i = insertion b R j -> i=j.
Proof. apply SF.up_injective. Qed.
Lemma block_index count : forall start n (G : Ctx nat n) fields i,
  PL.block count start G fields !! up i = rename (@up count n) (G !! i).
Proof.
  induction count; intros start n G fields i; cbn [PL.block up].
  - rewrite rename_id; reflexivity.
  - change (shift (PL.block count (S start) G fields !! up i) = rename (@up (S count) n) (G !! i)).
    rewrite IHcount, shift_up; reflexivity.
Qed.
Theorem insertion_index b R i :
  signature (extend b R) !! insertion b R i = rename (insertion b R) (signature R !! i).
Proof. apply block_index. Qed.

Fixpoint build (bs : list budget) (R : realization) : realization :=
  match bs with [] => R | b::tail => build tail (extend b R) end.
Fixpoint embedding (bs : list budget) (R : realization) : Fin (width R) -> Fin (width (build bs R)) :=
  match bs with [] => fun i => i | b::tail => fun i => embedding tail (extend b R) (insertion b R i) end.

Theorem build_typing bs : forall R t T,
  @typ nat RankSorts _ (signature R) t T ->
  @typ nat RankSorts _ (signature (build bs R)) (rename (embedding bs R) t) (rename (embedding bs R) T).
Proof.
  induction bs as [|b bs IH]; intros R t T HT; cbn [build embedding].
  - rewrite !rename_id; exact HT.
  - pose proof (IH (extend b R) (rename (insertion b R) t) (rename (insertion b R) T)
      (extend_typing b R t T HT)) as H.
    rewrite !rename_comp in H; exact H.
Qed.
Theorem embedding_typed bs R : TypedRen (signature R) (signature (build bs R)) (embedding bs R).
Proof.
  intro i; rewrite replace_as_rename.
  change (typ (signature (build bs R)) (rename (embedding bs R) (var i))
    (rename (embedding bs R) (signature R !! i))).
  apply build_typing, typ_var.
Qed.
Theorem embedding_fill bs : forall R i,
  identity_fill (build bs R) (embedding bs R i) = identity_fill R i.
Proof.
  induction bs as [|b bs IH]; intros R i; cbn [build embedding]; [reflexivity |].
  rewrite IH; apply insertion_fill.
Qed.
Theorem embedding_injective bs : forall R i j, embedding bs R i = embedding bs R j -> i=j.
Proof.
  induction bs as [|b bs IH]; intros R i j HE; [exact HE |].
  cbn [embedding] in HE; apply IH in HE; apply insertion_injective in HE; exact HE.
Qed.
Theorem embedding_index bs : forall R i,
  signature (build bs R) !! embedding bs R i = rename (embedding bs R) (signature R !! i).
Proof.
  induction bs as [|b bs IH]; intros R i; cbn [build embedding].
  - rewrite rename_id; reflexivity.
  - rewrite IH, insertion_index, rename_comp; reflexivity.
Qed.
Theorem filled_embedding bs R t :
  replace (identity_fill (build bs R)) (rename (embedding bs R) t) = replace (identity_fill R) t.
Proof. rewrite replace_rename; apply replace_ext, embedding_fill. Qed.
Theorem embedding_normal bs R t :
  normalb (rename (embedding bs R) t) = normalb t.
Proof. apply TF.normalb_rename. Qed.
Theorem embedding_preserves_recovery bs R t u :
  reduces_to nat 0 (replace (identity_fill R) t) u ->
  reduces_to nat 0 (replace (identity_fill (build bs R)) (rename (embedding bs R) t)) u.
Proof. rewrite filled_embedding; trivial. Qed.

Theorem build_wf bs R : @wf nat RankSorts _ (signature (build bs R)).
Proof. apply signature_wf. Qed.
Theorem build_normal bs R : PT.normal_context (signature (build bs R)) = true.
Proof. apply signature_normal. Qed.
Theorem build_fill_typed bs R : TypedSub (signature (build bs R)) ε (identity_fill (build bs R)).
Proof. apply identity_typed. Qed.

Definition request_budget {n} (x : CF.candidate n) := Budget (CF.depth x) (CF.node_budget x) (CF.literal_budget x).
Definition request_lookup (R : realization) (x : CF.candidate (width R)) :=
  CF.lookup (CF.depth x) (CF.node_budget x) (CF.literal_budget x) (signature R) (identity_fill R) x.
Theorem request_available R x : CF.accepted x 0 (signature R) ε (identity_fill R) = true ->
  exists i, request_lookup R x = Some i.
Proof. apply CF.lookup_complete. Qed.
Theorem request_typed R x i : request_lookup R x = Some i ->
  @typ nat RankSorts _ (signature (extend (request_budget x) R)) (var (CS.front i))
    (rename (insertion (request_budget x) R) (CF.field x)).
Proof. apply CF.lookup_typed. Qed.
Theorem request_fill R x i : request_lookup R x = Some i ->
  identity_fill (extend (request_budget x) R) (CS.front i) = CF.value (identity_fill R) x.
Proof. apply CF.lookup_filled. Qed.

Record allocation (R : realization) (x : CF.candidate (width R)) : Type := Allocation {
  slot : Fin (CF.count (CF.depth x) (CF.node_budget x) (CF.literal_budget x)
    (signature R) (identity_fill R));
  slot_found : request_lookup R x = Some slot
}.
Arguments slot {R x} _.
Arguments slot_found {R x} _.

(** The slot is obtained by inspecting the executable option. Coverage is
    used ONLY to eliminate the impossible None branch, never to extract a
    witness from an erased existential proof. *)
Definition allocate R x (HX : CF.accepted x 0 (signature R) ε (identity_fill R) = true) : allocation R x.
Proof.
  destruct (request_lookup R x) as [i|] eqn:HI.
  - exact {| slot := i; slot_found := HI |}.
  - exfalso; destruct (request_available R x HX) as [i HE]; rewrite HI in HE; discriminate.
Defined.

Definition allocate_original c R rs (D : CT.telescope (width R) rs) e
    (HD : CT.formed (signature R) D) (HN : CT.normal_annotations D = true)
    (HC : @typ nat RankSorts _ (CT.context D (signature R)) (EF.carrier e) (𝓤 c))
    (HU : @typ nat RankSorts _ (CT.context D (signature R)) (EF.left e) (EF.carrier e))
    (HV : @typ nat RankSorts _ (CT.context D (signature R)) (EF.right e) (EF.carrier e))
    (HNC : normalb (EF.carrier e) = true) (HNU : normalb (EF.left e) = true)
    (HNV : normalb (EF.right e) = true)
    (HE : def_equiv nat _ (CX.filled (identity_fill R) (EF.left e))
      (CX.filled (identity_fill R) (EF.right e))) : allocation R (CF.pack D e).
Proof.
  destruct (request_lookup R (CF.pack D e)) as [i|] eqn:HI.
  - exact {| slot := i; slot_found := HI |}.
  - exfalso.
    destruct (CF.original_telescope_covered c (width R) rs (signature R) D (identity_fill R) e
      (signature_wf R) (identity_typed R) HD HN HC HU HV HNC HNU HNV HE) as [i HF].
    change (request_lookup R (CF.pack D e) = Some i) in HF; rewrite HI in HF; discriminate.
Defined.

Theorem allocated_typed R x (a : allocation R x) :
  @typ nat RankSorts _ (signature (extend (request_budget x) R)) (var (CS.front (slot a)))
    (rename (insertion (request_budget x) R) (CF.field x)).
Proof. apply request_typed, slot_found. Qed.
Theorem allocated_fill R x (a : allocation R x) :
  identity_fill (extend (request_budget x) R) (CS.front (slot a)) = CF.value (identity_fill R) x.
Proof. apply request_fill, slot_found. Qed.

(** Numeric vectors are ordinary executable data. The valid realization
    record verifies a fixed base, not the success of any future quotation. *)
Definition empty : realization.
Proof.
  refine {| width := 0; signature := ε; identity_fill := fun i => match i with end |}.
  - constructor.
  - reflexivity.
  - intro i; inversion i.
Defined.
Example empty_vector_keeps_empty : width (build [] empty) = 0.
Proof. reflexivity. Qed.
Definition reflexive_sort : CF.candidate 0 := CF.leaf (EF.Desc 0 (𝓤 0) (𝓤 0) (𝓤 0)).
Example reflexive_sort_accepted : CF.accepted reflexive_sort 0 ε ε (identity_fill empty) = true.
Proof. vm_compute; reflexivity. Qed.
Example first_numeric_layer_width : width (build [Budget 0 1 0] empty) = 1.
Proof. vm_compute; reflexivity. Qed.
Example computed_allocation_slot : CS.fin_index (slot (allocate empty reflexive_sort reflexive_sort_accepted)) = 0.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions extend_typing.
Print Assumptions insertion_typed.
Print Assumptions insertion_fill.
Print Assumptions insertion_injective.
Print Assumptions insertion_index.
Print Assumptions build_typing.
Print Assumptions embedding_typed.
Print Assumptions embedding_fill.
Print Assumptions embedding_injective.
Print Assumptions embedding_index.
Print Assumptions filled_embedding.
Print Assumptions embedding_normal.
Print Assumptions embedding_preserves_recovery.
Print Assumptions build_wf.
Print Assumptions build_normal.
Print Assumptions build_fill_typed.
Print Assumptions request_available.
Print Assumptions request_typed.
Print Assumptions request_fill.
Print Assumptions allocate.
Print Assumptions allocate_original.
Print Assumptions allocated_typed.
Print Assumptions allocated_fill.
End CheckedEqualityLayers.
