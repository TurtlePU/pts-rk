From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting DefEq.
From PTSrk.NormalizationComplexity Require Import Rank Bounds Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import OriginalTypecheck FullConversion
  BoundedSyntaxEnumeration IndexedEquality RealizedEquality TarskiPalette
  ChurchSyntax PHOASTelescope.
Import Context ListNotations RankEstimate.

(** An executable EQUALITY-ONLY layer over a fixed preceding context.
    Every candidate comes from the complete finite original syntax vocabulary.
    Acceptance checks independent original typing and equality of ACTUAL
    filled endpoints. No quoted value or source program is a new field. *)
Module CheckedEqualityFields.
Module OT := OriginalTypecheck.OriginalTypecheck.
Module FC := FullConversion.FullConversion.
Module EN := BoundedSyntaxEnumeration.BoundedSyntaxEnumeration.
Module IE := IndexedEquality.IndexedEquality.
Module RE := RealizedEquality.RealizedEquality.
Module PL := TarskiPalette.TarskiPalette.
Module CS := ChurchSyntax.ChurchSyntax.
Module PT := PHOASTelescope.PHOASTelescope.

Record descriptor n : Type := Desc {
  level : nat;
  carrier : Term nat n;
  left : Term nat n;
  right : Term nat n
}.
Arguments Desc {n} _ _ _ _.
Arguments level {n} _.
Arguments carrier {n} _.
Arguments left {n} _.
Arguments right {n} _.

Definition descriptors s n k : list (descriptor n) :=
  flat_map (fun d => flat_map (fun C => flat_map (fun u =>
    map (fun v => Desc d C u v) (EN.sized_terms s n k))
      (EN.sized_terms s n k)) (EN.sized_terms s n k)) (seq 0 (S k)).
Definition node_budget {n} (x : descriptor n) :=
  Nat.max (nodes (carrier x)) (Nat.max (nodes (left x)) (nodes (right x))).
Definition literal_budget {n} (x : descriptor n) :=
  Nat.max (level x) (Nat.max (maxRankLiteral (carrier x))
    (Nat.max (maxRankLiteral (left x)) (maxRankLiteral (right x)))).

Theorem descriptors_iff s n k (x : descriptor n) :
  In x (descriptors s n k) <-> node_budget x <= s /\ literal_budget x <= k.
Proof.
  unfold descriptors; split.
  - intro HX; apply in_flat_map in HX; destruct HX as [d [HD HX]].
    apply in_flat_map in HX; destruct HX as [C [HC HX]].
    apply in_flat_map in HX; destruct HX as [u [HU HV]].
    apply in_map_iff in HV; destruct HV as [v [E HV]]; subst x.
    apply in_seq in HD; apply EN.sized_terms_iff in HC, HU, HV.
    unfold node_budget, literal_budget; cbn [carrier left right level].
    destruct HC as [HCS HCK], HU as [HUS HUK], HV as [HVS HVK]; split; lia.
  - destruct x as [d C u v]; unfold node_budget, literal_budget; cbn [carrier left right level]; intro H.
    apply in_flat_map; exists d; split; [apply in_seq; lia |].
    apply in_flat_map; exists C; split; [apply EN.sized_terms_iff; lia |].
    apply in_flat_map; exists u; split; [apply EN.sized_terms_iff; lia |].
    apply in_map; apply EN.sized_terms_iff; lia.
Qed.

Definition accepted {m n} (G : Ctx nat m) (H : Ctx nat n)
    (sigma : Fin m -> Term nat n) (x : descriptor m) : bool :=
  match OT.type_sort G (carrier x) with
  | None => false
  | Some _ => normalb (carrier x) && normalb (left x) && normalb (right x) &&
      OT.check G (left x) (carrier x) && OT.check G (right x) (carrier x) &&
      FC.convertibleb H (replace sigma (left x)) (replace sigma (right x))
  end.
Definition field {n} (x : descriptor n) := IE.eq_type (level x) (carrier x) (left x) (right x).
Definition value {m n} (H : Ctx nat n) (sigma : Fin m -> Term nat n) (x : descriptor m) :=
  RE.normal_reflexivity (level x) H (replace sigma (carrier x)) (replace sigma (left x)).
Definition field_rank {n} (G : Ctx nat n) (x : descriptor n) :=
  Nat.max ((match OT.type_sort G (carrier x) with Some c => c | None => 0 end)+2) (level x+1).

Theorem accepted_sound m n (G : Ctx nat m) (H : Ctx nat n) sigma x :
  @wf nat RankSorts m G -> accepted G H sigma x = true ->
  exists c, OT.type_sort G (carrier x) = Some c /\
    @typ nat RankSorts m G (carrier x) (𝓤 c) /\
    @typ nat RankSorts m G (left x) (carrier x) /\
    @typ nat RankSorts m G (right x) (carrier x) /\
    normalb (carrier x) = true /\ normalb (left x) = true /\ normalb (right x) = true /\
    def_equiv nat n (replace sigma (left x)) (replace sigma (right x)).
Proof.
  intros HG; unfold accepted; destruct (OT.type_sort G (carrier x)) as [c|] eqn:HC; [| discriminate].
  repeat rewrite andb_true_iff; intros [[[[[HN HU] HV] HTU] HTV] HE].
  exists c; repeat split; try assumption.
  - apply OT.type_sort_sound; assumption.
  - apply OT.check_sound; assumption.
  - apply OT.check_sound; assumption.
  - unfold FC.convertibleb in HE; destruct (FC.join_attempt H (replace sigma (left x)) (replace sigma (right x))) as [j|];
      [apply FC.joining_sound with (j := j) | discriminate].
Qed.

Theorem accepted_complete c m n (G : Ctx nat m) (H : Ctx nat n) sigma x :
  @wf nat RankSorts m G -> @wf nat RankSorts n H -> TypedSub G H sigma ->
  @typ nat RankSorts m G (carrier x) (𝓤 c) ->
  @typ nat RankSorts m G (left x) (carrier x) ->
  @typ nat RankSorts m G (right x) (carrier x) ->
  normalb (carrier x) = true -> normalb (left x) = true -> normalb (right x) = true ->
  def_equiv nat n (replace sigma (left x)) (replace sigma (right x)) ->
  accepted G H sigma x = true.
Proof.
  intros HG HH HS HC HU HV HNC HNU HNV HE; unfold accepted.
  rewrite (OT.type_sort_complete m G (carrier x) c HG HC), HNC, HNU, HNV,
    (OT.check_complete m G (left x) (carrier x) HG HU),
    (OT.check_complete m G (right x) (carrier x) HG HV); cbn.
  apply (proj2 (FC.convertibleb_correct n H (replace sigma (left x)) (replace sigma (right x))
    (replace sigma (carrier x)) (replace sigma (carrier x)) HH
    (typing_replace _ _ _ HU _ _ _ HS) (typing_replace _ _ _ HV _ _ _ HS))); exact HE.
Qed.

Theorem field_sorted m n (G : Ctx nat m) (H : Ctx nat n) sigma x :
  @wf nat RankSorts m G -> accepted G H sigma x = true ->
  @typ nat RankSorts m G (field x) (𝓤 (field_rank G x)).
Proof.
  intros HG HX; destruct (accepted_sound m n G H sigma x HG HX) as [c [HC [HCT [HU [HV Hrest]]]]].
  unfold field_rank; rewrite HC; unfold field; apply IE.eq_type_sort with (a := c); assumption.
Qed.
Theorem field_normal m n (G : Ctx nat m) (H : Ctx nat n) sigma x :
  @wf nat RankSorts m G -> accepted G H sigma x = true -> normalb (field x) = true.
Proof.
  intros HG HX; destruct (accepted_sound m n G H sigma x HG HX) as [c [_ [_ [_ [_ [HC [HU [HV _]]]]]]]].
  apply IE.eq_type_normal; assumption.
Qed.
Theorem value_typed m n (G : Ctx nat m) (H : Ctx nat n) sigma x :
  @wf nat RankSorts m G -> @wf nat RankSorts n H -> TypedSub G H sigma ->
  accepted G H sigma x = true -> @typ nat RankSorts n H (value H sigma x) (replace sigma (field x)).
Proof.
  intros HG HH HS HX; destruct (accepted_sound m n G H sigma x HG HX) as [c [_ [HC [HU [HV [_ [_ [_ HE]]]]]]]].
  unfold field; rewrite IE.eq_type_replace; apply RE.normal_reflexivity_typed with (c := c); try assumption.
  - change (typ H (replace sigma (carrier x)) (replace sigma (𝓤 c))); eapply typing_replace; eassumption.
  - eapply typing_replace; eassumption.
  - eapply typing_replace; eassumption.
Qed.
Theorem value_normal m n (G : Ctx nat m) (H : Ctx nat n) sigma x :
  @wf nat RankSorts m G -> @wf nat RankSorts n H -> TypedSub G H sigma ->
  accepted G H sigma x = true -> normalb (value H sigma x) = true.
Proof.
  intros HG HH HS HX; destruct (accepted_sound m n G H sigma x HG HX) as [c [_ [HC [HU Hrest]]]].
  apply RE.normal_reflexivity_normal with (c := c); [exact HH | |].
  - change (typ H (replace sigma (carrier x)) (replace sigma (𝓤 c))); eapply typing_replace; eassumption.
  - eapply typing_replace; eassumption.
Qed.
Theorem value_erases m n (H : Ctx nat n) (sigma : Fin m -> Term nat n) x P z :
  reduces_to nat n (IE.transport (value H sigma x) P z) z.
Proof. apply RE.normal_reflexivity_erases. Qed.

Definition entries s k {m n} (G : Ctx nat m) (H : Ctx nat n) sigma :=
  filter (accepted G H sigma) (descriptors s m k).
Theorem entries_iff s k m n (G : Ctx nat m) (H : Ctx nat n) sigma x :
  In x (entries s k G H sigma) <->
    node_budget x <= s /\ literal_budget x <= k /\ accepted G H sigma x = true.
Proof. unfold entries; rewrite filter_In, descriptors_iff; tauto. Qed.
Theorem computed_coverage m n (G : Ctx nat m) (H : Ctx nat n) sigma x :
  accepted G H sigma x = true ->
  In x (entries (node_budget x) (literal_budget x) G H sigma).
Proof. intro HX; apply entries_iff; repeat split; assumption || reflexivity. Qed.

Definition fallback {n} : descriptor n := Desc 0 (𝓤 0) (𝓤 0) (𝓤 0).
Definition count s k {m n} (G : Ctx nat m) (H : Ctx nat n) sigma := length (entries s k G H sigma).
Definition entry s k {m n} (G : Ctx nat m) (H : Ctx nat n) sigma i :=
  List.nth i (entries s k G H sigma) fallback.
Definition context s k {m n} (G : Ctx nat m) (H : Ctx nat n) sigma :
    Ctx nat (count s k G H sigma + m) :=
  PL.block (count s k G H sigma) 0 G (fun i => field (entry s k G H sigma i)).
Definition fill s k {m n} (G : Ctx nat m) (H : Ctx nat n) sigma :
    Fin (count s k G H sigma + m) -> Term nat n :=
  PL.fill_block (count s k G H sigma) 0 sigma (fun i => value H sigma (entry s k G H sigma i)).

Lemma entry_accepted s k m n (G : Ctx nat m) (H : Ctx nat n) sigma i :
  i < count s k G H sigma -> accepted G H sigma (entry s k G H sigma i) = true.
Proof.
  intro HI; assert (HE : In (entry s k G H sigma i) (entries s k G H sigma)).
  { unfold entry; apply nth_In; exact HI. }
  apply entries_iff in HE; tauto.
Qed.
Theorem context_wf s k m n (G : Ctx nat m) (H : Ctx nat n) sigma :
  @wf nat RankSorts m G -> @wf nat RankSorts _ (context s k G H sigma).
Proof.
  intro HG; apply PL.block_wf with (rank := fun i => field_rank G (entry s k G H sigma i)); [exact HG |].
  intros i HI; apply field_sorted with (H := H) (sigma := sigma); [exact HG | apply entry_accepted; lia].
Qed.
Theorem context_normal s k m n (G : Ctx nat m) (H : Ctx nat n) sigma :
  @wf nat RankSorts m G -> PT.normal_context G = true ->
  PT.normal_context (context s k G H sigma) = true.
Proof.
  intros HG HN; apply PL.block_normal; [exact HN |].
  intros i HI; apply field_normal with (G := G) (H := H) (sigma := sigma); [exact HG | apply entry_accepted; lia].
Qed.
Theorem fill_typed s k m n (G : Ctx nat m) (H : Ctx nat n) sigma :
  @wf nat RankSorts m G -> @wf nat RankSorts n H -> TypedSub G H sigma ->
  TypedSub (context s k G H sigma) H (fill s k G H sigma).
Proof.
  intros HG HH HS; apply PL.fill_block_typed; [exact HS |].
  intros i HI; apply value_typed with (G := G); try assumption; apply entry_accepted; lia.
Qed.
Theorem entry_value_normal s k m n (G : Ctx nat m) (H : Ctx nat n) sigma i :
  @wf nat RankSorts m G -> @wf nat RankSorts n H -> TypedSub G H sigma ->
  i < count s k G H sigma -> normalb (value H sigma (entry s k G H sigma i)) = true.
Proof. intros; apply value_normal with (G := G); try assumption; apply entry_accepted; assumption. Qed.
Theorem field_variable_typed s k m n (G : Ctx nat m) (H : Ctx nat n) sigma
    (i : Fin (count s k G H sigma)) :
  @typ nat RankSorts _ (context s k G H sigma) (var (CS.front i))
    (rename up (field (entry s k G H sigma (CS.fin_index i)))).
Proof. apply (PL.block_front_typing _ i 0 m G (fun j => field (entry s k G H sigma j))). Qed.
Theorem fill_source s k m n (G : Ctx nat m) (H : Ctx nat n) sigma i :
  fill s k G H sigma (@up (count s k G H sigma) m i) = sigma i.
Proof. apply PL.fill_block_source. Qed.
Theorem fill_field s k m n (G : Ctx nat m) (H : Ctx nat n) sigma
    (i : Fin (count s k G H sigma)) :
  fill s k G H sigma (CS.front i) = value H sigma (entry s k G H sigma (CS.fin_index i)).
Proof. apply (PL.fill_block_front _ i 0 m n sigma (fun j => value H sigma (entry s k G H sigma j))). Qed.
Theorem field_application_erases s k m n (G : Ctx nat m) (H : Ctx nat n) sigma
    (i : Fin (count s k G H sigma)) (P z : Term nat (count s k G H sigma+m)) :
  reduces_to nat n (replace (fill s k G H sigma) (IE.transport (var (CS.front i)) P z))
    (replace (fill s k G H sigma) z).
Proof.
  rewrite IE.transport_replace; cbn [replace]; rewrite fill_field; apply value_erases.
Qed.

Definition descriptor_eq_dec n (x y : descriptor n) : {x=y}+{x<>y}.
Proof. decide equality; apply FC.term_eq_dec || apply Nat.eq_dec. Defined.
Fixpoint locate {n} (x : descriptor n) (xs : list (descriptor n)) : option (Fin (length xs)) :=
  match xs with
  | [] => None
  | y::ys => if descriptor_eq_dec n x y then Some fzero else option_map fsucc (locate x ys)
  end.
Theorem locate_sound n (x : descriptor n) xs : forall i,
  locate x xs = Some i -> List.nth (CS.fin_index i) xs fallback = x.
Proof.
  induction xs as [|y ys IH]; intros i HI; cbn [locate] in HI; [discriminate |].
  destruct (descriptor_eq_dec n x y) as [E|NE].
  - inversion HI; subst; reflexivity.
  - destruct (locate x ys) as [j|] eqn:HJ; cbn [option_map] in HI; [| discriminate].
    inversion HI; subst; cbn [CS.fin_index nth]; apply IH; reflexivity.
Qed.
Theorem locate_complete n (x : descriptor n) xs : In x xs -> exists i, locate x xs = Some i.
Proof.
  induction xs as [|y ys IH]; intro HX; [contradiction |]; cbn [locate].
  destruct (descriptor_eq_dec n x y) as [E|NE]; [exists fzero; reflexivity |].
  destruct HX as [E|HX]; [symmetry in E; contradiction |].
  destruct (IH HX) as [i HI]; rewrite HI; exists (fsucc i); reflexivity.
Qed.
Definition lookup s k {m n} (G : Ctx nat m) (H : Ctx nat n) sigma x :=
  locate x (entries s k G H sigma).
Theorem lookup_complete m n (G : Ctx nat m) (H : Ctx nat n) sigma x :
  accepted G H sigma x = true ->
  exists i, lookup (node_budget x) (literal_budget x) G H sigma x = Some i.
Proof. intro HX; apply locate_complete, computed_coverage; exact HX. Qed.
Theorem lookup_typed s k m n (G : Ctx nat m) (H : Ctx nat n) sigma x i :
  lookup s k G H sigma x = Some i ->
  @typ nat RankSorts _ (context s k G H sigma) (var (CS.front i)) (rename up (field x)).
Proof.
  intro HI; pose proof (locate_sound m x (entries s k G H sigma) i HI) as HE.
  change (entry s k G H sigma (CS.fin_index i) = x) in HE.
  rewrite <- HE; apply field_variable_typed.
Qed.
Theorem original_descriptor_covered c m n (G : Ctx nat m) (H : Ctx nat n) sigma x :
  @wf nat RankSorts m G -> @wf nat RankSorts n H -> TypedSub G H sigma ->
  @typ nat RankSorts m G (carrier x) (𝓤 c) ->
  @typ nat RankSorts m G (left x) (carrier x) -> @typ nat RankSorts m G (right x) (carrier x) ->
  normalb (carrier x) = true -> normalb (left x) = true -> normalb (right x) = true ->
  def_equiv nat n (replace sigma (left x)) (replace sigma (right x)) ->
  exists i, lookup (node_budget x) (literal_budget x) G H sigma x = Some i.
Proof. intros; apply lookup_complete; eapply accepted_complete; eassumption. Qed.

(** This bound is computed from the checked finite layer, not guessed from
    literal ranks alone: variable declarations in G may carry larger ranks. *)
Definition rank_budget s k {m n} (G : Ctx nat m) (H : Ctx nat n) sigma :=
  fold_right Nat.max 0 (map (field_rank G) (entries s k G H sigma)).
Lemma member_max (xs : list nat) r : In r xs -> r <= fold_right Nat.max 0 xs.
Proof.
  induction xs as [|x xs IH]; intro HR; [contradiction |].
  destruct HR as [E|HR]; cbn; [subst; lia | specialize (IH HR); lia].
Qed.
Theorem entry_rank_bounded s k m n (G : Ctx nat m) (H : Ctx nat n) sigma i :
  i < count s k G H sigma ->
  field_rank G (entry s k G H sigma i) <= rank_budget s k G H sigma.
Proof.
  intro HI; unfold rank_budget; apply member_max, in_map.
  unfold entry; apply nth_In; exact HI.
Qed.

Print Assumptions entry_rank_bounded.
Print Assumptions context_wf.
Print Assumptions context_normal.
Print Assumptions fill_typed.
Print Assumptions entry_value_normal.
Print Assumptions field_variable_typed.
Print Assumptions fill_source.
Print Assumptions fill_field.
Print Assumptions field_application_erases.
Print Assumptions locate_sound.
Print Assumptions locate_complete.
Print Assumptions lookup_complete.
Print Assumptions lookup_typed.
Print Assumptions original_descriptor_covered.
Print Assumptions descriptors_iff.
Print Assumptions accepted_sound.
Print Assumptions accepted_complete.
Print Assumptions field_sorted.
Print Assumptions field_normal.
Print Assumptions value_typed.
Print Assumptions value_normal.
Print Assumptions value_erases.
Print Assumptions entries_iff.
Print Assumptions computed_coverage.
End CheckedEqualityFields.
