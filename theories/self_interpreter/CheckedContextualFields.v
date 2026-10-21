From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting DefEq.
From PTSrk.NormalizationComplexity Require Import Rank Bounds Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import OriginalTypecheck FullConversion
  SizedSyntaxEnumeration CheckedEqualityFields IndexedEquality TarskiPalette
  ChurchSyntax PHOASTelescope ContextualTelescope UniformTelescope
  ContextualTelescopeRun ContextualEqualityRealizer ContextualEqualityExtension UniformTelescopeRecovery.
Import Context ListNotations RankEstimate.

(** Source-independent bounded syntax for equality-only fields, including
    arbitrary finite dependent telescope prefixes. All typing is checked
    against the ORIGINAL judgment; no candidate proof is assumed. *)
Module CheckedContextualFields.
Module OT := OriginalTypecheck.OriginalTypecheck.
Module FC := FullConversion.FullConversion.
Module EN := SizedSyntaxEnumeration.SizedSyntaxEnumeration.
Module EF := CheckedEqualityFields.CheckedEqualityFields.
Module IE := IndexedEquality.IndexedEquality.
Module PL := TarskiPalette.TarskiPalette.
Module CS := ChurchSyntax.ChurchSyntax.
Module PT := PHOASTelescope.PHOASTelescope.
Module CT := ContextualTelescope.ContextualTelescope.
Module UT := UniformTelescope.UniformTelescope.
Module TR := ContextualTelescopeRun.ContextualTelescopeRun.
Module CE := ContextualEqualityRealizer.ContextualEqualityRealizer.
Module CX := ContextualEqualityExtension.ContextualEqualityExtension.
Module UR := UniformTelescopeRecovery.UniformTelescopeRecovery.

Inductive candidate : nat -> Type :=
| leaf {n} : EF.descriptor n -> candidate n
| bind {n} : nat -> Term nat n -> candidate (S n) -> candidate n.
Derive NoConfusionHom for candidate.

Fixpoint profile {n} (x : candidate n) : list nat :=
  match x with leaf _ => [] | bind r _ y => r :: profile y end.
Fixpoint domains {n} (x : candidate n) : CT.telescope n (profile x) :=
  match x with leaf _ => CT.tnil | bind r A y => CT.tcons r A (domains y) end.
Fixpoint endpoint {n} (x : candidate n) : EF.descriptor (CT.scope (profile x) n) :=
  match x with leaf e => e | bind _ _ y => endpoint y end.
Fixpoint depth {n} (x : candidate n) :=
  match x with leaf _ => 0 | bind _ _ y => S (depth y) end.
Fixpoint node_budget {n} (x : candidate n) :=
  match x with leaf e => EF.node_budget e | bind _ A y => Nat.max (nodes A) (node_budget y) end.
Fixpoint literal_budget {n} (x : candidate n) :=
  match x with leaf e => EF.literal_budget e
  | bind r A y => Nat.max r (Nat.max (maxRankLiteral A) (literal_budget y)) end.

Fixpoint candidates h s n k : list (candidate n) :=
  map leaf (EF.descriptors s n k) ++
    match h with
    | 0 => []
    | S h' => flat_map (fun r => flat_map (fun A =>
        map (bind r A) (candidates h' s (S n) k)) (EN.sized_terms s n k)) (seq 0 (S k))
    end.

Theorem candidates_iff h : forall s n k (x : candidate n),
  In x (candidates h s n k) <->
  depth x <= h /\ node_budget x <= s /\ literal_budget x <= k.
Proof.
  induction h as [|h IH]; intros s n k x; cbn [candidates]; rewrite in_app_iff.
  - destruct x as [n e|n r A y]; cbn [depth node_budget literal_budget]; split.
    + intros [HX|HX]; [apply in_map_iff in HX; destruct HX as [e' [E HE]]; inversion E; subst;
        apply EF.descriptors_iff in HE; lia | contradiction].
    + intros [_ H]; left; apply in_map; apply EF.descriptors_iff; exact H.
    + intros [HX|HX]; [apply in_map_iff in HX; destruct HX as [e [E _]]; discriminate | contradiction].
    + lia.
  - destruct x as [n e|n r A y]; cbn [depth node_budget literal_budget]; split.
    + intros [HX|HX].
      * apply in_map_iff in HX; destruct HX as [e' [E HE]]; inversion E; subst;
          apply EF.descriptors_iff in HE; lia.
      * apply in_flat_map in HX; destruct HX as [r' [_ HX]].
        apply in_flat_map in HX; destruct HX as [A' [_ HX]].
        apply in_map_iff in HX; destruct HX as [y' [E _]]; discriminate.
    + intros [_ H]; left; apply in_map; apply EF.descriptors_iff; exact H.
    + intros [HX|HX].
      * apply in_map_iff in HX; destruct HX as [e [E _]]; discriminate.
      * apply in_flat_map in HX; destruct HX as [r' [HR HX]].
        apply in_flat_map in HX; destruct HX as [A' [HA HX]].
        apply in_map_iff in HX; destruct HX as [y' [E HY]]; dependent elimination E.
        apply in_seq in HR; apply EN.sized_terms_iff in HA; apply IH in HY; lia.
    + intro H; right; apply in_flat_map; exists r; split; [apply in_seq; lia |].
      apply in_flat_map; exists A; split; [apply EN.sized_terms_iff; lia |].
      apply in_map, IH; lia.
Qed.

Fixpoint accepted {m} (x : candidate m) : forall n,
    Ctx nat m -> Ctx nat n -> (Fin m -> Term nat n) -> bool :=
  match x in candidate k return forall n, Ctx nat k -> Ctx nat n -> (Fin k -> Term nat n) -> bool with
  | leaf e => fun n G H sigma => EF.accepted G H sigma e
  | bind r A y => fun n G H sigma =>
      OT.check G A (𝓤 r) && normalb A &&
      accepted y (S n) (G & A) (H & replace sigma A) (transpose sigma)
  end.

Theorem accepted_decompose m (x : candidate m) : forall n G H sigma,
  @wf nat RankSorts m G -> accepted x n G H sigma = true ->
  CT.formed G (domains x) /\ CT.normal_annotations (domains x) = true /\
  EF.accepted (CT.context (domains x) G)
    (CT.context (CT.replace_telescope (domains x) n sigma) H)
    (CT.lift_sub (profile x) sigma) (endpoint x) = true.
Proof.
  induction x as [m e|m r A y IH]; intros n G H sigma HG HX.
  - cbn [domains CT.formed CT.normal_annotations CT.context CT.replace_telescope CT.lift_sub profile endpoint] in *;
      repeat split; exact HX.
  - cbn [accepted] in HX; repeat rewrite andb_true_iff in HX; destruct HX as [[HA HN] HY].
    assert (HAt : @typ nat RankSorts m G A (𝓤 r)) by (apply OT.check_sound; assumption).
    destruct (IH (S n) (G & A) (H & replace sigma A) (transpose sigma)
      (wf_cons r HG HAt) HY) as [HD [HN' HE]].
    cbn [domains CT.formed CT.normal_annotations CT.context CT.replace_telescope CT.lift_sub profile endpoint].
    repeat split; try assumption; now rewrite HN, HN'.
Qed.

Theorem accepted_recompose m (x : candidate m) : forall n G H sigma,
  @wf nat RankSorts m G -> CT.formed G (domains x) ->
  CT.normal_annotations (domains x) = true ->
  EF.accepted (CT.context (domains x) G)
    (CT.context (CT.replace_telescope (domains x) n sigma) H)
    (CT.lift_sub (profile x) sigma) (endpoint x) = true -> accepted x n G H sigma = true.
Proof.
  induction x as [m e|m r A y IH]; intros n G H sigma HG HD HN HE.
  - exact HE.
  - cbn [domains CT.formed] in HD; destruct HD as [HA HD].
    cbn [domains CT.normal_annotations] in HN; apply andb_true_iff in HN; destruct HN as [HN HNY].
    cbn [accepted]; rewrite (OT.check_complete m G A (𝓤 r) HG HA), HN; cbn.
    apply IH; try assumption; eapply wf_cons; eassumption.
Qed.

Definition field {n} (x : candidate n) :=
  CX.declaration (EF.level (endpoint x)) (domains x)
    (EF.carrier (endpoint x)) (EF.left (endpoint x)) (EF.right (endpoint x)).
Definition value {n} (sigma : Fin n -> Term nat 0) (x : candidate n) :=
  CX.value (EF.level (endpoint x)) (domains x) sigma
    (EF.carrier (endpoint x)) (EF.left (endpoint x)).
Definition field_rank {n} (G : Ctx nat n) (x : candidate n) :=
  CT.rank (profile x) (EF.field_rank (CT.context (domains x) G) (endpoint x)).

Theorem field_sorted n (G : Ctx nat n) sigma x :
  @wf nat RankSorts n G -> accepted x 0 G ε sigma = true ->
  @typ nat RankSorts n G (field x) (𝓤 (field_rank G x)).
Proof.
  intros HG HX; destruct (accepted_decompose n x 0 G ε sigma HG HX) as [HD [HN HE]].
  unfold field, CX.declaration, CE.witness_type, field_rank.
  apply CT.close_type_sort; [exact HD |].
  apply EF.field_sorted with (H := CT.context (CT.replace_telescope (domains x) 0 sigma) ε)
    (sigma := CT.lift_sub (profile x) sigma); [apply CT.formed_wf; assumption | exact HE].
Qed.
Theorem field_normal n (G : Ctx nat n) sigma x :
  @wf nat RankSorts n G -> accepted x 0 G ε sigma = true -> normalb (field x) = true.
Proof.
  intros HG HX; destruct (accepted_decompose n x 0 G ε sigma HG HX) as [HD [HN HE]].
  unfold field, CX.declaration, CE.witness_type; rewrite CT.close_type_normal, HN; cbn.
  apply EF.field_normal with (G := CT.context (domains x) G)
    (H := CT.context (CT.replace_telescope (domains x) 0 sigma) ε)
    (sigma := CT.lift_sub (profile x) sigma); [apply CT.formed_wf; assumption | exact HE].
Qed.
Theorem value_typed n (G : Ctx nat n) sigma x :
  @wf nat RankSorts n G -> TypedSub G ε sigma -> accepted x 0 G ε sigma = true ->
  @typ nat RankSorts 0 ε (value sigma x) (replace sigma (field x)).
Proof.
  intros HG HS HX; destruct (accepted_decompose n x 0 G ε sigma HG HX) as [HD [HN HE]].
  destruct (EF.accepted_sound _ _ _ _ _ _ (CT.formed_wf _ _ _ _ HG HD) HE)
    as [c [_ [HC [HU [HV [_ [_ [_ Heq]]]]]]]].
  apply CX.value_typed with (c := c) (G := G); assumption.
Qed.
Theorem value_normal n (G : Ctx nat n) sigma x :
  @wf nat RankSorts n G -> TypedSub G ε sigma -> accepted x 0 G ε sigma = true ->
  normalb (value sigma x) = true.
Proof.
  intros HG HS HX; destruct (accepted_decompose n x 0 G ε sigma HG HX) as [HD [HN HE]].
  destruct (EF.accepted_sound _ _ _ _ _ _ (CT.formed_wf _ _ _ _ HG HD) HE)
    as [c [_ [HC [HU Hrest]]]].
  apply CX.value_normal with (c := c) (G := G); assumption.
Qed.

Theorem accepted_complete c n (G : Ctx nat n) sigma x :
  @wf nat RankSorts n G -> TypedSub G ε sigma -> CT.formed G (domains x) ->
  CT.normal_annotations (domains x) = true ->
  @typ nat RankSorts _ (CT.context (domains x) G) (EF.carrier (endpoint x)) (𝓤 c) ->
  @typ nat RankSorts _ (CT.context (domains x) G) (EF.left (endpoint x)) (EF.carrier (endpoint x)) ->
  @typ nat RankSorts _ (CT.context (domains x) G) (EF.right (endpoint x)) (EF.carrier (endpoint x)) ->
  normalb (EF.carrier (endpoint x)) = true -> normalb (EF.left (endpoint x)) = true ->
  normalb (EF.right (endpoint x)) = true ->
  def_equiv nat _ (CX.filled sigma (EF.left (endpoint x))) (CX.filled sigma (EF.right (endpoint x))) ->
  accepted x 0 G ε sigma = true.
Proof.
  intros HG HS HD HN HC HU HV HNC HNU HNV HE; apply accepted_recompose; try assumption.
  apply EF.accepted_complete with (c := c); try assumption.
  - apply CT.formed_wf; assumption.
  - apply CT.formed_wf; [constructor | eapply CT.formed_replace; eassumption].
  - apply CT.context_sub; exact HS.
Qed.

Fixpoint pack {n rs} (D : CT.telescope n rs) : EF.descriptor (CT.scope rs n) -> candidate n :=
  match D with CT.tnil => leaf | CT.tcons r A E => fun e => bind r A (pack E e) end.
Theorem field_pack n rs (D : CT.telescope n rs) e :
  field (pack D e) = CX.declaration (EF.level e) D (EF.carrier e) (EF.left e) (EF.right e).
Proof.
  revert e; induction D; intro e; [reflexivity |].
  change (Π A (field (pack D e)) = Π A (CX.declaration (EF.level e) D (EF.carrier e) (EF.left e) (EF.right e))).
  now rewrite IHD.
Qed.
Theorem pack_accepted n rs (D : CT.telescope n rs) : forall m G H sigma e,
  @wf nat RankSorts n G -> CT.formed G D -> CT.normal_annotations D = true ->
  EF.accepted (CT.context D G) (CT.context (CT.replace_telescope D m sigma) H)
    (CT.lift_sub rs sigma) e = true -> accepted (pack D e) m G H sigma = true.
Proof.
  induction D; intros m G H sigma e HG HD HN HE; [exact HE |].
  cbn [CT.formed] in HD; destruct HD as [HA HD].
  cbn [CT.normal_annotations] in HN; apply andb_true_iff in HN; destruct HN as [HN HND].
  cbn [pack accepted]; rewrite (OT.check_complete n G A (𝓤 r) HG HA), HN; cbn.
  apply IHD; try assumption; eapply wf_cons; eassumption.
Qed.

Fixpoint accepted_candidates h s k m n (G : Ctx nat m) (H : Ctx nat n)
    (sigma : Fin m -> Term nat n) : list (candidate m) :=
  map leaf (EF.entries s k G H sigma) ++
  match h with
  | 0 => []
  | S h' => flat_map (fun r => flat_map (fun A =>
      if OT.check G A (𝓤 r) && normalb A then
        map (bind r A) (accepted_candidates h' s k (S m) (S n)
          (G & A) (H & replace sigma A) (transpose sigma))
      else []) (EN.sized_terms s m k)) (seq 0 (S k))
  end.

Theorem accepted_candidates_iff h : forall s k m n (G : Ctx nat m) H sigma x,
  In x (accepted_candidates h s k m n G H sigma) <->
  depth x<=h /\ node_budget x<=s /\ literal_budget x<=k /\
    accepted x n G H sigma=true.
Proof.
  induction h as [|h IH]; intros s k m n G H sigma x;
    cbn [accepted_candidates]; rewrite in_app_iff.
  - destruct x as [m e|m r A y]; cbn [depth node_budget literal_budget accepted]; split.
    + intros [HX|HX]; [apply in_map_iff in HX; destruct HX as [e' [E HE]];
        dependent elimination E; apply EF.entries_iff in HE; split; [lia|exact HE]|contradiction].
    + intros [_ HX]; left; apply in_map, EF.entries_iff; exact HX.
    + intros [HX|HX]; [apply in_map_iff in HX; destruct HX as [e' [E _]]; discriminate|contradiction].
    + lia.
  - destruct x as [m e|m r A y]; cbn [depth node_budget literal_budget accepted]; split.
    + intros [HX|HX].
      * apply in_map_iff in HX; destruct HX as [e' [E HE]];
          dependent elimination E; apply EF.entries_iff in HE; split; [lia|exact HE].
      * apply in_flat_map in HX; destruct HX as [r [HR HX]].
        apply in_flat_map in HX; destruct HX as [A [HA HX]].
        destruct (OT.check G A (𝓤 r) && normalb A); [|contradiction].
        apply in_map_iff in HX; destruct HX as [y [E _]]; discriminate.
    + intros [_ HX]; left; apply in_map, EF.entries_iff; exact HX.
    + intros [HX|HX].
      * apply in_map_iff in HX; destruct HX as [e' [E _]]; discriminate.
      * apply in_flat_map in HX; destruct HX as [r' [HR HX]].
        apply in_flat_map in HX; destruct HX as [A' [HA HX]].
        destruct (OT.check G A' (𝓤 r') && normalb A') eqn:HG; [|contradiction].
        apply in_map_iff in HX; destruct HX as [y' [E HY]].
        dependent elimination E.
        apply in_seq in HR; apply EN.sized_terms_iff in HA; apply IH in HY.
        rewrite HG; cbn; destruct HY as [HYD [HYN [HYL HYA]]].
        repeat split; try assumption; lia.
    + intros [HD [HN [HL HA]]].
      apply andb_true_iff in HA; destruct HA as [HG HY].
      right; apply in_flat_map; exists r; split; [apply in_seq; lia|].
      apply in_flat_map; exists A; split; [apply EN.sized_terms_iff; lia|].
      rewrite HG; apply in_map, IH; repeat split; try assumption; lia.
Qed.

Definition entries h s k {n} (G : Ctx nat n) sigma :=
  accepted_candidates h s k n 0 G ε sigma.
Theorem entries_iff h s k n (G : Ctx nat n) sigma x :
  In x (entries h s k G sigma) <-> depth x <= h /\ node_budget x <= s /\
    literal_budget x <= k /\ accepted x 0 G ε sigma = true.
Proof. apply accepted_candidates_iff. Qed.

Theorem entries_reference_agrees h s k n (G : Ctx nat n) sigma x :
  In x (entries h s k G sigma) <->
  In x (filter (fun y => accepted y 0 G ε sigma) (candidates h s n k)).
Proof. rewrite entries_iff, filter_In, candidates_iff; tauto. Qed.
Theorem computed_coverage n (G : Ctx nat n) sigma x :
  accepted x 0 G ε sigma = true ->
  In x (entries (depth x) (node_budget x) (literal_budget x) G sigma).
Proof. intro HX; apply entries_iff; repeat split; assumption || reflexivity. Qed.

Definition fallback {n} : candidate n := leaf EF.fallback.
Definition count h s k {n} (G : Ctx nat n) sigma := length (entries h s k G sigma).
Definition entry h s k {n} (G : Ctx nat n) sigma i := nth i (entries h s k G sigma) fallback.
Definition context h s k {n} (G : Ctx nat n) sigma : Ctx nat (count h s k G sigma+n) :=
  PL.block (count h s k G sigma) 0 G (fun i => field (entry h s k G sigma i)).
Definition fill h s k {n} (G : Ctx nat n) sigma : Fin (count h s k G sigma+n) -> Term nat 0 :=
  PL.fill_block (count h s k G sigma) 0 sigma (fun i => value sigma (entry h s k G sigma i)).

Lemma entry_accepted h s k n (G : Ctx nat n) sigma i :
  i < count h s k G sigma -> accepted (entry h s k G sigma i) 0 G ε sigma = true.
Proof.
  intro HI; assert (HE : In (entry h s k G sigma i) (entries h s k G sigma)).
  { unfold entry; apply nth_In; exact HI. }
  apply entries_iff in HE; tauto.
Qed.
Theorem context_wf h s k n (G : Ctx nat n) sigma :
  @wf nat RankSorts n G -> @wf nat RankSorts _ (context h s k G sigma).
Proof.
  intro HG; apply PL.block_wf with (rank := fun i => field_rank G (entry h s k G sigma i)); [exact HG |].
  intros i HI; apply field_sorted with (sigma := sigma); [exact HG | apply entry_accepted; lia].
Qed.
Theorem context_normal h s k n (G : Ctx nat n) sigma :
  @wf nat RankSorts n G -> PT.normal_context G = true -> PT.normal_context (context h s k G sigma) = true.
Proof.
  intros HG HN; apply PL.block_normal; [exact HN |].
  intros i HI; apply field_normal with (G := G) (sigma := sigma); [exact HG | apply entry_accepted; lia].
Qed.
Theorem fill_typed h s k n (G : Ctx nat n) sigma :
  @wf nat RankSorts n G -> TypedSub G ε sigma -> TypedSub (context h s k G sigma) ε (fill h s k G sigma).
Proof.
  intros HG HS; apply PL.fill_block_typed; [exact HS |].
  intros i HI; apply value_typed with (G := G); try assumption; apply entry_accepted; lia.
Qed.
Theorem entry_value_normal h s k n (G : Ctx nat n) sigma i :
  @wf nat RankSorts n G -> TypedSub G ε sigma -> i < count h s k G sigma ->
  normalb (value sigma (entry h s k G sigma i)) = true.
Proof. intros; apply value_normal with (G := G); try assumption; apply entry_accepted; assumption. Qed.
Theorem field_variable_typed h s k n (G : Ctx nat n) sigma (i : Fin (count h s k G sigma)) :
  @typ nat RankSorts _ (context h s k G sigma) (var (CS.front i))
    (rename up (field (entry h s k G sigma (CS.fin_index i)))).
Proof. apply (PL.block_front_typing _ i 0 n G (fun j => field (entry h s k G sigma j))). Qed.
Theorem fill_source h s k n (G : Ctx nat n) sigma i :
  fill h s k G sigma (@up (count h s k G sigma) n i) = sigma i.
Proof. apply PL.fill_block_source. Qed.
Theorem fill_field h s k n (G : Ctx nat n) sigma (i : Fin (count h s k G sigma)) :
  fill h s k G sigma (CS.front i) = value sigma (entry h s k G sigma (CS.fin_index i)).
Proof. apply (PL.fill_block_front _ i 0 n 0 sigma (fun j => value sigma (entry h s k G sigma j))). Qed.

(** Full application of every actual closed field returns its literal
    payload. Telescope arguments and payload need not themselves be normal. *)
Theorem value_erases n (sigma : Fin n -> Term nat 0) (x : candidate n) m
    (tau : Fin (CT.scope (profile x) 0) -> Term nat m) P z :
  reduces_to nat m (IE.transport
    (TR.run (CX.filled_domains (domains x) sigma) tau
      (replace (TR.base tau) (value sigma x))) P z) z.
Proof. apply CE.normal_witness_erases. Qed.

Definition candidate_eq_dec n (x y : candidate n) : {x=y}+{x<>y}.
Proof.
  revert y; induction x as [n e|n r A x IH]; intro y; dependent elimination y;
    try (right; discriminate).
  - destruct (EF.descriptor_eq_dec _ e d) as [E|NE]; [left; now subst |].
    right; intro E; dependent elimination E; contradiction.
  - destruct (Nat.eq_dec r n2) as [ER|NR]; [subst n2 | right; intro E; dependent elimination E; contradiction].
    destruct (FC.term_eq_dec A t) as [EA|NA]; [subst t | right; intro E; dependent elimination E; contradiction].
    destruct (IH c) as [EX|NX]; [subst c; left; reflexivity | right; intro E; dependent elimination E; contradiction].
Defined.
Fixpoint locate {n} (x : candidate n) (xs : list (candidate n)) : option (Fin (length xs)) :=
  match xs with
  | [] => None
  | y::ys => if candidate_eq_dec n x y then Some fzero else option_map fsucc (locate x ys)
  end.
Theorem locate_sound n (x : candidate n) xs : forall i,
  locate x xs = Some i -> nth (CS.fin_index i) xs fallback = x.
Proof.
  induction xs as [|y ys IH]; intros i HI; cbn [locate] in HI; [discriminate |].
  destruct (candidate_eq_dec n x y) as [E|NE].
  - inversion HI; subst; reflexivity.
  - destruct (locate x ys) as [j|] eqn:HJ; cbn [option_map] in HI; [| discriminate].
    inversion HI; subst; cbn [CS.fin_index nth]; apply IH; reflexivity.
Qed.
Theorem locate_complete n (x : candidate n) xs : In x xs -> exists i, locate x xs = Some i.
Proof.
  induction xs as [|y ys IH]; intro HX; [contradiction |]; cbn [locate].
  destruct (candidate_eq_dec n x y) as [E|NE]; [exists fzero; reflexivity |].
  destruct HX as [E|HX]; [symmetry in E; contradiction |].
  destruct (IH HX) as [i HI]; rewrite HI; exists (fsucc i); reflexivity.
Qed.
Definition lookup h s k {n} (G : Ctx nat n) sigma x := locate x (entries h s k G sigma).
Theorem lookup_complete n (G : Ctx nat n) sigma x :
  accepted x 0 G ε sigma = true ->
  exists i, lookup (depth x) (node_budget x) (literal_budget x) G sigma x = Some i.
Proof. intro HX; apply locate_complete, computed_coverage; exact HX. Qed.
Theorem lookup_typed h s k n (G : Ctx nat n) sigma x i :
  lookup h s k G sigma x = Some i ->
  @typ nat RankSorts _ (context h s k G sigma) (var (CS.front i)) (rename up (field x)).
Proof.
  intro HI; pose proof (locate_sound n x (entries h s k G sigma) i HI) as HE.
  change (entry h s k G sigma (CS.fin_index i) = x) in HE.
  rewrite <- HE; apply field_variable_typed.
Qed.
Theorem lookup_filled h s k n (G : Ctx nat n) sigma x i :
  lookup h s k G sigma x = Some i -> fill h s k G sigma (CS.front i) = value sigma x.
Proof.
  intro HI; rewrite fill_field.
  pose proof (locate_sound n x (entries h s k G sigma) i HI) as HE.
  change (entry h s k G sigma (CS.fin_index i) = x) in HE.
  exact (f_equal (fun y => value sigma y) HE).
Qed.

Definition rank_budget h s k {n} (G : Ctx nat n) sigma :=
  fold_right Nat.max 0 (map (field_rank G) (entries h s k G sigma)).
Theorem entry_rank_bounded h s k n (G : Ctx nat n) sigma i :
  i < count h s k G sigma -> field_rank G (entry h s k G sigma i) <= rank_budget h s k G sigma.
Proof. intro HI; unfold rank_budget; apply EF.member_max, in_map; unfold entry; apply nth_In; exact HI. Qed.

Theorem original_telescope_covered c n rs (G : Ctx nat n) (D : CT.telescope n rs) sigma e :
  @wf nat RankSorts n G -> TypedSub G ε sigma -> CT.formed G D -> CT.normal_annotations D = true ->
  @typ nat RankSorts _ (CT.context D G) (EF.carrier e) (𝓤 c) ->
  @typ nat RankSorts _ (CT.context D G) (EF.left e) (EF.carrier e) ->
  @typ nat RankSorts _ (CT.context D G) (EF.right e) (EF.carrier e) ->
  normalb (EF.carrier e) = true -> normalb (EF.left e) = true -> normalb (EF.right e) = true ->
  def_equiv nat _ (CX.filled sigma (EF.left e)) (CX.filled sigma (EF.right e)) ->
  exists i, lookup (depth (pack D e)) (node_budget (pack D e)) (literal_budget (pack D e))
    G sigma (pack D e) = Some i.
Proof.
  intros HG HS HD HND HC HU HV HNC HNU HNV HE.
  apply lookup_complete, pack_accepted; try assumption.
  apply EF.accepted_complete with (c := c); try assumption.
  - apply CT.formed_wf; assumption.
  - apply CT.formed_wf; [constructor | eapply CT.formed_replace; eassumption].
  - apply CT.context_sub; exact HS.
Qed.

Definition local_domains h s k {n} (G : Ctx nat n) sigma (x : candidate n) :=
  CT.rename_telescope (domains x) (count h s k G sigma+n) up.
Definition local_apply h s k {n} (G : Ctx nat n) sigma (x : candidate n)
    (i : Fin (count h s k G sigma)) :=
  UT.apply_under (local_domains h s k G sigma x) (var (CS.front i)).
Definition lifted h s k {n} (G : Ctx nat n) sigma (x : candidate n)
    (t : Term nat (CT.scope (profile x) n)) :=
  rename (CT.lift_ren (profile x) (@up (count h s k G sigma) n)) t.
Theorem local_apply_typed h s k n (G : Ctx nat n) sigma x i :
  lookup h s k G sigma x = Some i ->
  @typ nat RankSorts _ (CT.context (local_domains h s k G sigma x) (context h s k G sigma))
    (local_apply h s k G sigma x i)
    (IE.eq_type (EF.level (endpoint x)) (lifted h s k G sigma x (EF.carrier (endpoint x)))
      (lifted h s k G sigma x (EF.left (endpoint x))) (lifted h s k G sigma x (EF.right (endpoint x)))).
Proof.
  intro HI; unfold local_apply; apply UT.apply_under_typed.
  unfold local_domains, lifted; rewrite <- IE.eq_type_rename, <- CT.close_type_rename.
  apply lookup_typed; exact HI.
Qed.
Theorem local_apply_normal h s k n (G : Ctx nat n) sigma x i :
  normalb (local_apply h s k G sigma x i) = true.
Proof. apply UT.apply_under_normal; reflexivity. Qed.
Lemma filled_local_domains h s k n (G : Ctx nat n) sigma x :
  CT.replace_telescope (local_domains h s k G sigma x) 0 (fill h s k G sigma) =
  CX.filled_domains (domains x) sigma.
Proof.
  unfold local_domains, CX.filled_domains.
  transitivity (CT.rename_telescope (CT.replace_telescope (domains x) 0 sigma) 0 (fun i => i)).
  - apply UR.telescope_substitution_square; intro i; rewrite fill_source, rename_id; reflexivity.
  - apply UR.telescope_rename_id.
Qed.
Theorem local_transport_erases h s k n (G : Ctx nat n) sigma x i P z :
  lookup h s k G sigma x = Some i ->
  reduces_to nat _ (replace (CT.lift_sub (profile x) (fill h s k G sigma))
    (IE.transport (local_apply h s k G sigma x i) P z))
    (replace (CT.lift_sub (profile x) (fill h s k G sigma)) z).
Proof.
  intro HI; rewrite IE.transport_replace; unfold local_apply; rewrite UT.apply_under_replace, filled_local_domains.
  cbn [replace].
  pose proof (value_erases n sigma x (CT.scope (profile x) 0) (fun i => var i)
    (replace (CT.lift_sub (profile x) (fill h s k G sigma)) P)
    (replace (CT.lift_sub (profile x) (fill h s k G sigma)) z)) as H.
  rewrite TR.run_apply_under, replace_var in H.
  refine (eq_ind_r (fun q : Term nat 0 => reduces_to nat _
    (IE.transport (UT.apply_under (CX.filled_domains (domains x) sigma) q)
      (replace (CT.lift_sub (profile x) (fill h s k G sigma)) P)
      (replace (CT.lift_sub (profile x) (fill h s k G sigma)) z))
    (replace (CT.lift_sub (profile x) (fill h s k G sigma)) z)) H
    (lookup_filled h s k n G sigma x i HI)).
Qed.

Print Assumptions original_telescope_covered.
Print Assumptions local_apply_typed.
Print Assumptions local_apply_normal.
Print Assumptions filled_local_domains.
Print Assumptions local_transport_erases.
Print Assumptions accepted_complete.
Print Assumptions field_pack.
Print Assumptions pack_accepted.
Print Assumptions entries_iff.
Print Assumptions computed_coverage.
Print Assumptions context_wf.
Print Assumptions context_normal.
Print Assumptions fill_typed.
Print Assumptions entry_value_normal.
Print Assumptions field_variable_typed.
Print Assumptions fill_source.
Print Assumptions fill_field.
Print Assumptions value_erases.
Print Assumptions locate_sound.
Print Assumptions locate_complete.
Print Assumptions lookup_complete.
Print Assumptions lookup_typed.
Print Assumptions lookup_filled.
Print Assumptions entry_rank_bounded.
Print Assumptions candidates_iff.
Print Assumptions accepted_decompose.
Print Assumptions accepted_recompose.
Print Assumptions field_sorted.
Print Assumptions field_normal.
Print Assumptions value_typed.
Print Assumptions value_normal.
End CheckedContextualFields.
