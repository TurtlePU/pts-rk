From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import Syntax Context Typing Preservation Ranks DefEq
  Reduction AbstractRewriting.
From PTSrk.NormalizationComplexity Require Import Rank Greedy Bounds RedexRanks
  AutomaticBound.
From PTSrk.SelfInterpreter Require Import ChurchSyntaxFaithful.
Import Context RankEstimate.

(** A deliberately LIMITED obstruction. A faithful normal quotation cannot
    itself serve as a conversion-respecting semantic type-index map. This
    does NOT exclude PHOAS with separate quotation and index interpretation,
    canonical/quotiented indices, explicit transports, or weaker fidelity. *)
Module PHOASConversion.

Definition identity : Term nat 0 := lam (𝓤 0) (var fzero).
Definition expanded_type : Term nat 0 := app identity (𝓤 0).
Definition contracted_type : Term nat 0 := 𝓤 0.

Lemma identity_typed :
  @typ nat RankSorts 0 ε identity (Π (𝓤 0) (𝓤 0)).
Proof.
  unfold identity. apply typ_λ with (ℓ := 0); [constructor; reflexivity |].
  change (typ (ε & 𝓤 0) (var fzero) ((ε & 𝓤 0) !! fzero)); constructor.
Qed.

Lemma expanded_type_typed : @typ nat RankSorts 0 ε expanded_type (𝓤 0).
Proof.
  change (typ ε expanded_type (subst (𝓤 0) (𝓤 0))).
  apply typ_app with (U := 𝓤 0); [apply identity_typed | constructor; reflexivity].
Qed.
Lemma contracted_type_typed : @typ nat RankSorts 0 ε contracted_type (𝓤 0).
Proof. constructor; reflexivity. Qed.
Lemma type_witness_step : step nat 0 expanded_type contracted_type.
Proof. unfold expanded_type, identity, contracted_type; apply step_beta. Qed.
Lemma type_witness_conversion : def_equiv nat 0 expanded_type contracted_type.
Proof.
  apply def_equiv_prop; exists contracted_type; split;
    [apply rtc_in, type_witness_step | reflexivity].
Qed.
Lemma type_witness_distinct : expanded_type <> contracted_type.
Proof. discriminate. Qed.

(** Both witnesses belong to the SAME independently defined finite budget:
    sort/type rank 0, literal ceiling 0, at most 5 syntax nodes, and the
    conservative sufficient redex budget 6. No quote property is in it. *)
Definition SmallType (t : Term nat 0) : Prop :=
  @typ nat RankSorts 0 ε t (𝓤 0) /\
  TypeRank ε t 0 /\ maxRankLiteral t = 0 /\ nodes t <= 5 /\
  RedexBound ε t 6.

Theorem small_type_witnesses : SmallType expanded_type /\ SmallType contracted_type.
Proof.
  assert (build : forall t, @typ nat RankSorts 0 ε t (𝓤 0) ->
    maxRankLiteral t = 0 -> nodes t <= 5 -> SmallType t).
  { intros t Ht HL HN. unfold SmallType; repeat split; try assumption.
    - exists (𝓤 0); split; [exact Ht | constructor; reflexivity].
    - eapply redex_bound_monotone; [apply conservative_rank_sound with (T := 𝓤 0); exact Ht |].
      unfold conservativeRank; lia. }
  split; apply build; try apply expanded_type_typed; try apply contracted_type_typed;
    cbn [expanded_type contracted_type identity maxRankLiteral nodes]; lia.
Qed.

Definition NormalFaithfulSharedMap {n} (D : Term nat 0 -> Prop)
    (Q : Term nat 0 -> Term nat n) : Prop :=
  (forall t, D t -> normalb (Q t) = true) /\
  (forall t u, D t -> D u -> Q t = Q u -> t = u) /\
  (forall t u, D t -> D u -> def_equiv nat 0 t u -> def_equiv nat n (Q t) (Q u)).

(** The target scope and fixed externally chosen index are arbitrary.
    Increasing rank/size/literal budgets does not repair these three
    simultaneous contracts once both convertible witnesses are admitted. *)
Theorem no_shared_map_on_types n D (Q : Term nat 0 -> Term nat n) :
  D expanded_type -> D contracted_type -> ~ NormalFaithfulSharedMap D Q.
Proof.
  intros HD HE [HN [HI HC]]. apply type_witness_distinct.
  apply HI; [exact HD | exact HE |].
  apply normal_conversion_identity.
  - apply HN; exact HD.
  - apply HN; exact HE.
  - apply HC; [exact HD | exact HE | apply type_witness_conversion].
Qed.

Corollary no_small_type_shared_map n (Q : Term nat 0 -> Term nat n) :
  ~ NormalFaithfulSharedMap SmallType Q.
Proof. apply no_shared_map_on_types; apply small_type_witnesses. Qed.

Corollary no_fixed_index_shared_map (I : Type) n
    (D : I -> Term nat 0 -> Prop) (Q : I -> Term nat 0 -> Term nat n) i :
  D i expanded_type -> D i contracted_type ->
  ~ NormalFaithfulSharedMap (D i) (Q i).
Proof. apply no_shared_map_on_types. Qed.

(** The same obstruction holds if two nominally separate maps are required
    to agree by original beta conversion. Ordinary PHOAS need NOT impose
    this agreement: a faithful syntax code and its semantic type index play
    different roles and may be unrelated as target terms. *)
Theorem no_faithful_code_agrees_with_index n (D : Term nat 0 -> Prop)
    (Q J : Term nat 0 -> Term nat n) :
  D expanded_type -> D contracted_type ->
  (forall t, D t -> normalb (Q t) = true) ->
  (forall t u, D t -> D u -> Q t = Q u -> t = u) ->
  (forall t u, D t -> D u -> def_equiv nat 0 t u -> def_equiv nat n (J t) (J u)) ->
  (forall t, D t -> def_equiv nat n (Q t) (J t)) -> False.
Proof.
  intros HD HE HN HI HC HA. apply (no_shared_map_on_types n D Q HD HE).
  split; [exact HN |]. split; [exact HI |]. intros t u Ht Hu Htu.
  transitivity (J t); [apply HA; exact Ht |].
  transitivity (J u); [apply HC; assumption | symmetry; apply HA; exact Hu].
Qed.

Print Assumptions expanded_type_typed.
Print Assumptions type_witness_conversion.
Print Assumptions small_type_witnesses.
Print Assumptions no_shared_map_on_types.
Print Assumptions no_small_type_shared_map.
Print Assumptions no_fixed_index_shared_map.
Print Assumptions no_faithful_code_agrees_with_index.

End PHOASConversion.
