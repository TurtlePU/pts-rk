From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Inversions
  Preservation Ranks DefEq.
From PTSrk.NormalizationComplexity Require Import RedexRanks.
Import Context.

(** This obstruction concerns one fixed ORIGINAL PTS term used as the head
    of an application spine.  Arguments may contain arbitrary externally
    constructed type and program representations.  No effective quotation,
    common representation type, or size bound is required.  Externally adding
    abstractions around the whole result is outside this precise interface. *)
Inductive ApplicationSpine {n} (head : Term nat n) : Term nat n -> Prop :=
| spine_head : ApplicationSpine head head
| spine_argument f u :
    ApplicationSpine head f -> ApplicationSpine head (app f u).

(** The rank is the sort of a term's TYPE, as in the existing normalization
    development.  Conversion and alternative typing derivations cannot
    change this rank in a well-formed original context. *)
Theorem application_spine_rank {n} (G : Ctx nat n) head result r s :
  @wf nat RankSorts n G ->
  ApplicationSpine head result ->
  TypeRank G head r -> TypeRank G result s -> s <= r.
Proof.
  intros HG Hspine. revert s.
  induction Hspine; intros s Hhead Hresult.
  - assert (r = s) by (eapply type_rank_unique; eassumption). lia.
  - destruct Hresult as [T [Happ HT]].
    destruct (app_inversion RankSorts f u T Happ)
      as [A [B [Hf [Hu Heq]]]].
    destruct (typing_type_rank G f (Π A B) HG Hf) as [q Hq].
    assert (s <= q).
    { apply (application_rank_le_function G f u s q HG).
      - exists T; split; assumption.
      - exact Hq. }
    specialize (IHHspine q Hhead Hq). lia.
Qed.

Theorem application_spine_conversion_rank {n} (G : Ctx nat n)
  head result target r s :
  @wf nat RankSorts n G ->
  ApplicationSpine head result ->
  TypeRank G head r ->
  (exists T, @typ nat RankSorts n G result T) ->
  TypeRank G target s -> def_equiv nat n result target -> s <= r.
Proof.
  intros HG Hspine Hhead [T HT] Htarget Heq.
  destruct (typing_type_rank G result T HG HT) as [q Hq].
  assert (q = s) by (eapply type_rank_conversion; eassumption).
  subst q. eapply application_spine_rank; eassumption.
Qed.

(** Explicit closed inhabitants at EVERY type rank.  Their scopes are
    generalized only to make the constructor proofs independent of shifting.

      A_0 = U_0,       A_(r+1) = Pi _:A_r. U_0
      v_0 = U_0,       v_(r+1) = lambda _:A_r. U_0.

    In particular A_r : U_r and v_r : A_r use precisely RankSorts. *)
Fixpoint rank_type (r : nat) {n} : Term nat n :=
  match r with
  | 0 => 𝓤 0
  | S k => Π (rank_type k) (𝓤 0)
  end.

Definition rank_value (r : nat) {n} : Term nat n :=
  match r with
  | 0 => 𝓤 0
  | S k => lam (rank_type k) (𝓤 0)
  end.

Theorem rank_type_sort r : forall n (G : Ctx nat n),
  @typ nat RankSorts n G (rank_type r) (𝓤 r).
Proof.
  induction r; intros n G; cbn [rank_type].
  - constructor; reflexivity.
  - eapply typ_Π with (ℓₜ := r) (ℓᵤ := 0).
    + apply IHr.
    + constructor; reflexivity.
    + change (S r = Nat.max (S r) 0). rewrite Nat.max_0_r. reflexivity.
Qed.

Theorem rank_value_typing r n (G : Ctx nat n) :
  @typ nat RankSorts n G (rank_value r) (rank_type r).
Proof.
  destruct r; cbn [rank_value rank_type].
  - constructor; reflexivity.
  - eapply typ_λ with (ℓ := r).
    + apply rank_type_sort.
    + constructor; reflexivity.
Qed.

Theorem rank_value_type_rank r n (G : Ctx nat n) :
  TypeRank G (rank_value r) r.
Proof.
  exists (rank_type r). split; [apply rank_value_typing | apply rank_type_sort].
Qed.

(** A deliberately permissive specification: each original closed typed
    target may choose ANY typed application spine headed by the evaluator.
    Thus failure of this specification also excludes every more restrictive
    fixed-head interface using a quotation function and explicit type/code
    arguments.  This does not rule out a metalevel family of evaluators. *)
Definition UniversalFixedHeadEvaluator (head : Term nat 0) : Prop :=
  (exists T, @typ nat RankSorts 0 ε head T) /\
  forall target T, @typ nat RankSorts 0 ε target T ->
    exists result U,
      ApplicationSpine head result /\
      @typ nat RankSorts 0 ε result U /\
      def_equiv nat 0 result target.

Theorem no_universal_fixed_head_evaluator head :
  ~ UniversalFixedHeadEvaluator head.
Proof.
  intros [[T HT] Hall].
  assert (HG : @wf nat RankSorts 0 ε) by constructor.
  destruct (typing_type_rank ε head T HG HT) as [r Hr].
  destruct (Hall (rank_value (S r)) (rank_type (S r))
    (rank_value_typing (S r) 0 ε))
    as [result [U [Hspine [Hresult Heq]]]].
  assert (S r <= r).
  { eapply application_spine_conversion_rank;
      [exact HG | exact Hspine | exact Hr | | | exact Heq].
    - exists U; exact Hresult.
    - apply rank_value_type_rank. }
  lia.
Qed.

Print Assumptions application_spine_rank.
Print Assumptions application_spine_conversion_rank.
Print Assumptions rank_type_sort.
Print Assumptions rank_value_typing.
Print Assumptions rank_value_type_rank.
Print Assumptions no_universal_fixed_head_evaluator.
