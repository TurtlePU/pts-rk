From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Inversions
  Preservation Ranks DefEq.
From PTSrk.NormalizationComplexity Require Import RedexRanks.
Import Context ListNotations.

(** A finite basis denotes fixed CLOSED ORIGINAL terms.  A basis atom carries
    only its membership witness.  Every universe atom remains available,
    without a bound on its index.  Application is the sole term constructor.
    There is no implicit abstraction, annotation erasure or eta conversion. *)
Inductive Expression (basis : list (Term nat 0)) : Type :=
| basis_atom (t : Term nat 0) : In t basis -> Expression basis
| universe_atom (i : nat) : Expression basis
| application (f u : Expression basis) : Expression basis.

Arguments basis_atom {basis} t _.
Arguments universe_atom {basis} i.
Arguments application {basis} f u.

Fixpoint decode {basis} (e : Expression basis) : Term nat 0 :=
  match e with
  | basis_atom t _ => t
  | universe_atom i => 𝓤 i
  | application f u => app (decode f) (decode u)
  end.

Definition TypedBasis (basis : list (Term nat 0)) : Prop :=
  forall t, In t basis -> exists T, @typ nat RankSorts 0 ε t T.

Definition BasisRankBound (basis : list (Term nat 0)) (bound : nat) : Prop :=
  forall t, In t basis -> exists r, TypeRank ε t r /\ r <= bound.

Theorem finite_basis_rank_bound basis :
  TypedBasis basis -> exists bound, BasisRankBound basis bound.
Proof.
  induction basis as [|b basis IH]; intro Htyped.
  - exists 0. intros t Hin. contradiction.
  - destruct (Htyped b (or_introl eq_refl)) as [T Hb].
    assert (HG : @wf nat RankSorts 0 ε) by constructor.
    destruct (typing_type_rank ε b T HG Hb) as [r Hr].
    destruct IH as [bound Hbound].
    { intros t Hin. apply Htyped. right; exact Hin. }
    exists (Nat.max r bound). intros t Hin.
    destruct Hin as [<-|Hin].
    + exists r. split; [exact Hr | apply Nat.le_max_l].
    + destruct (Hbound t Hin) as [s [Hs Hle]].
      exists s. split; [exact Hs |].
      eapply Nat.le_trans; [exact Hle | apply Nat.le_max_r].
Qed.

Lemma universe_type_rank i : TypeRank ε (𝓤 i) 0.
Proof.
  exists (𝓤 0). split; constructor; reflexivity.
Qed.

(** The rank is the sort of the term's TYPE, not its own universe index.
    In particular all universe atoms have type rank zero.  Application
    cannot increase this rank, even for dependent types or partial spines. *)
Theorem decoded_rank_bound basis bound (e : Expression basis) r :
  BasisRankBound basis bound -> TypeRank ε (decode e) r -> r <= bound.
Proof.
  intros Hbasis. revert r.
  induction e as [t Hin|i|f IHf u IHu]; intros r Hrank; cbn [decode] in *.
  - destruct (Hbasis t Hin) as [s [Hs Hle]].
    assert (r = s).
    { eapply type_rank_unique; [constructor | exact Hrank | exact Hs]. }
    subst r. exact Hle.
  - assert (r = 0).
    { eapply type_rank_unique; [constructor | exact Hrank | apply universe_type_rank]. }
    subst r. apply Nat.le_0_l.
  - destruct Hrank as [T [Happ HT]].
    destruct (app_inversion RankSorts (decode f) (decode u) T Happ)
      as [A [B [Hf [Hu Heq]]]].
    assert (HG : @wf nat RankSorts 0 ε) by constructor.
    destruct (typing_type_rank ε (decode f) (Π A B) HG Hf) as [s Hs].
    assert (r <= s).
    { apply (application_rank_le_function ε (decode f) (decode u) r s HG).
      - exists T; split; assumption.
      - exact Hs. }
    specialize (IHf s Hs). lia.
Qed.

Corollary typed_decoded_rank_bound basis bound (e : Expression basis) T :
  BasisRankBound basis bound -> @typ nat RankSorts 0 ε (decode e) T ->
  exists r, TypeRank ε (decode e) r /\ r <= bound.
Proof.
  intros Hbasis Htyped.
  assert (HG : @wf nat RankSorts 0 ε) by constructor.
  destruct (typing_type_rank ε (decode e) T HG Htyped) as [r Hr].
  exists r. split; [exact Hr | eapply decoded_rank_bound; eassumption].
Qed.

(** Conversion cannot evade the bound.  This uses confluence, original
    subject reduction and uniqueness of typing; no normalization hypothesis
    on either the representation or the target is required. *)
Theorem decoded_conversion_rank_bound basis bound (e : Expression basis)
  target T r :
  BasisRankBound basis bound -> @typ nat RankSorts 0 ε (decode e) T ->
  TypeRank ε target r -> def_equiv nat 0 (decode e) target -> r <= bound.
Proof.
  intros Hbasis Htyped Htarget Heq.
  destruct (typed_decoded_rank_bound basis bound e T Hbasis Htyped)
    as [s [Hs Hle]].
  assert (s = r).
  { eapply type_rank_conversion; [constructor | exact Hs | exact Htarget | exact Heq]. }
  subst s. exact Hle.
Qed.

(** Explicit original closed inhabitants at every type rank.  These are the
    same elementary witnesses used in SelfInterpreter.RankObstruction,
    repeated here to avoid depending on the interpreter development.

       A_0 = U_0,       A_(r+1) = Pi _:A_r. U_0
       v_0 = U_0,       v_(r+1) = lambda _:A_r. U_0.
 *)
Fixpoint obstruction_type (r : nat) {n} : Term nat n :=
  match r with
  | 0 => 𝓤 0
  | S k => Π (obstruction_type k) (𝓤 0)
  end.

Definition obstruction_value (r : nat) {n} : Term nat n :=
  match r with
  | 0 => 𝓤 0
  | S k => lam (obstruction_type k) (𝓤 0)
  end.

Theorem obstruction_type_sort r : forall n (G : Ctx nat n),
  @typ nat RankSorts n G (obstruction_type r) (𝓤 r).
Proof.
  induction r; intros n G; cbn [obstruction_type].
  - constructor; reflexivity.
  - eapply typ_Π with (ℓₜ := r) (ℓᵤ := 0).
    + apply IHr.
    + constructor; reflexivity.
    + change (S r = Nat.max (S r) 0). rewrite Nat.max_0_r. reflexivity.
Qed.

Theorem obstruction_value_typing r n (G : Ctx nat n) :
  @typ nat RankSorts n G (obstruction_value r) (obstruction_type r).
Proof.
  destruct r; cbn [obstruction_value obstruction_type].
  - constructor; reflexivity.
  - eapply typ_λ with (ℓ := r).
    + apply obstruction_type_sort.
    + constructor; reflexivity.
Qed.

Theorem obstruction_value_type_rank r n (G : Ctx nat n) :
  TypeRank G (obstruction_value r) r.
Proof.
  exists (obstruction_type r).
  split; [apply obstruction_value_typing | apply obstruction_type_sort].
Qed.

(** A deliberately permissive completeness requirement: the entire decoded
    expression must be originally typable, but may have any type and need
    only be beta-CONVERTIBLE to the target.  No quoter, effectiveness,
    forward reduction, size or number-of-applications bound is imposed. *)
Definition BetaComplete (basis : list (Term nat 0)) : Prop :=
  forall target T, @typ nat RankSorts 0 ε target T ->
    exists (e : Expression basis) U,
      @typ nat RankSorts 0 ε (decode e) U /\
      def_equiv nat 0 (decode e) target.

Theorem no_finite_typed_basis basis : TypedBasis basis -> ~ BetaComplete basis.
Proof.
  intros Htyped Hcomplete.
  destruct (finite_basis_rank_bound basis Htyped) as [bound Hbound].
  destruct (Hcomplete (obstruction_value (S bound)) (obstruction_type (S bound))
    (obstruction_value_typing (S bound) 0 ε)) as [e [U [He Heq]]].
  assert (S bound <= bound).
  { eapply decoded_conversion_rank_bound;
      [exact Hbound | exact He | apply obstruction_value_type_rank | exact Heq]. }
  lia.
Qed.

Print Assumptions finite_basis_rank_bound.
Print Assumptions decoded_rank_bound.
Print Assumptions typed_decoded_rank_bound.
Print Assumptions decoded_conversion_rank_bound.
Print Assumptions obstruction_type_sort.
Print Assumptions obstruction_value_typing.
Print Assumptions obstruction_value_type_rank.
Print Assumptions no_finite_typed_basis.
