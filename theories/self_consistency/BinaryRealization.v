(** Independent binary carry specification and executable original-PTS
    witnesses at every standard binary code.  Native N/nat only describe
    the existing encoding; no internal Church numeral conversion is used. *)
From Stdlib Require Import NArith.NArith NArith.Nnat.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  InternalBinary ResourceRealization.

Module BinaryRealization.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  InternalBinary.InternalBinary ResourceRealization.ResourceRealization.

Inductive positive_code : code -> Prop :=
| positive_one : positive_code (Atom POne)
| positive_even p : positive_code p -> positive_code (Pair (Atom PEven) p)
| positive_odd p : positive_code p -> positive_code (Pair (Atom POdd) p).
Inductive successor_code : code -> code -> Prop :=
| successor_zero : successor_code (Atom NZero) (Atom POne)
| successor_one : successor_code (Atom POne) (Pair (Atom PEven) (Atom POne))
| successor_even p : positive_code p ->
    successor_code (Pair (Atom PEven) p) (Pair (Atom POdd) p)
| successor_odd p q : positive_code p -> successor_code p q ->
    successor_code (Pair (Atom POdd) p) (Pair (Atom PEven) q).

Theorem encoded_positive p : positive_code (encode_positive p).
Proof. induction p; cbn; constructor; assumption. Qed.
Theorem positive_code_exact c :
  positive_code c <-> exists p, c = encode_positive p.
Proof.
  split.
  - intro H; induction H as [|c H [p ->]|c H [p ->]];
      [exists xH |exists (xO p) |exists (xI p)]; reflexivity.
  - intros [p ->]; apply encoded_positive.
Qed.
Theorem encoded_positive_successor p :
  successor_code (encode_positive p) (encode_positive (Pos.succ p)).
Proof.
  induction p; cbn [encode_positive Pos.succ];
    constructor; auto using encoded_positive.
Qed.

Definition encode_N n := match n with N0 => Atom NZero | Npos p => encode_positive p end.
Lemma encode_N_injective a b : encode_N a = encode_N b -> a = b.
Proof.
  destruct a as [|a], b as [|b]; cbn [encode_N]; intro H; try reflexivity.
  - exfalso; apply (positive_has_nonzero_code b); symmetry; exact H.
  - exfalso; apply (positive_has_nonzero_code a); exact H.
  - apply (f_equal decode_positive) in H; rewrite !positive_roundtrip in H.
    inversion H; reflexivity.
Qed.
Theorem successor_code_exact a b : successor_code a b <->
  exists n, a = encode_N n /\ b = encode_N (N.succ n).
Proof.
  split.
  - intro H; induction H as [| |p Hp|p q Hp Hpq [n [En Eq]]].
    + exists N0; split; reflexivity.
    + exists (Npos xH); split; reflexivity.
    + destruct (proj1 (positive_code_exact _) Hp) as [p' ->].
      exists (Npos (xO p')); split; reflexivity.
    + destruct (proj1 (positive_code_exact _) Hp) as [p' Ep].
      assert (E : n = Npos p').
      { apply encode_N_injective; rewrite <- En, Ep; reflexivity. }
      subst n; subst p; subst q.
      exists (Npos (xI p')); split; reflexivity.
  - intros [[|p] [-> ->]]; [constructor |apply encoded_positive_successor].
Qed.
Theorem encoded_natural_successor n :
  successor_code (encode_nat n) (encode_nat (S n)).
Proof.
  apply successor_code_exact; exists (N.of_nat n); split; [reflexivity |].
  unfold encode_nat; rewrite Nat2N.inj_succ; reflexivity.
Qed.
Theorem successor_code_natural_exact a b : successor_code a b <->
  exists n, a = encode_nat n /\ b = encode_nat (S n).
Proof.
  split.
  - intro H; apply successor_code_exact in H; destruct H as [n [-> ->]].
    exists (N.to_nat n); unfold encode_nat.
    rewrite Nat2N.inj_succ, N2Nat.id; split; reflexivity.
  - intros [n [-> ->]]; apply encoded_natural_successor.
Qed.

Definition PosTerm {n} (x : Term nat n) := app (lift_closed positive) x.
Definition NumTerm {n} (x : Term nat n) := app (lift_closed number) x.
Definition SuccTerm {n} (x y : Term nat n) := Rel successor x y.
Definition BitTerm {n} (side : bool) (x : Term nat n) :=
  PairTerm (lift_closed (atom (if side then PEven else POdd))) x.
Lemma PosTerm_replace {m n} (f : Fin m -> Term nat n) x :
  replace f (PosTerm x) = PosTerm (replace f x).
Proof. unfold PosTerm; cbn [replace]; rewrite replace_lift_closed; reflexivity. Qed.
Lemma NumTerm_replace {m n} (f : Fin m -> Term nat n) x :
  replace f (NumTerm x) = NumTerm (replace f x).
Proof. unfold NumTerm; cbn [replace]; rewrite replace_lift_closed; reflexivity. Qed.
Lemma SuccTerm_replace {m n} (f : Fin m -> Term nat n) x y :
  replace f (SuccTerm x y) = SuccTerm (replace f x) (replace f y).
Proof. apply Rel_replace. Qed.
Lemma BitTerm_replace {m n} (f : Fin m -> Term nat n) side x :
  replace f (BitTerm side x) = BitTerm side (replace f x).
Proof. unfold BitTerm; rewrite PairTerm_replace, replace_lift_closed; reflexivity. Qed.
Ltac binary_substitution H :=
  unfold subst in H;
  repeat first [rewrite PosTerm_replace in H | rewrite NumTerm_replace in H
    | rewrite SuccTerm_replace in H | rewrite BitTerm_replace in H
    | rewrite replace_product in H | rewrite replace_arrow in H
    | rewrite replace_lift_closed in H | rewrite replace_shift_substitution in H
    | rewrite replace_shift in H
    | progress cbn [replace transpose fin_match V0 v1 eq_rect] in H];
  repeat rewrite lift_closed_zero in H.

Lemma pos_step_application side p hp : Typed ε p carrier ->
  Typed ε hp (PosTerm p) ->
  Typed ε (app (app (pos_step side) p) hp) (PosTerm (BitTerm side p)).
Proof.
  intros Hp Hhp; pose proof (pos_step_typed side) as H.
  assert (E : pos_step_type side =
    Π carrier (Arrow (PosTerm V0) (PosTerm (BitTerm side V0))))
    by (destruct side; reflexivity).
  rewrite E in H; pose proof (tApp H Hp) as J; binary_substitution J.
  eapply arrow_application; [exact J |exact Hhp].
Qed.
Lemma num_positive_application p hp : Typed ε p carrier ->
  Typed ε hp (PosTerm p) ->
  Typed ε (app (app num_positive p) hp) (NumTerm p).
Proof.
  intros Hp Hhp; pose proof num_positive_typed as H.
  change (Typed ε num_positive (Π carrier (Arrow (PosTerm V0) (NumTerm V0)))) in H.
  pose proof (tApp H Hp) as J; binary_substitution J.
  eapply arrow_application; [exact J |exact Hhp].
Qed.
Lemma succ_even_application p hp : Typed ε p carrier ->
  Typed ε hp (PosTerm p) ->
  Typed ε (app (app succ_even p) hp) (SuccTerm (BitTerm true p) (BitTerm false p)).
Proof.
  intros Hp Hhp; pose proof succ_even_typed as H.
  change (Typed ε succ_even (Π carrier (Arrow (PosTerm V0)
    (SuccTerm (BitTerm true V0) (BitTerm false V0))))) in H.
  pose proof (tApp H Hp) as J; binary_substitution J.
  eapply arrow_application; [exact J |exact Hhp].
Qed.
Definition carry_application p q hp h := app (app (app (app succ_odd p) q) hp) h.
Lemma succ_odd_application p q hp h :
  Typed ε p carrier -> Typed ε q carrier ->
  Typed ε hp (PosTerm p) -> Typed ε h (SuccTerm p q) ->
  Typed ε (carry_application p q hp h) (SuccTerm (BitTerm false p) (BitTerm true q)).
Proof.
  intros Hp Hq Hhp Hh; pose proof succ_odd_typed as H.
  change (Typed ε succ_odd (Π carrier (Π (lift_closed carrier)
    (Arrow (PosTerm v1) (Arrow (SuccTerm v1 V0)
      (SuccTerm (BitTerm false v1) (BitTerm true V0))))))) in H.
  pose proof (tApp H Hp) as H1; binary_substitution H1.
  pose proof (tApp H1 Hq) as H2; binary_substitution H2.
  unfold carry_application; eapply arrow_application;
    [eapply arrow_application; [exact H2 |exact Hhp] |exact Hh].
Qed.

Fixpoint positive_witness (p : BinNums.positive) : closed_term :=
  match p with
  | xH => pos_one
  | xO p => app (app (pos_step true) (quote (encode_positive p))) (positive_witness p)
  | xI p => app (app (pos_step false) (quote (encode_positive p))) (positive_witness p)
  end.
Definition natural_witness n := match N.of_nat n with
  | N0 => num_zero
  | Npos p => app (app num_positive (quote (encode_positive p))) (positive_witness p)
  end.
Fixpoint positive_successor_witness (p : BinNums.positive) : closed_term :=
  match p with
  | xH => succ_one
  | xO p => app (app succ_even (quote (encode_positive p))) (positive_witness p)
  | xI p => carry_application (quote (encode_positive p))
      (quote (encode_positive (Pos.succ p))) (positive_witness p)
      (positive_successor_witness p)
  end.
Definition natural_successor_witness n := match N.of_nat n with
  | N0 => succ_zero | Npos p => positive_successor_witness p end.

Theorem positive_witness_typed p :
  Typed ε (positive_witness p) (PosTerm (quote (encode_positive p))).
Proof.
  induction p; cbn [positive_witness encode_positive quote];
    [apply (pos_step_application false) |apply (pos_step_application true) |];
    auto using quote_typed, pos_one_typed.
Qed.
Theorem natural_witness_typed n :
  Typed ε (natural_witness n) (NumTerm (quote (encode_nat n))).
Proof.
  unfold natural_witness, encode_nat; destruct (N.of_nat n) as [|p].
  - exact num_zero_typed.
  - apply num_positive_application; auto using quote_typed, positive_witness_typed.
Qed.
Theorem positive_successor_witness_typed p :
  Typed ε (positive_successor_witness p)
    (SuccTerm (quote (encode_positive p)) (quote (encode_positive (Pos.succ p)))).
Proof.
  induction p; cbn [positive_successor_witness Pos.succ encode_positive quote].
  - apply succ_odd_application; auto using quote_typed, positive_witness_typed.
  - apply succ_even_application; auto using quote_typed, positive_witness_typed.
  - exact succ_one_typed.
Qed.
Theorem natural_successor_witness_typed n :
  Typed ε (natural_successor_witness n)
    (SuccTerm (quote (encode_nat n)) (quote (encode_nat (S n)))).
Proof.
  unfold natural_successor_witness, encode_nat; rewrite Nat2N.inj_succ.
  destruct (N.of_nat n) as [|p]; [exact succ_zero_typed |].
  apply positive_successor_witness_typed.
Qed.
Theorem standard_successor_realized a b : successor_code a b ->
  exists h, Typed ε h (SuccTerm (quote a) (quote b)).
Proof.
  intro H; apply successor_code_natural_exact in H; destruct H as [n [-> ->]].
  exists (natural_successor_witness n); apply natural_successor_witness_typed.
Qed.
End BinaryRealization.
