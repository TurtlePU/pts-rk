(** Concrete countable code universes for the paper's set model.
    Finite and sort decoding are constructed here. Infinite carriers are
    explicit parameters: no aleph hierarchy or GCH bound is assumed/proved. *)
From Stdlib Require Import Arith.PeanoNat Arith.Compare_dec Lia.
From ZFC Require Import Sets Axioms Cartesian.
From PTSrkModel Require Import SetFunctions.

Module CodeUniverses.

Fixpoint numeral (n : nat) : Ens :=
  match n with 0 => Vide | S n => Sing (numeral n) end.
Lemma numeral_injective n m : EQ (numeral n) (numeral m) -> n = m.
Proof.
  revert m; induction n; intros [|m] E; cbn [numeral] in E; auto.
  - destruct (not_EQ_Vide_Sing _ E).
  - destruct (not_EQ_Sing_Vide _ E).
  - f_equal. apply IHn, EQ_Sing_EQ; exact E.
Qed.

Inductive Code := finite (n : nat) | infinite (j : nat) | sort (j : nat).
Definition key c := match c with
  | finite n => 3*n | infinite j => S (3*j) | sort j => S (S (3*j)) end.
Definition repr c := numeral (key c).
Theorem repr_injective c d : EQ (repr c) (repr d) -> c = d.
Proof.
  intro E. apply numeral_injective in E.
  destruct c, d; cbn [key] in E; try (f_equal; lia); lia.
Qed.
Definition Allowed i c : Prop :=
  match c with infinite j => j <= i | _ => True end.
Definition allowed_dec i c : {Allowed i c} + {~ Allowed i c}.
Proof. destruct c; cbn [Allowed]; [left; exact I | apply le_dec | left; exact I]. Defined.
Definition U i : Ens :=
  sup {c : Code | Allowed i c} (fun c => repr (proj1_sig c)).

Theorem universe_membership i x :
  IN x (U i) <-> exists c, Allowed i c /\ EQ x (repr c).
Proof.
  split.
  - intros [[c Hc] E]. exists c; auto.
  - intros [c [Hc E]]. exists (Specif.exist _ c Hc); exact E.
Qed.
Theorem code_membership i c : IN (repr c) (U i) <-> Allowed i c.
Proof.
  rewrite universe_membership. split.
  - intros [d [Hd E]]. apply repr_injective in E; subst; exact Hd.
  - intro Hc. exists c; split; [exact Hc | apply EQ_refl].
Qed.
Theorem sort_in_every_universe i j : IN (repr (sort j)) (U i).
Proof. apply code_membership; exact I. Qed.
Theorem finite_in_every_universe i n : IN (repr (finite n)) (U i).
Proof. apply code_membership; exact I. Qed.
Theorem infinite_membership i j : IN (repr (infinite j)) (U i) <-> j <= i.
Proof. apply code_membership. Qed.
Theorem universe_monotone i j : i <= j -> INC (U i) (U j).
Proof.
  intros Hij x Hx. apply universe_membership in Hx as [c [Hc E]].
  apply universe_membership. exists c; split; [| exact E].
  destruct c; cbn [Allowed] in *; auto; lia.
Qed.
Theorem universe_strict i : ~ INC (U (S i)) (U i).
Proof.
  intro H. assert (Hin : IN (repr (infinite (S i))) (U (S i))).
  { apply infinite_membership; lia. }
  pose proof (H _ Hin) as Hout. apply infinite_membership in Hout; lia.
Qed.

Definition next c := match c with
  | finite n => infinite n | infinite n => sort n | sort n => finite (S n) end.
Fixpoint enumerate n := match n with 0 => finite 0 | S n => next (enumerate n) end.
Lemma enumerate_cycle n :
  enumerate (3*n) = finite n /\
  enumerate (S (3*n)) = infinite n /\
  enumerate (S (S (3*n))) = sort n.
Proof.
  induction n as [|n [H0 [H1 H2]]]; [repeat split; reflexivity |].
  replace (3*S n) with (S (S (S (3*n)))) by lia.
  change (next (enumerate (S (S (3*n)))) = finite (S n) /\
    next (next (enumerate (S (S (3*n))))) = infinite (S n) /\
    next (next (next (enumerate (S (S (3*n)))))) = sort (S n)).
  rewrite H2; repeat split; reflexivity.
Qed.
Lemma enumerate_key c : enumerate (key c) = c.
Proof. destruct c; cbn [key]; apply enumerate_cycle. Qed.
Definition enumerate_universe i n : Ens :=
  if allowed_dec i (enumerate n) then repr (enumerate n) else repr (finite 0).
Theorem universe_enumeration i : EQ (U i) (sup nat (enumerate_universe i)).
Proof.
  apply INC_EQ.
  - intros x Hx. apply universe_membership in Hx as [c [Hc E]].
    exists (key c). unfold enumerate_universe. rewrite enumerate_key.
    destruct (allowed_dec i c); [exact E | contradiction].
  - intros x [n E]. apply (IN_sound_left (enumerate_universe i n) x (U i)).
    + apply EQ_sym; exact E.
    + unfold enumerate_universe. destruct (allowed_dec i (enumerate n)).
      * apply code_membership; assumption.
      * apply finite_in_every_universe.
Qed.

Definition finite_carrier n : Ens :=
  sup {k : nat | k < n} (fun k => numeral (proj1_sig k)).
Theorem finite_carrier_membership n x :
  IN x (finite_carrier n) <-> exists k, k < n /\ EQ x (numeral k).
Proof.
  split.
  - intros [[k Hk] E]. exists k; auto.
  - intros [k [Hk E]]. exists (Specif.exist _ k Hk); exact E.
Qed.
Theorem finite_carrier_zero : EQ (finite_carrier 0) Vide.
Proof.
  apply tout_vide_est_Vide. intros x Hx. exfalso.
  apply finite_carrier_membership in Hx as [k [Hk _]]. lia.
Qed.

Section Decoding.
Variable infinite_carrier : nat -> Ens.
Definition code_value c : Ens := match c with
  | finite n => finite_carrier n
  | infinite j => infinite_carrier j
  | sort j => U j end.

(** Separation over the countable code index, followed by union, implements
    total extensional decoding without deciding equality of arbitrary sets.
    On a genuine code the value family is a singleton up to EQ. *)
Definition El (x : Ens) : Ens :=
  Union (sup {c : Code | EQ x (repr c)} (fun c => code_value (proj1_sig c))).
Theorem decoding_membership x y :
  IN y (El x) <-> exists c, EQ x (repr c) /\ IN y (code_value c).
Proof.
  split.
  - intro H. destruct (Union_IN _ _ H) as [v [Hv Hy]].
    destruct Hv as [[c Hc] E]. exists c; split; [exact Hc |].
    exact (IN_sound_right y v (code_value c) E Hy).
  - intros [c [Hc Hy]]. unfold El.
    eapply IN_Union with (E' := code_value c); [| exact Hy].
    exists (Specif.exist _ c Hc). apply EQ_refl.
Qed.
Theorem decoding_extensional x y : EQ x y -> EQ (El x) (El y).
Proof.
  intro E. apply INC_EQ; intros z Hz; apply decoding_membership in Hz as [c [Hc Hzin]];
    apply decoding_membership; exists c; split; [| exact Hzin | | exact Hzin].
  - eapply EQ_tran; [apply EQ_sym; exact E | exact Hc].
  - eapply EQ_tran; [exact E | exact Hc].
Qed.
Theorem decode_repr c : EQ (El (repr c)) (code_value c).
Proof.
  apply INC_EQ.
  - intros y Hy. apply decoding_membership in Hy as [d [E Hd]].
    apply repr_injective in E; subst; exact Hd.
  - intros y Hy. apply decoding_membership. exists c; split; [apply EQ_refl | exact Hy].
Qed.
Theorem decode_sort j : EQ (El (repr (sort j))) (U j).
Proof. apply decode_repr. Qed.
Theorem decode_infinite j : EQ (El (repr (infinite j))) (infinite_carrier j).
Proof. apply decode_repr. Qed.
Theorem decode_empty : EQ (El (repr (finite 0))) Vide.
Proof. eapply EQ_tran; [apply decode_repr | apply finite_carrier_zero]. Qed.
Theorem sort_axiom i : IN (repr (sort i)) (El (repr (sort 0))).
Proof.
  eapply IN_sound_right; [apply EQ_sym; apply decode_sort | apply sort_in_every_universe].
Qed.
Theorem empty_code_in_sort j : IN (repr (finite 0)) (El (repr (sort j))).
Proof.
  eapply IN_sound_right; [apply EQ_sym; apply decode_sort | apply finite_in_every_universe].
Qed.
(** The ordinary decoded function space for Bottom is empty. Its cardinal
    code and the interpretation of the original PTS term are still absent. *)
Theorem decoded_sort_product_empty j g :
  ~ IN g (dependent_product (El (repr (sort j))) El).
Proof.
  eapply dependent_product_empty_fiber.
  - apply empty_code_in_sort.
  - apply decode_empty.
Qed.
End Decoding.

Print Assumptions repr_injective.
Print Assumptions code_membership.
Print Assumptions universe_monotone.
Print Assumptions universe_strict.
Print Assumptions universe_enumeration.
Print Assumptions finite_carrier_zero.
Print Assumptions decoding_extensional.
Print Assumptions decode_repr.
Print Assumptions sort_axiom.
Print Assumptions decoded_sort_product_empty.
Check universe_enumeration.
Check decode_repr.
Check sort_axiom.
Check decoded_sort_product_empty.
End CodeUniverses.
