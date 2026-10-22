From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk.NormalizationComplexity Require Import Bounds.

(** Knuth's double arrow: tetration base height = base ↑↑ height. *)
Fixpoint tetration (base height : nat) : nat :=
  match height with 0 => 1 | S h => base ^ tetration base h end.

Theorem tower_le_tetration d n :
  2 <= n -> tower d n <= tetration n (S d).
Proof.
  intro Hn; induction d.
  - change (n <= n ^ 1); rewrite Nat.pow_1_r; reflexivity.
  - change (2 ^ tower d n <= n ^ tetration n (S d)).
    apply Nat.pow_le_mono; lia.
Qed.

Theorem tower_le_knuth d n :
  tower d n <= tetration (Nat.max 2 n) (S d).
Proof.
  eapply Nat.le_trans; [apply tower_monotone, Nat.le_max_r |].
  apply tower_le_tetration, Nat.le_max_l.
Qed.

Print Assumptions tower_le_tetration.
Print Assumptions tower_le_knuth.
