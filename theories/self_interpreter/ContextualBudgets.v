From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
From PTSrk.SelfInterpreter Require Import ContextualTelescope.
Import ListNotations.

(** Finite, executable RANK-VECTOR enumeration. These descriptors contain
    no source terms or domain annotations. This does not supply the uniform
    law families that must eventually be instantiated at each descriptor. *)
Module ContextualBudgets.
Module CT := ContextualTelescope.ContextualTelescope.

Fixpoint vectors_exact (length_bound rank_bound : nat) : list (list nat) :=
  match length_bound with
  | 0 => [[]]
  | S l => flat_map (fun r => map (cons r) (vectors_exact l rank_bound))
      (seq 0 (S rank_bound))
  end.
Fixpoint vectors (length_bound rank_bound : nat) : list (list nat) :=
  match length_bound with
  | 0 => [[]]
  | S l => vectors l rank_bound ++ vectors_exact (S l) rank_bound
  end.
Fixpoint count (length_bound rank_bound : nat) : nat :=
  match length_bound with
  | 0 => 1
  | S l => count l rank_bound + Nat.pow (S rank_bound) (S l)
  end.

Theorem vectors_exact_spec l k rs :
  In rs (vectors_exact l k) <-> length rs = l /\ Forall (fun r => r <= k) rs.
Proof.
  revert rs; induction l; intro rs; cbn [vectors_exact].
  - split.
    + intros [H | H]; [subst; split; constructor | contradiction].
    + intros [H _]; destruct rs; [now left | discriminate].
  - rewrite in_flat_map; split.
    + intros [r [Hr Hrs]]; apply in_map_iff in Hrs as [tail [Hrs Htail]]; subst rs.
      apply IHl in Htail as [HL HF]; apply in_seq in Hr.
      split; [cbn; now rewrite HL | constructor; [lia | exact HF]].
    + intros [HL HF]; destruct rs as [| r tail]; [discriminate |].
      inversion HF; subst. exists r; split.
      * apply in_seq; lia.
      * apply in_map; apply IHl; split; [cbn in HL; lia | assumption].
Qed.

Theorem vectors_spec l k rs : In rs (vectors l k) <-> CT.bounded l k rs.
Proof.
  unfold CT.bounded; revert rs; induction l; intro rs; cbn [vectors].
  - split.
    + intros [H | H]; [subst; split; [cbn; lia | constructor] | contradiction].
    + intros [H _]; destruct rs; [now left | cbn in H; lia].
  - rewrite in_app_iff, IHl, vectors_exact_spec; split.
    + intros [[HL HF] | [HL HF]]; split; [lia | exact HF | lia | exact HF].
    + intros [HL HF]; destruct (Nat.eq_dec (length rs) (S l)).
      * right; split; assumption.
      * left; split; [lia | exact HF].
Qed.

Lemma flat_map_constant_length (A B : Type) (f : A -> list B) xs c :
  (forall x, In x xs -> length (f x) = c) ->
  length (flat_map f xs) = length xs * c.
Proof.
  induction xs; intro H; cbn; [reflexivity |].
  rewrite length_app, H by (now left).
  rewrite IHxs by (intros; apply H; now right); lia.
Qed.

Theorem vectors_exact_length l k : length (vectors_exact l k) = Nat.pow (S k) l.
Proof.
  induction l; cbn [vectors_exact]; [reflexivity |].
  rewrite flat_map_constant_length with (c := Nat.pow (S k) l).
  - rewrite length_seq; reflexivity.
  - intros; rewrite length_map; exact IHl.
Qed.

Theorem vectors_length l k : length (vectors l k) = count l k.
Proof.
  induction l; cbn [vectors count]; [reflexivity |].
  rewrite length_app, IHl, vectors_exact_length; reflexivity.
Qed.

Theorem every_vector_enumerated rs :
  In rs (vectors (length rs) (CT.vector_bound rs)).
Proof. apply vectors_spec, CT.every_vector_bounded. Qed.

Lemma zero_rank n : CT.rank (repeat 0 (S n)) 0 = 1.
Proof.
  induction n; [reflexivity |].
  change (Nat.max 1 (CT.rank (repeat 0 (S n)) 0) = 1); now rewrite IHn.
Qed.

Theorem rank_does_not_bound_length length_bound :
  exists rs, CT.rank rs 0 = 1 /\ length_bound < length rs.
Proof.
  exists (repeat 0 (S length_bound)); split; [apply zero_rank | rewrite repeat_length; lia].
Qed.

Print Assumptions vectors_exact_spec.
Print Assumptions vectors_spec.
Print Assumptions vectors_exact_length.
Print Assumptions vectors_length.
Print Assumptions every_vector_enumerated.
Print Assumptions rank_does_not_bound_length.
End ContextualBudgets.
