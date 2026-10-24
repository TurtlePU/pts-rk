(** Representation bounds, including repeated fields and annotations.
    These are data-size bounds, not a machine-level checker cost theorem. *)
From Stdlib Require Import Lists.List Arith.PeanoNat NArith.NArith Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk.SelfConsistency Require Import NativeProofCodes StructuralCodes
  CertificateSerialization RankCompression.
Import NativeProofCodes.NativeProofCodes.

Fixpoint positive_bits (p : positive) : nat :=
  match p with xH => 1 | xO p | xI p => S (positive_bits p) end.

Theorem binary_encoding_size p : S (code_size (encode_positive p)) = 2 * positive_bits p.
Proof. induction p; cbn [encode_positive code_size positive_bits]; lia. Qed.

Theorem term_labels_encoded_size {n} (t : Term nat n) :
  length (term_labels t) <= code_size (encode_term t).
Proof.
  induction t; cbn [term_labels encode_term code_size length];
    repeat rewrite length_app; lia.
Qed.

Ltac term_size_facts :=
  repeat match goal with
  | |- context [length (term_labels ?t)] =>
    let k := fresh "k" in let E := fresh "Esize" in let H := fresh "Hsize" in
    remember (length (term_labels t)) as k eqn:E;
    pose proof (term_labels_encoded_size t) as H; rewrite <- E in H
  end.

Theorem step_labels_encoded_size {n} (p : StepCode n) :
  length (step_labels p) <= code_size (encode_step p).
Proof.
  induction p; cbn [step_labels encode_step code_size]; repeat rewrite length_app;
    term_size_facts; lia.
Qed.

Theorem equality_labels_encoded_size {n} (p : EqualityCode n) :
  length (equality_labels p) <= code_size (encode_equality p).
Proof.
  induction p; cbn [equality_labels encode_equality code_size]; repeat rewrite length_app;
    term_size_facts; try lia.
  pose proof (step_labels_encoded_size s); lia.
Qed.

Theorem certificate_labels_encoded_size {n} (p : Certificate n) :
  length (certificate_labels p) <= code_size (encode_certificate p).
Proof.
  induction p; cbn [certificate_labels encode_certificate code_size length];
    repeat rewrite length_app; cbn [length]; term_size_facts; try lia.
  pose proof (equality_labels_encoded_size e); lia.
Qed.

Theorem context_labels_encoded_size {n} (c : ContextCode n) :
  length (context_code_labels c) <= code_size (encode_context c).
Proof.
  induction c; cbn [context_code_labels encode_context code_size length];
    repeat rewrite length_app; [lia |].
  pose proof (certificate_labels_encoded_size c0); lia.
Qed.

Theorem input_support_encoded_size {n} (c : ContextCode n) (p : Certificate n) :
  length (input_support c p) <= code_size (encode_input c p).
Proof.
  unfold input_support, encode_input; cbn [length code_size]; rewrite length_app.
  pose proof (context_labels_encoded_size c).
  pose proof (certificate_labels_encoded_size p); lia.
Qed.

Theorem compressed_label_serialized_bound {n} (c : ContextCode n) (p : Certificate n) x :
  compress (input_support c p) x <= code_size (encode_input c p).
Proof.
  eapply Nat.le_trans; [apply compress_bound | apply input_support_encoded_size].
Qed.

Theorem decoded_label_bound q n (c : ContextCode n) (p : Certificate n) x :
  decode_input q = Some (existT _ n (c,p)) ->
  compress (input_support c p) x <= code_size q.
Proof.
  intro H; apply input_decode_encode in H; cbn [encode_packed] in H.
  rewrite <- H; apply compressed_label_serialized_bound.
Qed.
