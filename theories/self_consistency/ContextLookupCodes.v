(** Faithful literal contexts and the ORIGINAL shifted contextual lookup.
    This is distinct from CertificateSerialization.encode_context, whose
    extensions store declaration certificates, not declarations themselves.
    Raw lookup is a local operation: whole-context scope is separate. *)
From Stdlib Require Import Arith.PeanoNat.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context.
From PTSrk.SelfConsistency Require Import StructuralCodes CodeSubstitution
  NativeProofCodes.

Module ContextLookupCodes.

Definition empty_code := Atom GEmpty.
Definition extend_code G A := Pair (Atom GExtend) (Pair G A).
Fixpoint encode_ctx {n} (G : Ctx nat n) : code :=
  match G with
  | ε => empty_code
  | G & A => extend_code (encode_ctx G) (encode_term A)
  end.
Fixpoint decode_ctx (g : code) (n : nat) : option (Ctx nat n) :=
  match g with
  | Atom GEmpty =>
      match n with 0 => Some ε | S _ => None end
  | Pair (Atom GExtend) (Pair g A) =>
      match n with
      | 0 => None
      | S k => g <- decode_ctx g k ;; A <- decode_term A k ;; Some (g & A)
      end
  | _ => None
  end.

Theorem ctx_roundtrip {n} (G : Ctx nat n) :
  decode_ctx (encode_ctx G) n = Some G.
Proof.
  induction G; cbn [encode_ctx empty_code extend_code decode_ctx];
    try rewrite IHG; cbn [bind]; try rewrite term_roundtrip; reflexivity.
Qed.
Theorem encode_ctx_injective {n} (G H : Ctx nat n) :
  encode_ctx G = encode_ctx H -> G = H.
Proof.
  intro E; pose proof (ctx_roundtrip G) as K; rewrite E, ctx_roundtrip in K;
    congruence.
Qed.
Theorem ctx_decode_encode g : forall n (G : Ctx nat n),
  decode_ctx g n = Some G -> encode_ctx G = g.
Proof.
  revert g; fix IH 1; intros g n G H.
  destruct g as [t|h args].
  - destruct t; try discriminate; destruct n; try discriminate.
    inversion H; reflexivity.
  - destruct h as [t|h a]; [|discriminate].
    destruct t; try discriminate.
    destruct args as [t|g A]; [discriminate|].
    destruct n; [discriminate|]; cbn [decode_ctx] in H.
    parse_options H; inversion H; subst; cbn [encode_ctx extend_code].
    rewrite (IH g n c E), (term_decode_encode A n t E0); reflexivity.
Qed.

(** Both zero and successor lookup shift once at EACH context extension. *)
Fixpoint raw_lookup (g : code) (i : nat) : option code :=
  match g with
  | Pair (Atom GExtend) (Pair g A) =>
      match i with
      | 0 => raw_rename S A
      | S j => B <- raw_lookup g j ;; raw_rename S B
      end
  | _ => None
  end.
Definition raw_lookup_code g i := k <- decode_nat i ;; raw_lookup g k.

Inductive LookupGraph : code -> nat -> code -> Prop :=
| LookupZero g A B : raw_rename S A = Some B ->
    LookupGraph (extend_code g A) 0 B
| LookupSucc g A i B C : LookupGraph g i B -> raw_rename S B = Some C ->
    LookupGraph (extend_code g A) (S i) C.

Theorem lookup_graph_output g i A : LookupGraph g i A -> raw_lookup g i = Some A.
Proof.
  intro H; induction H; cbn [extend_code raw_lookup];
    [assumption|rewrite IHLookupGraph; exact H0].
Qed.
Theorem lookup_graph_complete g : forall i A,
  raw_lookup g i = Some A -> LookupGraph g i A.
Proof.
  revert g; fix IH 1; intros g i A H.
  destruct g as [t|h args]; [discriminate|].
  destruct h as [t|h a]; [|discriminate].
  destruct t; try discriminate.
  destruct args as [t|g B]; [discriminate|].
  destruct i; cbn [raw_lookup] in H.
  - apply LookupZero; exact H.
  - destruct (raw_lookup g i) as [C|] eqn:E; cbn [bind] in H; [|discriminate].
    apply LookupSucc with C; [apply IH; exact E|exact H].
Qed.
Theorem lookup_graph_unique g i A B :
  LookupGraph g i A -> LookupGraph g i B -> A = B.
Proof. intros H K; apply lookup_graph_output in H; apply lookup_graph_output in K; congruence. Qed.

Theorem raw_lookup_encode {n} (G : Ctx nat n) (i : Fin n) :
  raw_lookup (encode_ctx G) (fin_number i) = Some (encode_term (G !! i)).
Proof.
  revert i; induction G; intro i; [dependent elimination i|].
  dependent elimination i; cbn [encode_ctx extend_code raw_lookup fin_number index
    ctx_top ctx_pred fin_match].
  - apply raw_shift_encode.
  - rewrite IHG; cbn [bind]; apply raw_shift_encode.
Qed.
Theorem raw_lookup_code_encode {n} (G : Ctx nat n) (i : Fin n) :
  raw_lookup_code (encode_ctx G) (encode_nat (fin_number i)) =
    Some (encode_term (G !! i)).
Proof. unfold raw_lookup_code; rewrite nat_roundtrip; apply raw_lookup_encode. Qed.
Theorem decoded_lookup_exact g n (G : Ctx nat n) k (i : Fin n) :
  decode_ctx g n = Some G -> decode_fin n k = Some i ->
  raw_lookup g k = Some (encode_term (G !! i)).
Proof.
  intros HG Hi; rewrite <- (ctx_decode_encode g n G HG), <- (fin_decode_number n k i Hi).
  apply raw_lookup_encode.
Qed.
Theorem standard_lookup_graph {n} (G : Ctx nat n) (i : Fin n) :
  LookupGraph (encode_ctx G) (fin_number i) (encode_term (G !! i)).
Proof. apply lookup_graph_complete, raw_lookup_encode. Qed.

(** Native certificate-context erasure is explicit, not confused with its
    distinct faithful certificate serialization or claimed to be internal. *)
Definition certificate_context {n} (c : NativeProofCodes.ContextCode n) :=
  encode_ctx (NativeProofCodes.context c).
Theorem certificate_context_extend {n} (c : NativeProofCodes.ContextCode n) r p :
  certificate_context (NativeProofCodes.ExtendContext c r p) =
    extend_code (certificate_context c) (encode_term (NativeProofCodes.subject p)).
Proof. reflexivity. Qed.
Theorem certificate_context_lookup {n} (c : NativeProofCodes.ContextCode n) (i : Fin n) :
  raw_lookup (certificate_context c) (fin_number i) =
    Some (encode_term (NativeProofCodes.context c !! i)).
Proof. apply raw_lookup_encode. Qed.

Example empty_lookup_rejected i : raw_lookup empty_code i = None.
Proof. reflexivity. Qed.

End ContextLookupCodes.
