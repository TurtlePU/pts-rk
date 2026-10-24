(** Finite fragments of the COMPLETE raw serialization alphabet.

    Admission depends only on tree size.  It does not inspect a parser,
    checker, typing derivation, or normalization result; malformed codes are
    included.  This is an executable external family of finite domains, not
    an internal quantification over all represented budgets. *)
From Stdlib Require Import List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk.SelfConsistency Require Import StructuralCodes.
Import ListNotations.

Definition tags : list tag :=
  [NZero; POne; PEven; POdd;
   TSort; TVar; TPi; TLam; TApp;
   SContract; SPiLeft; SPiRight; SLamLeft; SLamRight; SAppLeft; SAppRight;
   ERefl; EReduce; ESym; ETrans;
   CSort; CVar; CProduct; CAbstraction; CApplication; CConversion;
   GEmpty; GExtend; Input].

Theorem tags_length : length tags = 29.
Proof. reflexivity. Qed.

Theorem tags_complete t : In t tags.
Proof. destruct t; cbn; tauto. Qed.

Definition code_eq_dec : forall a b : code, {a = b} + {a <> b}.
Proof. decide equality; decide equality. Defined.

Lemma code_size_positive c : 1 <= code_size c.
Proof. destruct c; cbn; lia. Qed.

Definition pairs (xs : list code) : list code :=
  flat_map (fun a => map (Pair a) xs) xs.

Lemma pairs_spec xs c :
  In c (pairs xs) <-> exists a b, In a xs /\ In b xs /\ c = Pair a b.
Proof.
  unfold pairs; rewrite in_flat_map; split.
  - intros [a [Ha Hc]]. apply in_map_iff in Hc.
    destruct Hc as [b [E Hb]]. exists a, b; auto.
  - intros [a [b [Ha [Hb E]]]]. subst c.
    exists a; split; [exact Ha | apply in_map; exact Hb].
Qed.

(** Only the immediately preceding domain is reused.  The size filter
    removes precisely the pairs exceeding the new budget. *)
Fixpoint codes (budget : nat) : list code :=
  match budget with
  | 0 => []
  | S b => map Atom tags ++
      filter (fun c => Nat.leb (code_size c) (S b)) (pairs (codes b))
  end.

Theorem codes_spec budget c : In c (codes budget) <-> code_size c <= budget.
Proof.
  revert c; induction budget as [|b IH]; intro c.
  - change (False <-> code_size c <= 0).
    pose proof (code_size_positive c); lia.
  - cbn [codes]; rewrite in_app_iff, filter_In, Nat.leb_le.
    split.
    + intros [H | [_ H]]; [|exact H].
      apply in_map_iff in H; destruct H as [t [E _]]; subst c; cbn; lia.
    + intro H; destruct c as [t|a d].
      * left; apply in_map; apply tags_complete.
      * right; split; [|exact H]. apply pairs_spec.
        exists a, d; repeat split; try reflexivity; apply IH;
          pose proof (code_size_positive a);
          pose proof (code_size_positive d); cbn in H; lia.
Qed.

Theorem codes_monotone b d c :
  b <= d -> In c (codes b) -> In c (codes d).
Proof. rewrite !codes_spec; lia. Qed.

Theorem code_covered c : In c (codes (code_size c)).
Proof. apply codes_spec; reflexivity. Qed.

Theorem codes_nonempty b : codes (S b) <> [].
Proof. cbn [codes tags]; discriminate. Qed.

Lemma fin_number_bound {n} (i : Fin n) : fin_number i < n.
Proof. induction i; cbn; lia. Qed.

(** Lookup is total only at its genuine finite index.  The [nth] default
    is never reached, as [lookup_in] proves. *)
Definition lookup (xs : list code) (i : Fin (length xs)) : code :=
  nth (fin_number i) xs (Atom NZero).

Theorem lookup_in xs i : In (lookup xs i) xs.
Proof. unfold lookup; apply nth_In; apply fin_number_bound. Qed.

Fixpoint locate (c : code) (xs : list code) : option (Fin (length xs)) :=
  match xs as ys return option (Fin (length ys)) with
  | [] => None
  | x :: ys =>
      if code_eq_dec c x then Some fzero
      else option_map fsucc (locate c ys)
  end.

Theorem locate_sound c xs i : locate c xs = Some i -> lookup xs i = c.
Proof.
  revert i; induction xs as [|x xs IH]; intros i H; [discriminate |].
  cbn [locate] in H. destruct (code_eq_dec c x) as [E|E].
  - inversion H; subst; reflexivity.
  - destruct (locate c xs) as [j|] eqn:Ej; cbn in H; [|discriminate].
    inversion H; subst i; unfold lookup; cbn [fin_number nth].
    apply IH; reflexivity.
Qed.

Theorem locate_complete c xs :
  In c xs -> exists i, locate c xs = Some i.
Proof.
  induction xs as [|x xs IH]; intro H; [contradiction |].
  cbn [locate]. destruct (code_eq_dec c x) as [E|E].
  - exists fzero; reflexivity.
  - destruct H as [H|H]; [congruence |].
    destruct (IH H) as [i Hi]. rewrite Hi; exists (fsucc i); reflexivity.
Qed.

Theorem locate_none c xs : locate c xs = None <-> ~ In c xs.
Proof.
  split.
  - intros H Hin; destruct (locate_complete c xs Hin) as [i Hi]; congruence.
  - intro H; destruct (locate c xs) as [i|] eqn:Hi; [|reflexivity].
    exfalso; apply H; rewrite <- (locate_sound c xs i Hi); apply lookup_in.
Qed.

Definition fragment_index budget c := locate c (codes budget).
Definition fragment_decode budget := lookup (codes budget).

Theorem fragment_decode_bound budget i :
  code_size (fragment_decode budget i) <= budget.
Proof. apply codes_spec; apply lookup_in. Qed.

Theorem fragment_index_complete budget c :
  code_size c <= budget -> exists i, fragment_index budget c = Some i.
Proof. intro H; apply locate_complete; apply codes_spec; exact H. Qed.

Theorem fragment_index_roundtrip budget c i :
  fragment_index budget c = Some i -> fragment_decode budget i = c.
Proof. apply locate_sound. Qed.

Theorem fragment_index_none budget c :
  fragment_index budget c = None <-> budget < code_size c.
Proof. unfold fragment_index; rewrite locate_none, codes_spec; lia. Qed.

Theorem fragment_index_injective budget c d i :
  fragment_index budget c = Some i ->
  fragment_index budget d = Some i -> c = d.
Proof.
  intros Hc Hd; pose proof (fragment_index_roundtrip budget c i Hc).
  pose proof (fragment_index_roundtrip budget d i Hd); congruence.
Qed.

Theorem bounded_index_injective budget c d :
  code_size c <= budget -> code_size d <= budget ->
  fragment_index budget c = fragment_index budget d -> c = d.
Proof.
  intros Hc _ E; destruct (fragment_index_complete budget c Hc) as [i Hi].
  eapply fragment_index_injective; [exact Hi | rewrite <- E; exact Hi].
Qed.

(** A reusable coverage endpoint for ANY complete serialization, independently
    of the particular constructor or acceptance status of its input. *)
Theorem serialized_input_covered {A : Type} (serialize : A -> code) (a : A) :
  exists i, fragment_index (code_size (serialize a)) (serialize a) = Some i /\
    fragment_decode (code_size (serialize a)) i = serialize a.
Proof.
  destruct (fragment_index_complete (code_size (serialize a)) (serialize a)
    (Nat.le_refl _)) as [i Hi].
  exists i; split; [exact Hi | now apply fragment_index_roundtrip].
Qed.
