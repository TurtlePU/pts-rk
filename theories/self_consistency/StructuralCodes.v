(** One finite-alphabet tree carrier, including binary labels and scope data.
    This is external serialization data, not a new PTS term constructor. *)
From Stdlib Require Import NArith.NArith NArith.Nnat.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.

Inductive tag : Type :=
| NZero | POne | PEven | POdd
| TSort | TVar | TPi | TLam | TApp
| SContract | SPiLeft | SPiRight | SLamLeft | SLamRight | SAppLeft | SAppRight
| ERefl | EReduce | ESym | ETrans
| CSort | CVar | CProduct | CAbstraction | CApplication | CConversion
| GEmpty | GExtend | Input.

Inductive code : Type := Atom : tag -> code | Pair : code -> code -> code.

Fixpoint code_size (c : code) : nat :=
  match c with Atom _ => 1 | Pair a b => S (code_size a + code_size b) end.

Fixpoint encode_positive (p : positive) : code :=
  match p with
  | xH => Atom POne
  | xO p => Pair (Atom PEven) (encode_positive p)
  | xI p => Pair (Atom POdd) (encode_positive p)
  end.
Fixpoint decode_positive (c : code) : option positive :=
  match c with
  | Atom POne => Some xH
  | Pair (Atom PEven) p => option_map xO (decode_positive p)
  | Pair (Atom POdd) p => option_map xI (decode_positive p)
  | _ => None
  end.

Definition encode_nat (n : nat) : code :=
  match N.of_nat n with N0 => Atom NZero | Npos p => encode_positive p end.
Definition decode_nat (c : code) : option nat :=
  match c with
  | Atom NZero => Some 0
  | _ => option_map (fun p => N.to_nat (Npos p)) (decode_positive c)
  end.

Lemma positive_roundtrip p : decode_positive (encode_positive p) = Some p.
Proof. induction p; cbn; try rewrite IHp; reflexivity. Qed.

Lemma positive_has_nonzero_code p : encode_positive p <> Atom NZero.
Proof. destruct p; discriminate. Qed.

Lemma decode_nat_positive p :
  decode_nat (encode_positive p) = Some (N.to_nat (Npos p)).
Proof.
  destruct p; cbn [encode_positive decode_nat decode_positive];
    try rewrite positive_roundtrip; reflexivity.
Qed.

Theorem nat_roundtrip n : decode_nat (encode_nat n) = Some n.
Proof.
  unfold encode_nat; pose proof (Nat2N.id n) as E.
  destruct (N.of_nat n) as [|p] eqn:H; [cbn in E; subst; reflexivity |].
  rewrite decode_nat_positive; f_equal; exact E.
Qed.

Theorem positive_decode_encode c p : decode_positive c = Some p -> encode_positive p = c.
Proof.
  revert p; induction c as [t|h IHh a IHa]; intros p H.
  - destruct t; cbn in H; try discriminate; inversion H; reflexivity.
  - destruct h as [t|h b]; [|discriminate].
    destruct t; cbn [decode_positive] in H; try discriminate;
      destruct (decode_positive a) as [q|] eqn:E; cbn in H; try discriminate;
      inversion H; subst; cbn [encode_positive]; f_equal; auto.
Qed.

Theorem nat_decode_encode c n : decode_nat c = Some n -> encode_nat n = c.
Proof.
  destruct c as [t|h a]; intro H.
  - destruct t; cbn in H; try discriminate; inversion H; reflexivity.
  - change (option_map (fun p => N.to_nat (Npos p)) (decode_positive (Pair h a)) = Some n) in H.
    destruct (decode_positive (Pair h a)) as [p|] eqn:E; cbn [option_map] in H;
      [|discriminate].
    inversion H; subst.
    change (encode_nat (N.to_nat (Npos p)) = Pair h a).
    unfold encode_nat; rewrite N2Nat.id.
    apply positive_decode_encode; exact E.
Qed.

Fixpoint fin_number {n} (i : Fin n) : nat :=
  match i with fzero => 0 | fsucc i => S (fin_number i) end.
Fixpoint decode_fin (n k : nat) : option (Fin n) :=
  match n with
  | 0 => None
  | S n => match k with 0 => Some fzero | S k => option_map fsucc (decode_fin n k) end
  end.

Theorem fin_roundtrip {n} (i : Fin n) : decode_fin n (fin_number i) = Some i.
Proof. induction i; cbn; try rewrite IHi; reflexivity. Qed.

Lemma fin_decode_number n k (i : Fin n) : decode_fin n k = Some i -> fin_number i = k.
Proof.
  revert k i; induction n; intros k i H; [discriminate |].
  destruct k; cbn in H.
  - inversion H; reflexivity.
  - destruct (decode_fin n k) as [j|] eqn:E; cbn in H; [|discriminate].
    inversion H; cbn; f_equal; eapply IHn; exact E.
Qed.

Definition bind {A B : Type} (x : option A) (f : A -> option B) : option B :=
  match x with Some a => f a | None => None end.
Notation "x <- a ;; b" := (bind a (fun x => b))
  (at level 100, a at next level, right associativity).

Fixpoint encode_term {n} (t : Term nat n) : code :=
  match t with
  | 𝓤 r => Pair (Atom TSort) (encode_nat r)
  | var i => Pair (Atom TVar) (encode_nat (fin_number i))
  | Π A B => Pair (Atom TPi) (Pair (encode_term A) (encode_term B))
  | lam A b => Pair (Atom TLam) (Pair (encode_term A) (encode_term b))
  | app f u => Pair (Atom TApp) (Pair (encode_term f) (encode_term u))
  end.

Fixpoint decode_term (c : code) (n : nat) : option (Term nat n) :=
  match c with
  | Pair (Atom TSort) r => r <- decode_nat r ;; Some (𝓤 r)
  | Pair (Atom TVar) i => k <- decode_nat i ;; i <- decode_fin n k ;; Some (var i)
  | Pair (Atom TPi) (Pair A B) =>
      A <- decode_term A n ;; B <- decode_term B (S n) ;; Some (Π A B)
  | Pair (Atom TLam) (Pair A b) =>
      A <- decode_term A n ;; b <- decode_term b (S n) ;; Some (lam A b)
  | Pair (Atom TApp) (Pair f u) =>
      f <- decode_term f n ;; u <- decode_term u n ;; Some (app f u)
  | _ => None
  end.

Theorem term_roundtrip {n} (t : Term nat n) : decode_term (encode_term t) n = Some t.
Proof.
  induction t; cbn [encode_term decode_term];
    try rewrite nat_roundtrip; try rewrite IHt1; try rewrite IHt2;
    cbn [bind]; try rewrite fin_roundtrip; reflexivity.
Qed.

Theorem encode_term_injective {n} (t u : Term nat n) : encode_term t = encode_term u -> t = u.
Proof.
  intro E; pose proof (term_roundtrip t) as H; rewrite E, term_roundtrip in H; congruence.
Qed.

(** Parser proofs inspect every branch and every field. A successful parser
    is a partial inverse, not a normalizer or a repair procedure. *)
Ltac parse_options H :=
  repeat match type of H with
  | context [bind ?v ?f] =>
      let E := fresh "E" in destruct v eqn:E; cbn [bind] in H; try discriminate
  end.

Theorem term_decode_encode c : forall n (t : Term nat n),
  decode_term c n = Some t -> encode_term t = c.
Proof.
  revert c; fix IH 1; intros c n t H.
  destruct c as [k|h args]; [destruct k; discriminate |].
  destruct h as [k|h a]; [|discriminate].
  destruct k; cbn [decode_term] in H; try discriminate.
  - parse_options H; inversion H; subst; cbn [encode_term].
    f_equal; eapply nat_decode_encode; eassumption.
  - parse_options H; inversion H; subst; cbn [encode_term].
    f_equal; match goal with E : decode_fin _ _ = Some _ |- _ =>
      rewrite (fin_decode_number _ _ _ E) end.
    eapply nat_decode_encode; eassumption.
  - destruct args as [k|a b]; [discriminate |];
    cbn [decode_term] in H; parse_options H; inversion H; subst;
    cbn [encode_term]; f_equal; f_equal; eapply IH; eassumption.
  - destruct args as [k|a b]; [discriminate |];
    cbn [decode_term] in H; parse_options H; inversion H; subst;
    cbn [encode_term]; f_equal; f_equal; eapply IH; eassumption.
  - destruct args as [k|a b]; [discriminate |];
    cbn [decode_term] in H; parse_options H; inversion H; subst;
    cbn [encode_term]; f_equal; f_equal; eapply IH; eassumption.
Qed.

Example out_of_scope_rejected :
  decode_term (Pair (Atom TVar) (encode_nat 1)) 1 = None.
Proof. reflexivity. Qed.
Example missing_annotation_rejected :
  decode_term (Pair (Atom TLam) (Atom NZero)) 0 = None.
Proof. reflexivity. Qed.
Example noncanonical_zero_rejected : decode_nat (Pair (Atom PEven) (Atom NZero)) = None.
Proof. reflexivity. Qed.
