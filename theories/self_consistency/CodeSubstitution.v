(** Executable capture-avoiding operations on the existing binary codes.
    The algorithms inspect raw fields, including lambda annotations; they do
    not call the intrinsically scoped decoder or assume source typing.
    These are external specifications, not internal PTS inhabitants. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk.SelfConsistency Require Import StructuralCodes.

Definition sort_code r := Pair (Atom TSort) (encode_nat r).
Definition var_code i := Pair (Atom TVar) (encode_nat i).
Definition pi_code A B := Pair (Atom TPi) (Pair A B).
Definition lam_code A b := Pair (Atom TLam) (Pair A b).
Definition app_code f u := Pair (Atom TApp) (Pair f u).

(** Independent local scope clauses. Binary fields are canonical, and both
    binders scope their annotation outside and their body inside the binder. *)
Inductive Scoped : nat -> code -> Prop :=
| scoped_sort n r : Scoped n (sort_code r)
| scoped_var n i : i < n -> Scoped n (var_code i)
| scoped_pi n A B : Scoped n A -> Scoped (S n) B -> Scoped n (pi_code A B)
| scoped_lam n A b : Scoped n A -> Scoped (S n) b -> Scoped n (lam_code A b)
| scoped_app n f u : Scoped n f -> Scoped n u -> Scoped n (app_code f u).

Definition lift_renaming (rho : nat -> nat) (i : nat) : nat :=
  match i with 0 => 0 | S j => S (rho j) end.

Fixpoint raw_rename (rho : nat -> nat) (c : code) : option code :=
  match c with
  | Pair (Atom TSort) r => r <- decode_nat r ;; Some (sort_code r)
  | Pair (Atom TVar) i => i <- decode_nat i ;; Some (var_code (rho i))
  | Pair (Atom TPi) (Pair A B) =>
      A <- raw_rename rho A ;; B <- raw_rename (lift_renaming rho) B ;;
      Some (pi_code A B)
  | Pair (Atom TLam) (Pair A b) =>
      A <- raw_rename rho A ;; b <- raw_rename (lift_renaming rho) b ;;
      Some (lam_code A b)
  | Pair (Atom TApp) (Pair f u) =>
      f <- raw_rename rho f ;; u <- raw_rename rho u ;; Some (app_code f u)
  | _ => None
  end.

Definition lift_replacement (sigma : nat -> option code) (i : nat) : option code :=
  match i with
  | 0 => Some (var_code 0)
  | S j => c <- sigma j ;; raw_rename S c
  end.

Fixpoint raw_replace (sigma : nat -> option code) (c : code) : option code :=
  match c with
  | Pair (Atom TSort) r => r <- decode_nat r ;; Some (sort_code r)
  | Pair (Atom TVar) i => i <- decode_nat i ;; sigma i
  | Pair (Atom TPi) (Pair A B) =>
      A <- raw_replace sigma A ;; B <- raw_replace (lift_replacement sigma) B ;;
      Some (pi_code A B)
  | Pair (Atom TLam) (Pair A b) =>
      A <- raw_replace sigma A ;; b <- raw_replace (lift_replacement sigma) b ;;
      Some (lam_code A b)
  | Pair (Atom TApp) (Pair f u) =>
      f <- raw_replace sigma f ;; u <- raw_replace sigma u ;; Some (app_code f u)
  | _ => None
  end.

Definition substitution_environment (u : code) (i : nat) : option code :=
  match i with 0 => Some u | S j => Some (var_code j) end.
Definition raw_subst (b u : code) : option code :=
  raw_replace (substitution_environment u) b.

Lemma fin_number_bound {n} (i : Fin n) : fin_number i < n.
Proof. induction i; cbn; lia. Qed.

Lemma decode_fin_complete n i : i < n -> exists j, decode_fin n i = Some j.
Proof.
  revert i; induction n; intros i H; [lia|].
  destruct i; cbn; [eexists; reflexivity|].
  destruct (IHn i) as [j E]; [lia|]. rewrite E; eexists; reflexivity.
Qed.

Theorem encoded_scoped {n} (t : Term nat n) : Scoped n (encode_term t).
Proof.
  induction t; cbn [encode_term]; constructor; auto using fin_number_bound.
Qed.

Theorem scoped_decode n c : Scoped n c -> exists t, decode_term c n = Some t.
Proof.
  intro H; induction H; cbn [sort_code var_code pi_code lam_code app_code decode_term].
  - rewrite nat_roundtrip; eexists; reflexivity.
  - rewrite nat_roundtrip; cbn [bind].
    destruct (decode_fin_complete n i H) as [j E]. rewrite E; eexists; reflexivity.
  - destruct IHScoped1 as [A' EA], IHScoped2 as [B' EB].
    rewrite EA; cbn [bind]; rewrite EB; eexists; reflexivity.
  - destruct IHScoped1 as [A' EA], IHScoped2 as [b' Eb].
    rewrite EA; cbn [bind]; rewrite Eb; eexists; reflexivity.
  - destruct IHScoped1 as [f' Ef], IHScoped2 as [u' Eu].
    rewrite Ef; cbn [bind]; rewrite Eu; eexists; reflexivity.
Qed.

Theorem scoped_iff_decode n c :
  Scoped n c <-> exists t, decode_term c n = Some t.
Proof.
  split; [apply scoped_decode|]. intros [t E].
  rewrite <- (term_decode_encode c n t E); apply encoded_scoped.
Qed.

Theorem scoped_iff_encoding n c :
  Scoped n c <-> exists t : Term nat n, encode_term t = c.
Proof.
  split.
  - intro H; destruct (scoped_decode n c H) as [t E].
    exists t; apply term_decode_encode; exact E.
  - intros [t <-]; apply encoded_scoped.
Qed.

Theorem raw_rename_encode {m} (t : Term nat m) :
  forall n (rho : nat -> nat) (f : Fin m -> Fin n),
  (forall i, rho (fin_number i) = fin_number (f i)) ->
  raw_rename rho (encode_term t) = Some (encode_term (rename f t)).
Proof.
  induction t; intros k rho xi H; cbn [encode_term raw_rename rename].
  - rewrite nat_roundtrip; reflexivity.
  - rewrite (IHt1 k rho xi H); cbn [bind].
    rewrite (IHt2 (S k) (lift_renaming rho) (weak xi)); [reflexivity|].
    intro i; dependent elimination i; cbn [lift_renaming fin_number weak fin_match]; auto.
  - rewrite nat_roundtrip; cbn [bind]; rewrite H; reflexivity.
  - rewrite (IHt1 k rho xi H); cbn [bind].
    rewrite (IHt2 (S k) (lift_renaming rho) (weak xi)); [reflexivity|].
    intro i; dependent elimination i; cbn [lift_renaming fin_number weak fin_match]; auto.
  - rewrite (IHt1 k rho xi H); cbn [bind]; rewrite (IHt2 k rho xi H); reflexivity.
Qed.

Theorem raw_shift_encode {n} (t : Term nat n) :
  raw_rename S (encode_term t) = Some (encode_term (shift t)).
Proof. apply raw_rename_encode; intro i; reflexivity. Qed.

Theorem raw_replace_encode {m} (t : Term nat m) :
  forall n (sigma : nat -> option code) (f : Fin m -> Term nat n),
  (forall i, sigma (fin_number i) = Some (encode_term (f i))) ->
  raw_replace sigma (encode_term t) = Some (encode_term (replace f t)).
Proof.
  induction t; intros k sigma xi H; cbn [encode_term raw_replace replace].
  - rewrite nat_roundtrip; reflexivity.
  - rewrite (IHt1 k sigma xi H); cbn [bind].
    rewrite (IHt2 (S k) (lift_replacement sigma) (transpose xi)); [reflexivity|].
    intro i; dependent elimination i; cbn [lift_replacement fin_number transpose fin_match].
    + reflexivity.
    + rewrite H; cbn [bind]; apply raw_shift_encode.
  - rewrite nat_roundtrip; cbn [bind]; apply H.
  - rewrite (IHt1 k sigma xi H); cbn [bind].
    rewrite (IHt2 (S k) (lift_replacement sigma) (transpose xi)); [reflexivity|].
    intro i; dependent elimination i; cbn [lift_replacement fin_number transpose fin_match].
    + reflexivity.
    + rewrite H; cbn [bind]; apply raw_shift_encode.
  - rewrite (IHt1 k sigma xi H); cbn [bind]; rewrite (IHt2 k sigma xi H); reflexivity.
Qed.

Theorem raw_subst_encode {n} (b : Term nat (S n)) (u : Term nat n) :
  raw_subst (encode_term b) (encode_term u) = Some (encode_term (subst b u)).
Proof.
  unfold raw_subst, subst; apply raw_replace_encode.
  intro i; dependent elimination i; reflexivity.
Qed.

Definition renaming_scoped m n (rho : nat -> nat) :=
  forall i, i < m -> rho i < n.
Definition replacement_scoped m n (sigma : nat -> option code) :=
  forall i c, i < m -> sigma i = Some c -> Scoped n c.
Definition replacement_total m (sigma : nat -> option code) :=
  forall i, i < m -> exists c, sigma i = Some c.

Lemma lift_renaming_scoped m n rho : renaming_scoped m n rho ->
  renaming_scoped (S m) (S n) (lift_renaming rho).
Proof. unfold renaming_scoped; intros H [|i] Hi; cbn; [lia|specialize (H i); lia]. Qed.

Theorem raw_rename_scoped m c : Scoped m c ->
  forall n rho, renaming_scoped m n rho ->
  exists d, raw_rename rho c = Some d /\ Scoped n d.
Proof.
  intro H; induction H; intros k rho Hr;
    cbn [sort_code var_code pi_code lam_code app_code raw_rename].
  - rewrite nat_roundtrip; eexists; split; [reflexivity|constructor].
  - rewrite nat_roundtrip; eexists; split; [reflexivity|constructor; auto].
  - destruct (IHScoped1 k rho Hr) as [ra [Ea Ha]].
    destruct (IHScoped2 (S k) (lift_renaming rho) (lift_renaming_scoped n k rho Hr))
      as [rb [Eb Hb]]. rewrite Ea; cbn [bind]; rewrite Eb.
    eexists; split; [reflexivity|constructor; assumption].
  - destruct (IHScoped1 k rho Hr) as [ra [Ea Ha]].
    destruct (IHScoped2 (S k) (lift_renaming rho) (lift_renaming_scoped n k rho Hr))
      as [rb [Eb Hb]]. rewrite Ea; cbn [bind]; rewrite Eb.
    eexists; split; [reflexivity|constructor; assumption].
  - destruct (IHScoped1 k rho Hr) as [ra [Ea Ha]], (IHScoped2 k rho Hr) as [rb [Eb Hb]].
    rewrite Ea; cbn [bind]; rewrite Eb.
    eexists; split; [reflexivity|constructor; assumption].
Qed.

Theorem raw_rename_preserves_scope m n rho c d :
  Scoped m c -> renaming_scoped m n rho -> raw_rename rho c = Some d -> Scoped n d.
Proof.
  intros H Hr E; destruct (raw_rename_scoped m c H n rho Hr) as [d' [E' H']].
  rewrite E in E'; inversion E'; assumption.
Qed.

Lemma lift_replacement_scoped m n sigma : replacement_scoped m n sigma ->
  replacement_scoped (S m) (S n) (lift_replacement sigma).
Proof.
  unfold replacement_scoped; intros H [|i] c Hi E; cbn [lift_replacement] in E.
  - inversion E; constructor; lia.
  - destruct (sigma i) as [d|] eqn:Ed; cbn [bind] in E; [|discriminate].
    eapply (raw_rename_preserves_scope n (S n) S d c);
      [apply (H i d); [lia|exact Ed]| |exact E].
    unfold renaming_scoped; intros; lia.
Qed.

Theorem raw_replace_preserves_scope m c : Scoped m c ->
  forall n sigma d, replacement_scoped m n sigma ->
  raw_replace sigma c = Some d -> Scoped n d.
Proof.
  intro H; induction H; intros k sigma d Hs E;
    cbn [sort_code var_code pi_code lam_code app_code raw_replace] in E.
  - rewrite nat_roundtrip in E; inversion E; constructor.
  - rewrite nat_roundtrip in E; cbn [bind] in E; eapply Hs; eassumption.
  - parse_options E; inversion E; subst; constructor.
    + eapply IHScoped1; eassumption.
    + eapply IHScoped2; [apply lift_replacement_scoped; exact Hs|eassumption].
  - parse_options E; inversion E; subst; constructor.
    + eapply IHScoped1; eassumption.
    + eapply IHScoped2; [apply lift_replacement_scoped; exact Hs|eassumption].
  - parse_options E; inversion E; subst; constructor;
      [eapply IHScoped1|eapply IHScoped2]; eassumption.
Qed.

Lemma lift_replacement_total m n sigma :
  replacement_scoped m n sigma -> replacement_total m sigma ->
  replacement_total (S m) (lift_replacement sigma).
Proof.
  unfold replacement_total; intros Hs H [|i] Hi; cbn [lift_replacement].
  - eexists; reflexivity.
  - destruct (H i) as [c E]; [lia|]. rewrite E; cbn [bind].
    assert (Hc : Scoped n c) by (apply (Hs i c); [lia|exact E]).
    assert (Hr : renaming_scoped n (S n) S) by
      (unfold renaming_scoped; intros; lia).
    destruct (raw_rename_scoped n c Hc (S n) S Hr) as [d [Ed Hd]].
    exists d; exact Ed.
Qed.

Theorem raw_replace_total m c : Scoped m c ->
  forall n sigma, replacement_scoped m n sigma -> replacement_total m sigma ->
  exists d, raw_replace sigma c = Some d.
Proof.
  intro H; induction H; intros k sigma Hs Ht;
    cbn [sort_code var_code pi_code lam_code app_code raw_replace].
  - rewrite nat_roundtrip; eexists; reflexivity.
  - rewrite nat_roundtrip; cbn [bind]; apply Ht; assumption.
  - destruct (IHScoped1 k sigma Hs Ht) as [ra Ea].
    destruct (IHScoped2 (S k) (lift_replacement sigma)
      (lift_replacement_scoped n k sigma Hs) (lift_replacement_total n k sigma Hs Ht)) as [rb Eb].
    rewrite Ea; cbn [bind]; rewrite Eb; eexists; reflexivity.
  - destruct (IHScoped1 k sigma Hs Ht) as [ra Ea].
    destruct (IHScoped2 (S k) (lift_replacement sigma)
      (lift_replacement_scoped n k sigma Hs) (lift_replacement_total n k sigma Hs Ht)) as [rb Eb].
    rewrite Ea; cbn [bind]; rewrite Eb; eexists; reflexivity.
  - destruct (IHScoped1 k sigma Hs Ht) as [ra Ea], (IHScoped2 k sigma Hs Ht) as [rb Eb].
    rewrite Ea; cbn [bind]; rewrite Eb; eexists; reflexivity.
Qed.

Theorem raw_subst_preserves_scope n b u d :
  Scoped (S n) b -> Scoped n u -> raw_subst b u = Some d -> Scoped n d.
Proof.
  intros Hb Hu; apply (raw_replace_preserves_scope (S n) b Hb n).
  unfold replacement_scoped; intros [|i] c Hi E; inversion E; subst; [assumption|].
  constructor; lia.
Qed.

Theorem raw_subst_total n b u : Scoped (S n) b -> Scoped n u ->
  exists d, raw_subst b u = Some d /\ Scoped n d.
Proof.
  intros Hb Hu; destruct (raw_replace_total (S n) b Hb n (substitution_environment u)) as [d E].
  - unfold replacement_scoped; intros [|i] c Hi E; inversion E; subst; [assumption|].
    constructor; lia.
  - unfold replacement_total; intros [|i] Hi; eexists; reflexivity.
  - exists d; split; [exact E|eapply raw_subst_preserves_scope; eassumption].
Qed.

(** A constructor-directed graph, independent of scope and source typing.
    Its variable clause uses the supplied environment, not a semantic test.
    The equivalence below covers arbitrary raw inputs, not only encodings. *)
Inductive Replaced (sigma : nat -> option code) : code -> code -> Prop :=
| replaced_sort r : Replaced sigma (sort_code r) (sort_code r)
| replaced_var i d : sigma i = Some d -> Replaced sigma (var_code i) d
| replaced_pi A B A' B' :
    Replaced sigma A A' -> Replaced (lift_replacement sigma) B B' ->
    Replaced sigma (pi_code A B) (pi_code A' B')
| replaced_lam A b A' b' :
    Replaced sigma A A' -> Replaced (lift_replacement sigma) b b' ->
    Replaced sigma (lam_code A b) (lam_code A' b')
| replaced_app f u f' u' :
    Replaced sigma f f' -> Replaced sigma u u' ->
    Replaced sigma (app_code f u) (app_code f' u').

Theorem replaced_computes sigma c d : Replaced sigma c d -> raw_replace sigma c = Some d.
Proof.
  intro H; induction H;
    cbn [sort_code var_code pi_code lam_code app_code raw_replace].
  - rewrite nat_roundtrip; reflexivity.
  - rewrite nat_roundtrip; exact H.
  - rewrite IHReplaced1; cbn [bind]; rewrite IHReplaced2; reflexivity.
  - rewrite IHReplaced1; cbn [bind]; rewrite IHReplaced2; reflexivity.
  - rewrite IHReplaced1; cbn [bind]; rewrite IHReplaced2; reflexivity.
Qed.

Theorem computes_replaced c : forall sigma d,
  raw_replace sigma c = Some d -> Replaced sigma c d.
Proof.
  revert c; fix IH 1; intros c sigma d H.
  destruct c as [k|h args]; [destruct k; discriminate|].
  destruct h as [k|h a]; [|discriminate].
  destruct k; cbn [raw_replace] in H; try discriminate.
  - parse_options H; inversion H; subst.
    match goal with E : decode_nat ?r = Some ?n |- _ =>
      rewrite <- (nat_decode_encode r n E) end.
    constructor.
  - parse_options H.
    match goal with E : decode_nat ?r = Some ?n |- _ =>
      rewrite <- (nat_decode_encode r n E) end.
    constructor; exact H.
  - destruct args as [k|a b]; [discriminate|].
    cbn [raw_replace] in H; parse_options H; inversion H; subst.
    constructor; eapply IH; eassumption.
  - destruct args as [k|a b]; [discriminate|].
    cbn [raw_replace] in H; parse_options H; inversion H; subst.
    constructor; eapply IH; eassumption.
  - destruct args as [k|a b]; [discriminate|].
    cbn [raw_replace] in H; parse_options H; inversion H; subst.
    constructor; eapply IH; eassumption.
Qed.

Theorem replaced_iff_computes sigma c d :
  Replaced sigma c d <-> raw_replace sigma c = Some d.
Proof. split; [apply replaced_computes|apply computes_replaced]. Qed.

Theorem replaced_preserves_scope m n sigma c d :
  Scoped m c -> replacement_scoped m n sigma -> Replaced sigma c d -> Scoped n d.
Proof.
  intros Hc Hs H; eapply raw_replace_preserves_scope; [exact Hc|exact Hs|].
  apply replaced_computes; exact H.
Qed.

Example substitution_avoids_capture :
  raw_subst (lam_code (sort_code 0) (var_code 1)) (var_code 0) =
  Some (lam_code (sort_code 0) (var_code 1)).
Proof. reflexivity. Qed.

Example substitution_transforms_annotations :
  raw_subst (lam_code (var_code 0) (var_code 0)) (sort_code 2) =
  Some (lam_code (sort_code 2) (var_code 0)).
Proof. reflexivity. Qed.

Example malformed_annotation_rejected :
  raw_subst (lam_code (Atom NZero) (var_code 0)) (sort_code 0) = None.
Proof. reflexivity. Qed.

Example noncanonical_index_rejected :
  raw_subst (Pair (Atom TVar) (Pair (Atom PEven) (Atom NZero))) (sort_code 0) = None.
Proof. reflexivity. Qed.
