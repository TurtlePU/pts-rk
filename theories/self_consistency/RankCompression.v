(** Finite-support compression counts distinct labels below a label.
    Successor is preserved only at adjacent labels actually in the support. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Arith.Compare_dec Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From PTSrk.SelfConsistency Require Import NativeProofCodes CertificateAdequacy SortRenaming.
Import ListNotations.
Import NativeProofCodes.NativeProofCodes.

Definition compress (support : list nat) (x : nat) : nat :=
  length (filter (fun y => y <? x) (nodup Nat.eq_dec support)).

Lemma compress_zero support : compress support 0 = 0.
Proof.
  unfold compress; induction (nodup Nat.eq_dec support); cbn; auto.
Qed.

Fixpoint term_labels {n} (t : Term nat n) : list nat :=
  match t with
  | 𝓤 r => [r] | var _ => []
  | Π A B | lam A B | app A B => term_labels A ++ term_labels B
  end.

Fixpoint context_labels {n} (G : Ctx nat n) : list nat :=
  match G with ε => [] | G & A => context_labels G ++ term_labels A end.

Fixpoint step_labels {n} (p : StepCode n) : list nat :=
  match p with
  | Contract A b u => term_labels A ++ term_labels b ++ term_labels u
  | PiLeft p B | LamLeft p B | AppLeft p B => step_labels p ++ term_labels B
  | PiRight A p | LamRight A p | AppRight A p => term_labels A ++ step_labels p
  end.

Fixpoint equality_labels {n} (p : EqualityCode n) : list nat :=
  match p with
  | Refl t => term_labels t | Reduce p => step_labels p
  | Symmetry p => equality_labels p
  | Transitivity p q => equality_labels p ++ equality_labels q
  end.

(** Every written term/annotation/rank/equality instruction is traversed;
    a product's computed result is included explicitly. No sharing discount. *)
Fixpoint certificate_labels {n} (p : Certificate n) : list nat :=
  match p with
  | SortRule r => [r; 0]
  | VariableRule i A => term_labels A
  | ProductRule A B a b p q => [a; b; Nat.max (S a) b] ++
      term_labels A ++ term_labels B ++ certificate_labels p ++ certificate_labels q
  | AbstractionRule A t B r p q => r ::
      (term_labels A ++ term_labels t ++ term_labels B ++ certificate_labels p ++ certificate_labels q)
  | ApplicationRule f u A B p q => term_labels f ++ term_labels u ++ term_labels A ++
      term_labels B ++ certificate_labels p ++ certificate_labels q
  | ConversionRule t A B r p q e => r ::
      (term_labels t ++ term_labels A ++ term_labels B ++ certificate_labels p ++
       certificate_labels q ++ equality_labels e)
  end.

Definition complete_support {n} (G : Ctx nat n) (p : Certificate n) : list nat :=
  0 :: 1 :: (context_labels G ++ certificate_labels p).

Lemma count_below_succ labels x :
  length (filter (fun y => y <? S x) labels) =
  length (filter (fun y => y <? x) labels) + count_occ Nat.eq_dec labels x.
Proof.
  induction labels as [|a labels IH]; cbn [filter length count_occ]; [reflexivity |].
  destruct (Nat.eq_dec a x); destruct (Nat.eq_dec x a); destruct (a <? S x) eqn:E1;
    destruct (a <? x) eqn:E2; cbn [length];
    repeat match goal with
    | H : (_ <? _) = true |- _ => apply Nat.ltb_lt in H
    | H : (_ <? _) = false |- _ => apply Nat.ltb_ge in H
    end; lia.
Qed.

Theorem compress_successor support x : In x support ->
  compress support (S x) = S (compress support x).
Proof.
  intro H; unfold compress; rewrite count_below_succ.
  assert (E : count_occ Nat.eq_dec (nodup Nat.eq_dec support) x = 1).
  { apply (proj1 (NoDup_count_occ' Nat.eq_dec _) (NoDup_nodup _ _)).
    apply nodup_In; exact H. }
  lia.
Qed.

Theorem compress_monotone support x y : x <= y -> compress support x <= compress support y.
Proof.
  intro H; induction H; [reflexivity |].
  unfold compress in *; rewrite count_below_succ; lia.
Qed.

Theorem compress_strict support x y : In x support -> x < y ->
  compress support x < compress support y.
Proof.
  intros H E; pose proof (compress_monotone support (S x) y E).
  rewrite compress_successor in H0 by exact H; lia.
Qed.

Theorem compress_product support a b : In a support ->
  compress support (Nat.max (S a) b) =
  Nat.max (S (compress support a)) (compress support b).
Proof.
  intro H; destruct (le_dec (S a) b).
  - rewrite Nat.max_r by assumption.
    rewrite Nat.max_r; [reflexivity |].
    pose proof (compress_strict support a b H l); lia.
  - rewrite Nat.max_l by lia; rewrite compress_successor by assumption.
    symmetry; apply Nat.max_l.
    pose proof (compress_monotone support b (S a) ltac:(lia)).
    rewrite compress_successor in H0 by assumption; exact H0.
Qed.

Corollary compress_one support : In 0 support -> compress support 1 = 1.
Proof. intro H; rewrite compress_successor by exact H; rewrite compress_zero; reflexivity. Qed.

Lemma compress_bound support x : compress support x <= length support.
Proof.
  unfold compress; apply Nat.le_trans with (m := length (nodup Nat.eq_dec support)).
  - generalize (nodup Nat.eq_dec support); intro labels.
    induction labels as [|a labels IH]; cbn [filter length]; [lia |].
    destruct (a <? x); cbn [length]; lia.
  - induction support; cbn; auto.
    destruct (in_dec Nat.eq_dec a support); cbn; lia.
Qed.

Theorem compression_respects_products {n} (p : Certificate n) :
  forall support, incl (certificate_labels p) support ->
  products_respected (compress support) p.
Proof.
  induction p; intros support H; cbn [products_respected]; try exact I.
  all: repeat split.
  all: try (apply compress_product; apply H; cbn [certificate_labels List.app In]; auto).
  all: first [apply IHp1 | apply IHp2]; intros x Hx; apply H;
    cbn [certificate_labels List.app In]; repeat rewrite in_app_iff; tauto.
Qed.

Theorem compressed_certificate_checked {n} (G : Ctx nat n) (p : Certificate n) :
  check G p = true ->
  check (relabel_context (compress (complete_support G p)) G)
    (relabel_certificate (compress (complete_support G p)) p) = true.
Proof.
  apply relabel_certificate_check; [apply compress_zero |].
  apply compression_respects_products; intros x Hx.
  unfold complete_support; cbn; right; right; apply in_app_iff; auto.
Qed.

Theorem compressed_original_typing {n} (G : Ctx nat n) (p : Certificate n) :
  check G p = true ->
  @typ nat RankSorts n (relabel_context (compress (complete_support G p)) G)
    (relabel (compress (complete_support G p)) (subject p))
    (relabel (compress (complete_support G p)) (type p)).
Proof.
  intro H; pose proof (certificate_sound _ _ (compressed_certificate_checked G p H)) as T.
  rewrite relabel_subject, relabel_type in T; try exact T; [apply compress_zero |].
  apply compression_respects_products; intros x Hx.
  unfold complete_support; cbn; right; right; apply in_app_iff; auto.
Qed.

Corollary compressed_label_bound {n} (G : Ctx nat n) (p : Certificate n) x :
  compress (complete_support G p) x <=
    2 + length (context_labels G) + length (certificate_labels p).
Proof.
  pose proof (compress_bound (complete_support G p) x).
  unfold complete_support in H; cbn [length] in H; rewrite length_app in H.
  change (compress (complete_support G p) x <=
    S (S (length (context_labels G) + length (certificate_labels p)))).
  exact H.
Qed.

Corollary compression_fixes_bottom {n} (G : Ctx nat n) (p : Certificate n) :
  relabel (compress (complete_support G p)) Bottom = Bottom.
Proof. apply relabel_bottom, compress_zero. Qed.

Corollary compression_preserves_bottom_acceptance (p : Certificate 0) :
  accepts_bottom p = true ->
  accepts_bottom (relabel_certificate (compress (complete_support ε p)) p) = true.
Proof.
  unfold accepts_bottom; rewrite !Bool.andb_true_iff.
  intros [H E]; split; [exact (compressed_certificate_checked ε p H) |].
  apply term_eqb_correct in E; apply term_eqb_correct.
  rewrite relabel_type; [rewrite E; apply compression_fixes_bottom | apply compress_zero |].
  apply compression_respects_products; intros x Hx; unfold complete_support; cbn; auto.
Qed.

Fixpoint term_nodes {n} (t : Term nat n) : nat :=
  match t with
  | 𝓤 _ | var _ => 1
  | Π A B | lam A B | app A B => S (term_nodes A + term_nodes B)
  end.

Theorem relabel_preserves_nodes rho {n} (t : Term nat n) :
  term_nodes (relabel rho t) = term_nodes t.
Proof. induction t; cbn; congruence. Qed.

Theorem compress_injective_on_support support x y :
  In x support -> In y support -> compress support x = compress support y -> x = y.
Proof.
  intros Hx Hy E; destruct (Nat.lt_trichotomy x y) as [H|[H|H]]; auto;
    [pose proof (compress_strict support x y Hx H) |
     pose proof (compress_strict support y x Hy H)]; lia.
Qed.

Example sparse_labels_compress : compress [0; 1; 100; 101; 500] 500 = 4.
Proof. vm_compute; reflexivity. Qed.

Example used_product_compresses :
  compress [0; 1; 100; 101; 500] (Nat.max 101 1) =
  Nat.max (S (compress [0; 1; 100; 101; 500] 100))
    (compress [0; 1; 100; 101; 500] 1).
Proof. apply compress_product; cbn; auto. Qed.

(** Include the proofs justifying every context declaration, not merely the
    declaration terms. This is the support for a complete contextual input. *)
Fixpoint context_code_labels {n} (c : ContextCode n) : list nat :=
  match c with
  | EmptyContext => []
  | ExtendContext c r p => r :: (context_code_labels c ++ certificate_labels p)
  end.

Definition input_support {n} (c : ContextCode n) (p : Certificate n) :=
  0 :: 1 :: (context_code_labels c ++ certificate_labels p).

Lemma compression_respects_context {n} (c : ContextCode n) support :
  incl (context_code_labels c) support -> context_products_respected (compress support) c.
Proof.
  induction c; intro H; cbn [context_products_respected]; [exact I |].
  split; [apply IHc | apply compression_respects_products]; intros x Hx;
    apply H; cbn [context_code_labels In]; right; apply in_app_iff; auto.
Qed.

Theorem compressed_input_checked {n} (c : ContextCode n) (p : Certificate n) :
  context_check c = true -> check (context c) p = true ->
  let rho := compress (input_support c p) in
  context_check (relabel_context_code rho c) = true /\
  check (context (relabel_context_code rho c)) (relabel_certificate rho p) = true.
Proof.
  intros C P rho; split.
  - apply relabel_context_check; [apply compress_zero | | exact C].
    apply compression_respects_context; intros x Hx.
    unfold input_support; cbn [In]; right; right; apply in_app_iff; auto.
  - rewrite relabel_context_code_decode; apply relabel_certificate_check;
      [apply compress_zero | | exact P].
    apply compression_respects_products; intros x Hx.
    unfold input_support; cbn [In]; right; right; apply in_app_iff; auto.
Qed.

Corollary compressed_input_original_typing {n} (c : ContextCode n) (p : Certificate n) :
  context_check c = true -> check (context c) p = true ->
  let rho := compress (input_support c p) in
  @typ nat RankSorts n (relabel_context rho (context c))
    (relabel rho (subject p)) (relabel rho (type p)).
Proof.
  intros C P rho; pose proof (proj2 (compressed_input_checked c p C P)) as H.
  apply certificate_sound in H; rewrite relabel_context_code_decode, relabel_subject in H.
  rewrite relabel_type in H; try exact H; [apply compress_zero |].
  apply compression_respects_products; intros x Hx; unfold input_support;
    cbn [In]; right; right; apply in_app_iff; auto.
Qed.

Corollary input_compressed_label_bound {n} (c : ContextCode n) (p : Certificate n) x :
  compress (input_support c p) x <=
    2 + length (context_code_labels c) + length (certificate_labels p).
Proof.
  pose proof (compress_bound (input_support c p) x) as H.
  unfold input_support in H; cbn [length] in H; rewrite length_app in H.
  exact H.
Qed.

Theorem every_original_judgment_compresses {n} (G : Ctx nat n) t A :
  @Preservation.wf nat RankSorts n G -> @typ nat RankSorts n G t A ->
  exists c p, context c = G /\ context_check c = true /\
    check G p = true /\ matches p t A /\
    @typ nat RankSorts n (relabel_context (compress (input_support c p)) G)
      (relabel (compress (input_support c p)) t)
      (relabel (compress (input_support c p)) A).
Proof.
  intros W T; destruct (context_code_complete G W) as [c [Ec C]].
  destruct (certificate_complete G t A T) as [p [P M]].
  exists c, p; repeat split; try assumption; try exact (proj1 M); try exact (proj2 M).
  pose proof (compressed_input_original_typing c p C ltac:(rewrite Ec; exact P)) as H.
  rewrite Ec, (proj1 M), (proj2 M) in H; exact H.
Qed.
