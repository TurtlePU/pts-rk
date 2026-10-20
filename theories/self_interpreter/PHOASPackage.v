From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks Reduction
  AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import STLCEmbedding Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import PHOASAlgebra PHOASTelescope PHOASFaithful
  PHOASRecovery RankedQuotation.
Import Context ChurchSTLC ListNotations.

Module PHOASPackage.
Module PA := PHOASAlgebra.PHOASAlgebra.
Module PT := PHOASTelescope.PHOASTelescope.
Module TH := TypedHOAS.TypedHOAS.
Module BP := BrownPalsberg.BrownPalsberg.
Module EQ := ExecutableQuotation.ExecutableQuotation.
Module RQ := RankedQuotation.RankedQuotation.
Module PF := PHOASFaithful.PHOASFaithful.
Module PR := PHOASRecovery.PHOASRecovery.

(** Families occupy a finite descending-rank telescope. The later handler
    telescope has only finite rank-pair descriptors, not one entry for each
    simple type shape. All definitions below compute ORIGINAL PTS syntax. *)
Fixpoint family_context count start {n} (G : Ctx nat n) : Ctx nat (count+n) :=
  match count with
  | 0 => G
  | S c => family_context c (S start) G & BP.family_type start start
  end.

Lemma family_context_wf count : forall start n (G : Ctx nat n),
  @wf nat RankSorts n G -> @wf nat RankSorts (count+n) (family_context count start G).
Proof.
  induction count; intros; cbn [family_context]; [assumption |].
  eapply wf_cons; [apply IHcount; assumption | apply BP.family_type_sort].
Qed.

Lemma family_context_normal count : forall start n (G : Ctx nat n),
  PT.normal_context G = true -> PT.normal_context (family_context count start G) = true.
Proof.
  induction count; intros; cbn [family_context PT.normal_context BP.family_type normalb];
    [assumption | rewrite IHcount by assumption; reflexivity].
Qed.

Lemma family_source_typing count : forall start n (G : Ctx nat n) t T,
  @typ nat RankSorts n G t T ->
  @typ nat RankSorts (count+n) (family_context count start G) (rename up t) (rename up T).
Proof.
  induction count; intros; cbn [family_context].
  - cbn [up]; rewrite !rename_id; assumption.
  - rewrite <- !shift_up. apply weakening, IHcount; assumption.
Qed.

Lemma family_slot_typing count : forall start n (G : Ctx nat n) r o,
  r < count ->
  @typ nat RankSorts (count+n) (family_context count start G)
    (var (RQ.slot count r o)) (BP.family_type (start+r) (start+r)).
Proof.
  induction count; intros start n G r o Hr; [lia |].
  destruct r; cbn [family_context RQ.slot].
  - rewrite Nat.add_0_r.
    change (typ (family_context count (S start) G & BP.family_type start start)
      (var fzero) ((family_context count (S start) G & BP.family_type start start) !! fzero)).
    constructor.
  - replace (start + S r) with (S start+r) by lia.
    change (typ (family_context count (S start) G & BP.family_type start start)
      (shift (var (RQ.slot count r o))) (shift (BP.family_type (S start+r) (S start+r)))).
    apply weakening, IHcount; lia.
Qed.

Inductive Handler : Type := Abs (a b : nat) | App (a b : nat).
Definition handler_eq_dec (x y : Handler) : {x=y}+{x<>y}.
Proof. decide equality; apply Nat.eq_dec. Defined.
Definition handler_rank h := match h with Abs a b | App a b => Nat.max (S a) b end.

Definition signature {n} (F : nat -> Term nat n) h : Term nat n :=
  match h with
  | Abs a b => BP.indexed_abs_type a b (F a) (F b) (F (Nat.max (S a) b))
  | App a b => BP.indexed_app_type a b (F a) (F b) (F (Nat.max (S a) b))
  end.
Definition handler_value {n} h : Term nat n :=
  match h with Abs a b => BP.abs_identity a b | App a b => BP.app_identity a b end.

Lemma signature_rename m n (rho : Fin m -> Fin n) F h :
  rename rho (signature F h) = signature (fun r => rename rho (F r)) h.
Proof.
  destruct h; unfold signature, BP.indexed_abs_type, BP.indexed_app_type,
    BP.abs_case_type, BP.app_case_type, BP.arr; syntax_simp.
Qed.

Lemma signature_sort n (G : Ctx nat n) F h :
  (forall r, r <= handler_rank h -> typ G (F r) (BP.family_type r r)) ->
  @typ nat RankSorts n G (signature F h) (𝓤 (S (handler_rank h))).
Proof.
  destruct h as [a b|a b]; intro HF; cbn [signature handler_rank] in *.
  - apply (proj1 (BP.indexed_handler_type_sorts a b n G _ _ _
      (HF a ltac:(lia)) (HF b ltac:(lia)) (HF (Nat.max (S a) b) ltac:(lia)))).
  - apply (proj2 (BP.indexed_handler_type_sorts a b n G _ _ _
      (HF a ltac:(lia)) (HF b ltac:(lia)) (HF (Nat.max (S a) b) ltac:(lia)))).
Qed.

Lemma signature_normal n (F : nat -> Fin n) h :
  normalb (signature (fun r => var (F r)) h) = true.
Proof.
  destruct h; reflexivity.
Qed.

Lemma handler_value_typed n (G : Ctx nat n) h :
  @typ nat RankSorts n G (handler_value h) (signature (fun r => BP.type_identity r) h).
Proof.
  destruct h as [a b|a b]; [apply (proj1 (BP.indexed_identity_handlers_typing a b n G)) |
    apply (proj2 (BP.indexed_identity_handlers_typing a b n G))].
Qed.

Fixpoint handler_context (hs : list Handler) {n} (G : Ctx nat n) F
    : Ctx nat (length hs+n) :=
  match hs with
  | [] => G
  | h::rest => handler_context rest G F & rename (@up (length rest) n) (signature F h)
  end.

Fixpoint handler_slot (hs : list Handler) (h : Handler) {n} (o : Fin n)
    : Fin (length hs+n) :=
  match hs with
  | [] => o
  | x::rest => if handler_eq_dec h x then fzero else fsucc (handler_slot rest h o)
  end.

Lemma handler_source_typing hs : forall n (G : Ctx nat n) F t T,
  @typ nat RankSorts n G t T ->
  @typ nat RankSorts (length hs+n) (handler_context hs G F) (rename up t) (rename up T).
Proof.
  induction hs; intros; cbn [handler_context length].
  - cbn [up]; rewrite !rename_id; assumption.
  - rewrite <- !shift_up. apply weakening, IHhs; assumption.
Qed.

Lemma handler_slot_typing hs : forall n (G : Ctx nat n) F h o,
  In h hs ->
  @typ nat RankSorts (length hs+n) (handler_context hs G F)
    (var (handler_slot hs h o)) (rename up (signature F h)).
Proof.
  induction hs; intros n G F h o Hin; [contradiction |].
  cbn [handler_context handler_slot length]. destruct (handler_eq_dec h a) as [->|Hneq].
  - rewrite <- shift_up.
    change (typ (handler_context hs G F & rename up (signature F a)) (var fzero)
      ((handler_context hs G F & rename up (signature F a)) !! fzero)). constructor.
  - rewrite <- shift_up.
    change (typ (handler_context hs G F & rename up (signature F a))
      (shift (var (handler_slot hs h o))) (shift (rename up (signature F h)))).
    apply weakening, IHhs. destruct Hin; [congruence | assumption].
Qed.

Lemma handler_context_wf hs : forall n (G : Ctx nat n) F,
  @wf nat RankSorts n G ->
  (forall h, In h hs -> @typ nat RankSorts n G (signature F h) (𝓤 (S (handler_rank h)))) ->
  @wf nat RankSorts (length hs+n) (handler_context hs G F).
Proof.
  induction hs; intros n G F HG HT; cbn [handler_context length]; [exact HG |].
  pose proof (HT a (or_introl eq_refl)) as Hr.
  eapply wf_cons with (ℓ := S (handler_rank a));
    [apply IHhs; [exact HG | intros; apply HT; now right] |].
  change (typ (handler_context hs G F) (rename up (signature F a))
    (rename up (𝓤 (S (handler_rank a))))).
  apply handler_source_typing; exact Hr.
Qed.

Lemma handler_context_normal hs : forall n (G : Ctx nat n) (F : nat -> Fin n),
  PT.normal_context G = true ->
  PT.normal_context (handler_context hs G (fun r => var (F r))) = true.
Proof.
  induction hs; intros; cbn [handler_context PT.normal_context]; [assumption |].
  rewrite IHhs by assumption. rewrite signature_rename. cbn [rename].
  rewrite signature_normal; reflexivity.
Qed.

(** All pairs below k+1 are included; their function rank is at most k+1.
    Thus k+2 family variables suffice, even for unused boundary pairs. *)
Definition handlers k : list Handler :=
  flat_map (fun a => flat_map (fun b => [Abs a b; App a b]) (seq 0 (S k))) (seq 0 (S k)).

Lemma handlers_abs k a b : a <= k -> b <= k -> In (Abs a b) (handlers k).
Proof.
  intros Ha Hb; unfold handlers. apply in_flat_map; exists a; split.
  - apply in_seq; lia.
  - apply in_flat_map; exists b; split; [apply in_seq; lia | now left].
Qed.
Lemma handlers_app k a b : a <= k -> b <= k -> In (App a b) (handlers k).
Proof.
  intros Ha Hb; unfold handlers. apply in_flat_map; exists a; split.
  - apply in_seq; lia.
  - apply in_flat_map; exists b; split; [apply in_seq; lia | right; now left].
Qed.
Lemma handlers_rank k h : In h (handlers k) -> handler_rank h <= S k.
Proof.
  unfold handlers; intros Hin. apply in_flat_map in Hin as [a [Ha Hin]].
  apply in_flat_map in Hin as [b [Hb Hin]]. apply in_seq in Ha; apply in_seq in Hb.
  destruct Hin as [<-|[<-|[]]]; cbn [handler_rank]; lia.
Qed.

Definition family_base k := family_context (S (S k)) 0 (ε & 𝓤 0).
Definition family_vars k r := RQ.slot (S (S k)) r (@fzero 0).
Definition family_terms k r : Term nat (S (S k)+1) := var (family_vars k r).
Definition package_context k := handler_context (handlers k) (family_base k) (family_terms k).
Definition width k := length (handlers k) + (S (S k)+1).
Definition ground k : Fin (width k) := @up (length (handlers k)) (S (S k)+1)
  (@up (S (S k)) 1 fzero).
Definition families k r : Term nat (width k) := rename (@up (length (handlers k)) (S (S k)+1)) (family_terms k r).
Definition abs_var k a b : Fin (width k) := handler_slot (handlers k) (Abs a b) (@up (S (S k)) 1 fzero).
Definition app_var k a b : Fin (width k) := handler_slot (handlers k) (App a b) (@up (S (S k)) 1 fzero).

Lemma family_base_typed k r : r <= S k ->
  @typ nat RankSorts _ (family_base k) (family_terms k r) (BP.family_type r r).
Proof.
  intro Hr; unfold family_base, family_terms. change (typ (family_context (S (S k)) 0 (ε & 𝓤 0))
    (var (RQ.slot (S (S k)) r fzero)) (BP.family_type (0+r) (0+r))).
  apply family_slot_typing; lia.
Qed.

Theorem package_context_wf k : @wf nat RankSorts (width k) (package_context k).
Proof.
  unfold package_context. apply handler_context_wf.
  - apply family_context_wf; eapply wf_cons; [apply wf_empty | constructor; reflexivity].
  - intros h Hh; apply signature_sort.
    intros r Hr; apply family_base_typed. pose proof (handlers_rank k h Hh); lia.
Qed.

Theorem package_context_normal k : PT.normal_context (package_context k) = true.
Proof.
  unfold package_context, family_terms. apply handler_context_normal.
  apply family_context_normal; reflexivity.
Qed.

Lemma ground_typed k : @typ nat RankSorts (width k) (package_context k) (var (ground k)) (𝓤 0).
Proof.
  unfold ground. change (typ (package_context k)
    (rename (@up (length (handlers k)) (S (S k)+1)) (rename (@up (S (S k)) 1) (var fzero)))
    (rename (@up (length (handlers k)) (S (S k)+1)) (rename (@up (S (S k)) 1) (𝓤 0)))).
  unfold package_context.
  apply handler_source_typing, family_source_typing.
  change (typ (ε & 𝓤 0) (var fzero) ((ε & 𝓤 0) !! fzero)); constructor.
Qed.

Lemma families_typed k : TH.BoundedFamiliesTyped k (package_context k) (families k).
Proof.
  intros r Hr. unfold families, package_context.
  change (typ (handler_context (handlers k) (family_base k) (family_terms k))
    (rename (@up (length (handlers k)) (S (S k)+1)) (family_terms k r))
    (rename (@up (length (handlers k)) (S (S k)+1)) (BP.family_type r r))).
  apply handler_source_typing, family_base_typed; lia.
Qed.

Lemma cases_typed k : PA.RankCasesTyped k (package_context k) (families k)
  (fun a b => var (abs_var k a b)) (fun a b => var (app_var k a b)).
Proof.
  split; intros a b Hk.
  - change (typ (package_context k) (var (abs_var k a b)) (signature (families k) (Abs a b))).
    unfold package_context, abs_var, families. rewrite <- signature_rename.
    apply handler_slot_typing, handlers_abs; lia.
  - change (typ (package_context k) (var (app_var k a b)) (signature (families k) (App a b))).
    unfold package_context, app_var, families. rewrite <- signature_rename.
    apply handler_slot_typing, handlers_app; lia.
Qed.

Definition source_ren k (_ : Fin 1) : Fin (width k) := ground k.
Definition result_type k A := BP.interpreted_type (families k) (ground k) A.
Definition payload k {t A} (d : @EQ.derivation 1 emptyEnv fzero t A) :=
  PA.quoted d (width k) (source_ren k) (families k)
    (fun a b => var (abs_var k a b)) (fun a b => var (app_var k a b)).
Definition quote k {t A} (d : @EQ.derivation 1 emptyEnv fzero t A) : Term nat 0 :=
  PT.close_term (package_context k) (payload k d).
Definition quote_type k A : Term nat 0 := PT.close_type (package_context k) (result_type k A).

Theorem payload_typed k t A (d : @EQ.derivation 1 emptyEnv fzero t A) :
  TH.rank_budget d <= k ->
  @typ nat RankSorts (width k) (package_context k) (payload k d) (result_type k A).
Proof.
  intro Hk; unfold payload, result_type. eapply PA.quoted_typed;
    [exact Hk | apply ground_typed | apply families_typed | apply cases_typed |].
  intros i C Hi; discriminate Hi.
Qed.

Theorem quote_typed k t A (d : @EQ.derivation 1 emptyEnv fzero t A) :
  TH.rank_budget d <= k -> @typ nat RankSorts 0 ε (quote k d) (quote_type k A).
Proof.
  intro Hk; unfold quote, quote_type. apply PT.close_typing;
    [apply package_context_wf | apply payload_typed; exact Hk].
Qed.

Theorem payload_normal k t A (d : @EQ.derivation 1 emptyEnv fzero t A) :
  normalb (payload k d) = true.
Proof.
  unfold payload, families, family_terms; cbn [rename]. apply PF.quoted_normal.
Qed.

Theorem quote_normal k t A (d : @EQ.derivation 1 emptyEnv fzero t A) :
  normalb (quote k d) = true.
Proof.
  unfold quote; apply PT.close_normal; [apply package_context_normal | apply payload_normal].
Qed.

Theorem quote_injective k t u A B
    (d : @EQ.derivation 1 emptyEnv fzero t A) (e : @EQ.derivation 1 emptyEnv fzero u B) :
  quote k d = quote k e -> t = u.
Proof.
  intro H; unfold quote in H. apply PT.close_injective in H.
  unfold payload, families, family_terms in H; cbn [rename] in H.
  eapply PF.quoted_injective; [| exact H].
  intros i j Hij; dependent elimination i; dependent elimination j; try reflexivity;
    match goal with z : Fin 0 |- _ => inversion z end.
Qed.

Theorem quote_conversion_injective k t u A B
    (d : @EQ.derivation 1 emptyEnv fzero t A) (e : @EQ.derivation 1 emptyEnv fzero u B) :
  def_equiv nat 0 (quote k d) (quote k e) -> t = u.
Proof.
  intro H; apply quote_injective with (k := k) (d := d) (e := e).
  eapply ChurchSyntaxFaithful.normal_conversion_identity;
    [apply quote_normal | apply quote_normal | exact H].
Qed.

Lemma result_type_sort k A : order A <= k ->
  @typ nat RankSorts (width k) (package_context k) (result_type k A) (𝓤 (order A)).
Proof.
  intro HA; unfold result_type. eapply TH.interpreted_bounded_sort;
    [exact HA | apply ground_typed | apply families_typed].
Qed.

Fixpoint family_fill count start {m n} (base : Fin m -> Term nat n)
    : Fin (count+m) -> Term nat n :=
  match count with
  | 0 => base
  | S c => fin_match (BP.type_identity start) (family_fill c (S start) base)
  end.

Fixpoint handler_fill (hs : list Handler) {m n} (base : Fin m -> Term nat n)
    : Fin (length hs+m) -> Term nat n :=
  match hs with
  | [] => base
  | h::rest => fin_match (handler_value h) (handler_fill rest base)
  end.

Definition fill k {n} (o : Fin n) : Fin (width k) -> Term nat n :=
  handler_fill (handlers k) (family_fill (S (S k)) 0 (fun _ : Fin 1 => var o)).

Lemma family_fill_source count : forall start m n (base : Fin m -> Term nat n) i,
  family_fill count start base (@up count m i) = base i.
Proof.
  induction count; intros; cbn [family_fill up fin_match]; [reflexivity | apply IHcount].
Qed.

Lemma family_fill_slot count : forall start m n (base : Fin m -> Term nat n) r o,
  r < count -> family_fill count start base (RQ.slot count r o) = BP.type_identity (start+r).
Proof.
  induction count; intros start m n env r o Hr; [lia |]. destruct r; cbn [family_fill RQ.slot fin_match].
  - now rewrite Nat.add_0_r.
  - change (family_fill count (S start) env (RQ.slot count r o) = BP.type_identity (start+S r)).
    replace (start+S r) with (S start+r) by lia. apply IHcount; lia.
Qed.

Lemma handler_fill_source hs : forall m n (base : Fin m -> Term nat n) i,
  handler_fill hs base (@up (length hs) m i) = base i.
Proof.
  induction hs; intros; cbn [handler_fill up length fin_match]; [reflexivity | apply IHhs].
Qed.

Lemma handler_fill_slot hs : forall m n (base : Fin m -> Term nat n) h o,
  In h hs -> handler_fill hs base (handler_slot hs h o) = handler_value h.
Proof.
  induction hs; intros; [contradiction |]. cbn [handler_fill handler_slot].
  destruct (handler_eq_dec h a) as [->|Hneq]; cbn [fin_match]; [reflexivity |].
  apply IHhs. destruct H; [congruence | assumption].
Qed.

Lemma fill_ground k n (o : Fin n) : fill k o (ground k) = var o.
Proof. unfold fill, ground; rewrite handler_fill_source, family_fill_source; reflexivity. Qed.

Lemma fill_family k n (o : Fin n) r : r <= S k ->
  replace (fill k o) (families k r) = BP.type_identity r.
Proof.
  intro Hr; unfold fill, families, family_terms, family_vars. cbn [rename replace].
  rewrite handler_fill_source, family_fill_slot by lia. reflexivity.
Qed.

Lemma fill_abs k n (o : Fin n) a b : Nat.max (S a) b <= k ->
  fill k o (abs_var k a b) = BP.abs_identity a b.
Proof.
  intro H; unfold fill, abs_var. rewrite handler_fill_slot; [reflexivity | apply handlers_abs; lia].
Qed.

Lemma fill_app k n (o : Fin n) a b : Nat.max (S a) b <= k ->
  fill k o (app_var k a b) = BP.app_identity a b.
Proof.
  intro H; unfold fill, app_var. rewrite handler_fill_slot; [reflexivity | apply handlers_app; lia].
Qed.

Lemma handler_value_replace m n (sigma : Fin m -> Term nat n) h :
  replace sigma (handler_value h) = handler_value h.
Proof. destruct h; reflexivity. Qed.

Lemma family_fill_replace count : forall start m n p
    (base : Fin m -> Term nat n) (sigma : Fin n -> Term nat p) i,
  replace sigma (family_fill count start base i) =
  family_fill count start (fun j => replace sigma (base j)) i.
Proof.
  induction count; intros; [reflexivity |].
  dependent elimination i; cbn [family_fill fin_match]; [reflexivity | apply IHcount].
Qed.

Lemma handler_fill_replace hs : forall m n p
    (base : Fin m -> Term nat n) (sigma : Fin n -> Term nat p) i,
  replace sigma (handler_fill hs base i) =
  handler_fill hs (fun j => replace sigma (base j)) i.
Proof.
  induction hs; intros; [reflexivity |].
  dependent elimination i; cbn [handler_fill fin_match];
    [apply handler_value_replace | apply IHhs].
Qed.

Lemma family_fill_ext count : forall start m n (base other : Fin m -> Term nat n),
  (forall i, base i = other i) -> forall j,
  family_fill count start base j = family_fill count start other j.
Proof.
  induction count; intros; [apply H |].
  dependent elimination j; cbn [family_fill fin_match]; [reflexivity | apply IHcount; exact H].
Qed.

Lemma handler_fill_ext hs : forall m n (base other : Fin m -> Term nat n),
  (forall i, base i = other i) -> forall j,
  handler_fill hs base j = handler_fill hs other j.
Proof.
  induction hs; intros; [apply H |].
  dependent elimination j; cbn [handler_fill fin_match]; [reflexivity | apply IHhs; exact H].
Qed.

Lemma fill_replace k m n (sigma : Fin m -> Term nat n) (o : Fin m) (p : Fin n) :
  sigma o = var p -> forall i, replace sigma (fill k o i) = fill k p i.
Proof.
  intros Ho i; unfold fill. rewrite handler_fill_replace.
  apply handler_fill_ext; intro j. rewrite family_fill_replace.
  apply family_fill_ext; intro l; cbn [replace]; exact Ho.
Qed.

Lemma typed_sub_cons m n (G : Ctx nat m) (H : Ctx nat n) sigma A v :
  TypedSub G H sigma -> @typ nat RankSorts n H v (replace sigma A) ->
  TypedSub (G & A) H (fin_match v sigma).
Proof.
  intros HS Hv i; dependent elimination i; cbn [index ctx_top ctx_pred fin_match].
  - unfold shift; rewrite replace_rename. exact Hv.
  - unfold shift; rewrite replace_rename. apply HS.
Qed.

Lemma family_fill_typed count : forall start m n (G : Ctx nat m) (H : Ctx nat n) sigma,
  TypedSub G H sigma ->
  TypedSub (family_context count start G) H (family_fill count start sigma).
Proof.
  induction count; intros; cbn [family_context family_fill]; [assumption |].
  apply typed_sub_cons; [apply IHcount; assumption |].
  change (typ H (BP.type_identity start) (BP.family_type start start)).
  apply BP.type_identity_typing.
Qed.

Lemma handler_fill_typed hs : forall m n (G : Ctx nat m) F (H : Ctx nat n) sigma,
  TypedSub G H sigma ->
  (forall h, In h hs -> @typ nat RankSorts n H (handler_value h) (replace sigma (signature F h))) ->
  TypedSub (handler_context hs G F) H (handler_fill hs sigma).
Proof.
  induction hs; intros m n G F H sigma HS HV; cbn [handler_context handler_fill]; [exact HS |].
  apply typed_sub_cons.
  - apply IHhs; [exact HS | intros; apply HV; now right].
  - rewrite replace_rename.
    replace (replace (fun x => handler_fill hs sigma (up x)) (signature F a))
      with (replace sigma (signature F a)).
    + apply HV; now left.
    + symmetry; apply replace_ext; apply handler_fill_source.
Qed.

Lemma signature_replace m n (sigma : Fin m -> Term nat n) F h :
  replace sigma (signature F h) = signature (fun r => replace sigma (F r)) h.
Proof.
  destruct h; unfold signature, BP.indexed_abs_type, BP.indexed_app_type;
    cbn [replace]; unfold BP.abs_case_type, BP.app_case_type;
    repeat (rewrite ?TH.arr_replace; cbn [replace]; rewrite ?replace_lift_shift);
    cbn [transpose fin_match]; reflexivity.
Qed.

Lemma signature_ext n (F K : nat -> Term nat n) h :
  (forall r, r <= handler_rank h -> F r = K r) -> signature F h = signature K h.
Proof.
  destruct h as [a b|a b]; intro HE; cbn [signature handler_rank] in *;
    rewrite (HE a ltac:(lia)), (HE b ltac:(lia)), (HE (Nat.max (S a) b) ltac:(lia)); reflexivity.
Qed.

Theorem fill_typed k n (G : Ctx nat n) (o : Fin n) :
  @typ nat RankSorts n G (var o) (𝓤 0) -> TypedSub (package_context k) G (fill k o).
Proof.
  intro Ho; unfold package_context, fill. apply handler_fill_typed.
  - apply family_fill_typed. intro i; dependent elimination i.
    + exact Ho.
    + match goal with z : Fin 0 |- _ => inversion z end.
  - intros h Hh. rewrite signature_replace.
    replace (signature (fun r => replace
      (family_fill (S (S k)) 0 (fun _ : Fin 1 => var o)) (family_terms k r)) h)
      with (@signature n (fun r => BP.type_identity r) h).
    + apply handler_value_typed.
    + symmetry; apply signature_ext. intros r Hr.
      unfold family_terms, family_vars; cbn [replace]. rewrite family_fill_slot;
        [reflexivity | pose proof (handlers_rank k h Hh); lia].
Qed.

Theorem quote_type_sort k A : order A <= k ->
  exists r, @typ nat RankSorts 0 ε (quote_type k A) (𝓤 r).
Proof.
  intro HA; unfold quote_type. eapply PT.close_type_sort;
    [apply package_context_wf | apply result_type_sort; exact HA].
Qed.

Theorem payload_recovers k t A (d : @EQ.derivation 1 emptyEnv fzero t A) n (o : Fin n) :
  TH.rank_budget d <= k ->
  reduces_to nat n (replace (fill k o) (payload k d)) (rename (fun _ : Fin 1 => o) t).
Proof.
  intro Hk; unfold payload. eapply PR.quoted_substitution_recovers;
    [exact Hk | | | |].
  - intro i; apply fill_ground.
  - intros r Hr; apply fill_family; lia.
  - intros a b Hab; cbn [replace]; apply fill_abs; exact Hab.
  - intros a b Hab; cbn [replace]; apply fill_app; exact Hab.
Qed.

Theorem run_quote_recovers k t A (d : @EQ.derivation 1 emptyEnv fzero t A) n (o : Fin n) :
  TH.rank_budget d <= k ->
  reduces_to nat n
    (PT.run (package_context k) (fill k o) (PT.lift_closed (quote k d)))
    (rename (fun _ : Fin 1 => o) t).
Proof.
  intro Hk; eapply rtc_trans; [apply PT.run_closed_term | apply payload_recovers; exact Hk].
Qed.

(** Coverage is existential in Prop; executable quotation consumes the
    independent Type-valued source derivation, not a target typing proof.
    A fixed budget supplies one finite parameter interface for every source
    derivation within it, independent of source term size and type shape. *)
Theorem every_source_quote t A : @has_type 1 emptyEnv fzero t A ->
  exists k (q : Term nat 0),
    normalb q = true /\ @typ nat RankSorts 0 ε q (quote_type k A) /\
    forall n (o : Fin n), reduces_to nat n
      (PT.run (package_context k) (fill k o) (PT.lift_closed q))
      (rename (fun _ : Fin 1 => o) t).
Proof.
  intro Ht; apply EQ.source_derivation in Ht; destruct Ht as [d].
  exists (TH.rank_budget d), (quote (TH.rank_budget d) d). split; [apply quote_normal |].
  split; [apply quote_typed; lia | intros; apply run_quote_recovers; lia].
Qed.

Print Assumptions package_context_wf.
Print Assumptions quote_typed.
Print Assumptions quote_normal.
Print Assumptions quote_injective.
Print Assumptions quote_conversion_injective.
Print Assumptions fill_typed.
Print Assumptions fill_replace.
Print Assumptions quote_type_sort.
Print Assumptions payload_recovers.
Print Assumptions run_quote_recovers.
Print Assumptions every_source_quote.
End PHOASPackage.
