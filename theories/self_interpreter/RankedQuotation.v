From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing Preservation Ranks Reduction
  AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import STLCEmbedding Greedy.
From PTSrk.SelfInterpreter Require Import RankedDecoder.
Import Context ChurchSTLC.

Module RankedQuotation.

(** A genuine shallow quotation precursor for the independent Church STLC
    source.  The budget bounds ALL application function types, not merely
    the final result type.  Source annotations are normal simple-type codes.
    There is no dependent conversion case in this source calculus. *)
Definition blocker_type (r : nat) {n} : Term nat n :=
  Π (𝓤 r) (Π (var fzero) (var (fsucc fzero))).
Definition blocker_value (r : nat) {n} : Term nat n :=
  lam (𝓤 r) (lam (var fzero) (var fzero)).

Lemma blocker_type_rename r m n (f : Fin m -> Fin n) :
  rename f (@blocker_type r m) = @blocker_type r n.
Proof. reflexivity. Qed.
Lemma blocker_value_rename r m n (f : Fin m -> Fin n) :
  rename f (@blocker_value r m) = @blocker_value r n.
Proof. reflexivity. Qed.

Lemma unblock r n (T t : Term nat n) :
  reduces_to nat n (app (app (blocker_value r) T) t) t.
Proof.
  unfold blocker_value. eapply rtc_step.
  - apply step_app_left, step_beta.
  - cbn [subst replace transpose fin_match shift rename weak].
    apply rtc_in, step_beta.
Qed.

Lemma subst_shift_identity n (T t : Term nat n) : subst (shift T) t = T.
Proof. unfold subst, shift; rewrite replace_rename; apply replace_var. Qed.

Inductive bounded_type (k : nat) :
  forall {n}, Env n -> Fin n -> Term nat n -> Ty -> Prop :=
| bt_var {n} E (o i : Fin n) A :
    E i = Some A -> bounded_type k E o (var i) A
| bt_lam {n} E (o : Fin n) A B b :
    bounded_type k (extend E A) (fsucc o) b B ->
    bounded_type k E o (lam (code A o) b) (arrow A B)
| bt_app {n} E (o : Fin n) A B f u :
    order (arrow A B) <= k ->
    bounded_type k E o f (arrow A B) -> bounded_type k E o u A ->
    bounded_type k E o (app f u) B.

Theorem bounded_type_source k n E o (t : Term nat n) A :
  bounded_type k E o t A -> has_type E o t A.
Proof. intro H; induction H; econstructor; eassumption. Qed.

Lemma bounded_type_monotone k n E o (t : Term nat n) A :
  bounded_type k E o t A -> forall j, k <= j -> bounded_type j E o t A.
Proof. intro H; induction H; intros j Hj; econstructor; eauto; lia. Qed.

Theorem every_source_has_budget n E o (t : Term nat n) A :
  has_type E o t A -> exists k, bounded_type k E o t A.
Proof.
  intro H; induction H.
  - exists 0; constructor; assumption.
  - destruct IHhas_type as [k Hk]; exists k; constructor; assumption.
  - destruct IHhas_type1 as [j Hj], IHhas_type2 as [k Hk].
    exists (Nat.max (order (arrow A B)) (Nat.max j k)).
    eapply bt_app with (A := A); [lia | |];
      eapply bounded_type_monotone; eauto; lia.
Qed.

(** The source environment is independent of PTS typing.  The target
    renaming and blocker-variable assignment are explicit parameters. *)
Inductive quotation (k : nat) : forall {m n}, Env m -> Fin m ->
  (Fin m -> Fin n) -> (nat -> Fin n) -> Term nat m -> Ty -> Term nat n -> Prop :=
| quote_var {m n} E o (rho : Fin m -> Fin n) blocks i A :
    E i = Some A -> quotation k E o rho blocks (var i) A (var (rho i))
| quote_lam {m n} E o (rho : Fin m -> Fin n) blocks A B b q :
    quotation k (extend E A) (fsucc o) (weak rho)
      (fun r => fsucc (blocks r)) b B q ->
    quotation k E o rho blocks (lam (code A o) b) (arrow A B)
      (lam (code A (rho o)) q)
| quote_app {m n} E o (rho : Fin m -> Fin n) blocks A B f u qf qu :
    order (arrow A B) <= k ->
    quotation k E o rho blocks f (arrow A B) qf ->
    quotation k E o rho blocks u A qu ->
    quotation k E o rho blocks (app f u) B
      (app (app (app (var (blocks (order (arrow A B))))
        (code (arrow A B) (rho o))) qf) qu).

Theorem quotation_exists k m E o (t : Term nat m) A :
  bounded_type k E o t A -> forall n (rho : Fin m -> Fin n) blocks,
  exists q, quotation k E o rho blocks t A q.
Proof.
  intro H; induction H; intros l rho blocks.
  - eexists; constructor; eassumption.
  - destruct (IHbounded_type _ (weak rho) (fun r => fsucc (blocks r)))
      as [q Hq]. eexists; constructor; exact Hq.
  - destruct (IHbounded_type1 _ rho blocks) as [qf Hf],
      (IHbounded_type2 _ rho blocks) as [qu Hu].
    eexists; econstructor; eassumption.
Qed.

Theorem quotation_normal k m n E o rho blocks (t : Term nat m) A
    (q : Term nat n) :
  quotation k E o rho blocks t A q -> normalb q = true.
Proof.
  intro H; induction H; cbn [normalb isLambda].
  - reflexivity.
  - rewrite code_normal, IHquotation; reflexivity.
  - rewrite code_normal, IHquotation1, IHquotation2; reflexivity.
Qed.

Definition RenamedEnvTyped {m n} (G : Ctx nat n) (E : Env m)
    (o : Fin m) (rho : Fin m -> Fin n) :=
  forall i A, E i = Some A ->
    @typ nat RankSorts n G (var (rho i)) (code A (rho o)).
Definition BlockersTyped k {n} (G : Ctx nat n) (blocks : nat -> Fin n) :=
  forall r, r <= k -> @typ nat RankSorts n G (var (blocks r)) (blocker_type r).

Lemma blocker_application n (G : Ctx nat n) r (h T t : Term nat n) :
  @typ nat RankSorts n G h (blocker_type r) ->
  @typ nat RankSorts n G T (𝓤 r) -> @typ nat RankSorts n G t T ->
  @typ nat RankSorts n G (app (app h T) t) T.
Proof.
  intros Hh HT Ht.
  assert (HH : @typ nat RankSorts n G (app h T) (Π T (shift T))).
  { change (typ G (app h T)
      (subst (Π (var fzero) (var (fsucc fzero))) T)).
    eapply typ_app; eassumption. }
  assert (Hout : @typ nat RankSorts n G (app (app h T) t)
      (subst (shift T) t)) by (eapply typ_app; eassumption).
  rewrite subst_shift_identity in Hout; exact Hout.
Qed.

Theorem quotation_typed k m n E o rho blocks (t : Term nat m) A
    (q : Term nat n) :
  quotation k E o rho blocks t A q -> forall G,
  @typ nat RankSorts n G (var (rho o)) (𝓤 0) ->
  RenamedEnvTyped G E o rho -> BlockersTyped k G blocks ->
  @typ nat RankSorts n G q (code A (rho o)).
Proof.
  intro H; induction H; intros G Ho HE HB.
  - apply HE; assumption.
  - cbn [code]. eapply typ_λ with (ℓ := order A).
    + apply code_typed; exact Ho.
    + apply IHquotation.
      * change (typ (G & code A (rho o)) (shift (var (rho o))) (shift (𝓤 0))).
        apply weakening; exact Ho.
      * intros i C HC. dependent elimination i; cbn [extend fin_match] in HC.
        -- inversion HC; subst C. cbn.
           rewrite <- (code_rename A _ _ fsucc (rho o)).
           change (typ (G & code A (rho o)) (var fzero)
             ((G & code A (rho o)) !! fzero)). constructor.
        -- cbn. rewrite <- (code_rename C _ _ fsucc (rho o)).
           change (typ (G & code A (rho o)) (shift (var (rho f)))
             (shift (code C (rho o)))). apply weakening. apply HE; exact HC.
      * intros r Hr. change (typ (G & code A (rho o))
          (shift (var (blocks r))) (shift (blocker_type r))).
        apply weakening, HB; exact Hr.
  - rewrite <- (code_subst B (rho o) qu).
    eapply typ_app with (U := code A (rho o)).
    + apply blocker_application with (r := order (arrow A B)).
      * apply HB; exact H.
      * apply (code_typed (arrow A B)); exact Ho.
      * apply IHquotation1; assumption.
    + apply IHquotation2; assumption.
Qed.

(** Recovery is ORIGINAL beta reduction, including annotations.  The
    substitution may have any target scope: source variables remain variables
    and blocker variables become the actual polymorphic identities. *)
Theorem quotation_recovery k m n E o rho blocks (t : Term nat m) A
    (q : Term nat n) :
  quotation k E o rho blocks t A q ->
  forall l (sigma : Fin n -> Term nat l) (ren : Fin m -> Fin l),
  (forall i, sigma (rho i) = var (ren i)) ->
  (forall r, r <= k -> sigma (blocks r) = blocker_value r) ->
  reduces_to nat l (replace sigma q) (rename ren t).
Proof.
  intro H; induction H; intros l sigma ren HS HB; cbn [replace rename].
  - rewrite HS; reflexivity.
  - rewrite (code_replace A _ _ sigma (rho o) (ren o) (HS o)), code_rename.
    apply (λ_cong_par nat (fun n => RTC (step nat n))); [reflexivity |].
    apply IHquotation.
    + intro i; dependent elimination i; cbn.
      * reflexivity.
      * rewrite HS; reflexivity.
    + intros r Hr. change (shift (sigma (blocks r)) = blocker_value r).
      rewrite HB by exact Hr; reflexivity.
  - rewrite HB by exact H.
    rewrite (code_replace (arrow A B) _ _ sigma (rho o) (ren o) (HS o)).
    eapply rtc_trans.
    + apply (app_cong_par nat (fun n => RTC (step nat n))); [apply unblock | reflexivity].
    + apply (app_cong_par nat (fun n => RTC (step nat n))).
      * apply IHquotation1; assumption.
      * apply IHquotation2; assumption.
Qed.

(** This structural eraser, unlike beta recovery, witnesses injectivity on
    original annotated syntax.  Its behavior on non-quotations is irrelevant. *)
Fixpoint erase {n} (q : Term nat n) : Term nat n :=
  match q with
  | lam A b => lam A (erase b)
  | app (app (app _ _) f) u => app (erase f) (erase u)
  | _ => q
  end.

Theorem quotation_erasure k m n E o rho blocks (t : Term nat m) A
    (q : Term nat n) :
  quotation k E o rho blocks t A q -> erase q = rename rho t.
Proof.
  intro H; induction H; cbn [erase rename].
  - reflexivity.
  - rewrite code_rename, IHquotation; reflexivity.
  - rewrite IHquotation1, IHquotation2; reflexivity.
Qed.

Theorem quotation_injective k m n E o rho blocks (t u : Term nat m) A B
    (q : Term nat n) (back : Fin n -> Term nat m) :
  (forall i, back (rho i) = var i) ->
  quotation k E o rho blocks t A q ->
  quotation k E o rho blocks u B q -> t = u.
Proof.
  intros Hb Ht Hu.
  pose proof (quotation_erasure _ _ _ _ _ _ _ _ _ _ Ht) as Et.
  pose proof (quotation_erasure _ _ _ _ _ _ _ _ _ _ Hu) as Eu.
  assert (Htback : replace back (rename rho t) = t).
  { rewrite replace_rename.
    transitivity (replace (fun i => var i) t); [apply replace_ext; exact Hb | apply replace_var]. }
  assert (Huback : replace back (rename rho u) = u).
  { rewrite replace_rename.
    transitivity (replace (fun i => var i) u); [apply replace_ext; exact Hb | apply replace_var]. }
  rewrite <- Htback, <- Huback, <- Et, <- Eu; reflexivity.
Qed.

(** Concrete finite telescopes.  The last inserted variable has rank start;
    the earlier variables have ranks start+1,...,start+count-1. *)
Fixpoint blocker_context (count start : nat) {n} (G : Ctx nat n)
    : Ctx nat (count + n) :=
  match count with
  | 0 => G
  | S c => blocker_context c (S start) G & blocker_type start
  end.

Fixpoint slot (count r : nat) {n} (fallback : Fin n) : Fin (count + n) :=
  match count with
  | 0 => fallback
  | S c => match r with 0 => fzero | S j => fsucc (slot c j fallback) end
  end.

Fixpoint fill (count start : nat) {n} : Fin (count + n) -> Term nat n :=
  match count with
  | 0 => fun i => var i
  | S c => fin_match (blocker_value start) (fill c (S start))
  end.

Lemma fill_source count : forall start n (i : Fin n),
  fill count start (@up count n i) = var i.
Proof. induction count; intros; cbn; [reflexivity | apply IHcount]. Qed.

Lemma fill_slot count : forall start n r (o : Fin n), r < count ->
  fill count start (slot count r o) = blocker_value (start + r).
Proof.
  induction count; intros start n r o Hr; [lia |].
  destruct r; cbn [fill slot fin_match].
  - rewrite Nat.add_0_r; reflexivity.
  - change (fill count (S start) (slot count r o) = blocker_value (start + S r)).
    rewrite IHcount by lia. f_equal; lia.
Qed.

Lemma context_source_typing count : forall start n (G : Ctx nat n) t T,
  @typ nat RankSorts n G t T ->
  @typ nat RankSorts (count+n) (blocker_context count start G)
    (rename up t) (rename up T).
Proof.
  induction count; intros start n G t T Ht; cbn [blocker_context].
  - cbn [up]; rewrite !rename_id; exact Ht.
  - rewrite <- !shift_up. apply weakening, IHcount; exact Ht.
Qed.

Lemma context_slot_typing count : forall start n (G : Ctx nat n) r o,
  r < count ->
  @typ nat RankSorts (count+n) (blocker_context count start G)
    (var (slot count r o)) (blocker_type (start+r)).
Proof.
  induction count; intros start n G r o Hr; [lia |].
  destruct r; cbn [blocker_context slot].
  - rewrite Nat.add_0_r.
    change (typ (blocker_context count (S start) G & blocker_type start)
      (var fzero)
      ((blocker_context count (S start) G & blocker_type start) !! fzero)).
    constructor.
  - replace (start + S r) with (S start + r) by lia.
    change (typ (blocker_context count (S start) G & blocker_type start)
      (shift (var (slot count r o))) (shift (blocker_type (S start+r)))).
    apply weakening, IHcount; lia.
Qed.

Fixpoint pack (count start : nat) {n} : Term nat (count+n) -> Term nat n :=
  match count with
  | 0 => fun q => q
  | S c => fun q => pack c (S start) (lam (blocker_type start) q)
  end.
Fixpoint package_type (count start : nat) {n} (A : Term nat n) : Term nat n :=
  match count with
  | 0 => A
  | S c => package_type c (S start) (Π (blocker_type start) (shift A))
  end.
Fixpoint unpack (count start : nat) {n} (p : Term nat n) : Term nat n :=
  match count with
  | 0 => p
  | S c => app (unpack c (S start) p) (blocker_value start)
  end.

Theorem pack_normal count : forall start n (q : Term nat (count+n)),
  normalb q = true -> normalb (pack count start q) = true.
Proof.
  induction count; intros start n q Hq; cbn [pack]; [exact Hq |].
  apply IHcount; cbn [normalb blocker_type]; exact Hq.
Qed.

Theorem pack_injective count : forall start n (q q' : Term nat (count+n)),
  pack count start q = pack count start q' -> q = q'.
Proof.
  induction count; intros start n q q' Hq; [exact Hq |].
  cbn [pack] in Hq. apply IHcount in Hq. now injection Hq.
Qed.

Theorem pack_typed count : forall start n (G : Ctx nat n) q A,
  @typ nat RankSorts (count+n) (blocker_context count start G)
    q (rename up A) ->
  @typ nat RankSorts n G (pack count start q) (package_type count start A).
Proof.
  induction count; intros start n G q A Hq; cbn [pack package_type].
  - cbn [up] in Hq; rewrite rename_id in Hq; exact Hq.
  - apply IHcount. cbn [rename].
    eapply typ_λ with (ℓ := S start).
    + apply identity_type_sort.
    + replace (rename (weak (@up count n)) (shift A))
        with (rename (@up (S count) n) A).
      * exact Hq.
      * unfold shift; rewrite rename_comp. apply rename_ext; reflexivity.
Qed.

Theorem unpack_typed count : forall start n (G : Ctx nat n) p A,
  @typ nat RankSorts n G p (package_type count start A) ->
  @typ nat RankSorts n G (unpack count start p) A.
Proof.
  induction count; intros start n G p A Hp; cbn [unpack]; [exact Hp |].
  assert (Hfun : @typ nat RankSorts n G (unpack count (S start) p)
    (Π (blocker_type start) (shift A))) by (apply IHcount; exact Hp).
  assert (Hout : @typ nat RankSorts n G
    (app (unpack count (S start) p) (blocker_value start))
    (subst (shift A) (blocker_value start))).
  { eapply typ_app; [exact Hfun | apply identity_value_typing]. }
  rewrite subst_shift_identity in Hout; exact Hout.
Qed.

Theorem unpack_pack count : forall start n (q : Term nat (count+n)),
  reduces_to nat n (unpack count start (pack count start q))
    (replace (fill count start) q).
Proof.
  induction count; intros start n q; cbn [pack unpack].
  - cbn [fill]; rewrite replace_var; reflexivity.
  - eapply rtc_trans.
    + apply (app_cong_par nat (fun n => RTC (step nat n))).
      * apply IHcount.
      * reflexivity.
    + cbn [replace blocker_type].
      eapply rtc_trans; [apply rtc_in, step_beta |].
      assert (Heq : subst (replace (transpose (fill count (S start))) q)
          (blocker_value start) = replace (fill (S count) start) q).
      { unfold subst; rewrite replace_replace. apply replace_ext.
        intro i; dependent elimination i; cbn [transpose fill fin_match].
        - reflexivity.
        - change (subst (shift (fill count (S start) f)) (blocker_value start) =
            fill count (S start) f). apply subst_shift_identity. }
      rewrite Heq; reflexivity.
Qed.

(** Finite-budget normal quotation and strong interpretation of the original
    annotated source terms.  These are uniformly defined PTS constructors;
    the natural-number budget remains an external family index. *)
Theorem finite_budget_quotation k n E o (t : Term nat n) A (G : Ctx nat n) :
  bounded_type k E o t A ->
  @typ nat RankSorts n G (var o) (𝓤 0) -> EnvTyped G E o ->
  exists q,
    quotation k E o (@up (S k) n) (fun r => slot (S k) r o) t A q /\
    normalb (pack (S k) 0 q) = true /\
    @typ nat RankSorts n G (pack (S k) 0 q)
      (package_type (S k) 0 (code A o)) /\
    @typ nat RankSorts n G (unpack (S k) 0 (pack (S k) 0 q)) (code A o) /\
    reduces_to nat n (unpack (S k) 0 (pack (S k) 0 q)) t.
Proof.
  intros Ht Ho HE.
  destruct (quotation_exists _ _ _ _ _ _ Ht _ (@up (S k) n)
    (fun r => slot (S k) r o)) as [q Hq].
  assert (HQ : @typ nat RankSorts n G (pack (S k) 0 q)
    (package_type (S k) 0 (code A o))).
  { apply pack_typed. rewrite code_rename.
    eapply quotation_typed; [exact Hq | | |].
    - change (typ (blocker_context (S k) 0 G)
        (rename up (var o)) (rename up (𝓤 0))).
      apply context_source_typing; exact Ho.
    - intros i B Hi. rewrite <- code_rename.
      change (typ (blocker_context (S k) 0 G)
        (rename up (var i)) (rename up (code B o))).
      apply context_source_typing, HE; exact Hi.
    - intros r Hr. change (typ (blocker_context (S k) 0 G)
        (var (slot (S k) r o)) (blocker_type (0+r))).
      apply context_slot_typing; lia. }
  exists q. split; [exact Hq |]. split.
  - apply pack_normal; eapply quotation_normal; exact Hq.
  - split; [exact HQ |]. split; [apply unpack_typed; exact HQ |].
    eapply rtc_trans; [apply unpack_pack |].
    assert (HR : reduces_to nat n (replace (fill (S k) 0) q)
      (rename (fun i => i) t)).
    { eapply quotation_recovery; [exact Hq | |].
      - apply fill_source.
      - intros r Hr. change (fill (S k) 0 (slot (S k) r o) = blocker_value (0+r)).
        apply fill_slot; lia. }
    rewrite rename_id in HR; exact HR.
Qed.

Theorem finite_package_injective k n E o (t u : Term nat n) A B
    (q q' : Term nat (S k+n)) :
  quotation k E o (@up (S k) n) (fun r => slot (S k) r o) t A q ->
  quotation k E o (@up (S k) n) (fun r => slot (S k) r o) u B q' ->
  pack (S k) 0 q = pack (S k) 0 q' -> t = u.
Proof.
  intros Ht Hu Heq. apply pack_injective in Heq; subst q'.
  eapply quotation_injective with (back := fill (S k) 0);
    [apply fill_source | exact Ht | exact Hu].
Qed.

Theorem every_source_has_normal_representation n E o (t : Term nat n) A
    (G : Ctx nat n) :
  has_type E o t A ->
  @typ nat RankSorts n G (var o) (𝓤 0) -> EnvTyped G E o ->
  exists k (p : Term nat n),
    normalb p = true /\
    @typ nat RankSorts n G p (package_type (S k) 0 (code A o)) /\
    @typ nat RankSorts n G (unpack (S k) 0 p) (code A o) /\
    reduces_to nat n (unpack (S k) 0 p) t.
Proof.
  intros Ht Ho HE. destruct (every_source_has_budget _ _ _ _ _ Ht) as [k Hk].
  destruct (finite_budget_quotation _ _ _ _ _ _ _ Hk Ho HE)
    as [q [Hq Hrest]]. exists k, (pack (S k) 0 q); exact Hrest.
Qed.

Corollary closed_source_normal_representation (t : Term nat 1) A :
  has_type emptyEnv fzero t A ->
  exists k (p : Term nat 1),
    normalb (close p) = true /\
    @typ nat RankSorts 0 ε (close p)
      (Π (𝓤 0) (package_type (S k) 0 (code A fzero))) /\
    @typ nat RankSorts 0 ε (close (unpack (S k) 0 p))
      (Π (𝓤 0) (code A fzero)) /\
    reduces_to nat 0 (close (unpack (S k) 0 p)) (close t).
Proof.
  intro Ht.
  assert (Ho : @typ nat RankSorts 1 (ε & 𝓤 0) (var fzero) (𝓤 0)).
  { change (typ (ε & 𝓤 0) (var fzero) ((ε & 𝓤 0) !! fzero)); constructor. }
  assert (HE : EnvTyped (ε & 𝓤 0) emptyEnv fzero).
  { intros i B Hi; discriminate. }
  destruct (every_source_has_normal_representation _ _ _ _ _ _ Ht Ho HE)
    as [k [p [HN [HP [HU HR]]]]].
  exists k, p. split; [exact HN |]. split.
  - unfold close. eapply typ_λ with (ℓ := 0); [constructor; reflexivity | exact HP].
  - split.
    + unfold close. eapply typ_λ with (ℓ := 0); [constructor; reflexivity | exact HU].
    + unfold close. apply (λ_cong_par nat (fun n => RTC (step nat n)));
        [reflexivity | exact HR].
Qed.

Print Assumptions quotation_normal.
Print Assumptions quotation_typed.
Print Assumptions quotation_recovery.
Print Assumptions quotation_injective.
Print Assumptions every_source_has_budget.
Print Assumptions finite_budget_quotation.
Print Assumptions finite_package_injective.
Print Assumptions every_source_has_normal_representation.
Print Assumptions closed_source_normal_representation.

End RankedQuotation.
