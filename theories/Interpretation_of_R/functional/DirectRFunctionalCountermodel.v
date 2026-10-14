(** A model of the independent source calculus, not a set model of PTS-rk.
    Stability is proved constructively; no native classical axiom is used. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Arith.Compare_dec Lia Setoids.Setoid.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From Interpretation_of_R Require Import DirectRCountermodel.
From Interpretation_of_R.functional Require Import DirectRFirstOrder DirectRFunctionalSyntax.
Import ListNotations.
Module FunctionalCountermodel.
Import SourceCountermodel.
Definition extend {n} (env : Fin n -> point) x : Fin (S n) -> point := fin_match x env.
Fixpoint eval {n} (t : FirstOrder.term n) (env : Fin n -> point) : point :=
  match t with
  | FirstOrder.variable i => env i
  | FirstOrder.zero => zero
  | FirstOrder.successor u => successor (eval u env)
  | FirstOrder.addition u v => addition (eval u env) (eval v env)
  | FirstOrder.multiplication u v => multiplication (eval u env) (eval v env)
  end.
Fixpoint holds {n} (A : FirstOrder.formula n) (env : Fin n -> point) : Prop :=
  match A with
  | FirstOrder.equal t u => eval t env = eval u env
  | FirstOrder.less_equal t u => order (eval t env) (eval u env)
  | FirstOrder.falsity => False
  | FirstOrder.implication B C => holds B env -> holds C env
  | FirstOrder.conjunction B C => ~ (holds B env -> holds C env -> False)
  | FirstOrder.disjunction B C => ~ holds B env -> ~ holds C env -> False
  | FirstOrder.universal B => forall x, holds B (extend env x)
  | FirstOrder.existential B => ~ (forall x, ~ holds B (extend env x))
  end.
Lemma eval_ext {n} t (env env' : Fin n -> point) :
  (forall i, env i = env' i) -> eval t env = eval t env'.
Proof. intro H. induction t; cbn [eval]; congruence. Qed.
Lemma holds_ext {n} A (env env' : Fin n -> point) :
  (forall i, env i = env' i) -> (holds A env <-> holds A env').
Proof.
  revert env env'. induction A; intros env env' H; cbn [holds];
    try (rewrite !(eval_ext _ env env' H); reflexivity).
  - reflexivity.
  - rewrite (IHA1 env env' H), (IHA2 env env' H). reflexivity.
  - rewrite (IHA1 env env' H), (IHA2 env env' H). reflexivity.
  - rewrite (IHA1 env env' H), (IHA2 env env' H). reflexivity.
  - assert (HE : forall x, holds A (extend env x) <-> holds A (extend env' x)).
    { intro x. apply IHA. intro i. dependent elimination i; [reflexivity |apply H]. }
    split; intros HA x; apply HE; apply HA.
  - assert (HE : forall x, holds A (extend env x) <-> holds A (extend env' x)).
    { intro x. apply IHA. intro i. dependent elimination i; [reflexivity |apply H]. }
    split; intros HA HB; apply HA; intro x; intro HX; apply (HB x); apply HE; exact HX.
Qed.
Lemma eval_rename {m n} t (f : Fin m -> Fin n) env :
  eval (FunctionalSyntax.trename f t) env = eval t (fun i => env (f i)).
Proof. induction t; cbn [FunctionalSyntax.trename eval]; congruence. Qed.
Lemma eval_subst {m n} t (f : Fin m -> FirstOrder.term n) env :
  eval (FunctionalSyntax.tsubst f t) env = eval t (fun i => eval (f i) env).
Proof. induction t; cbn [FunctionalSyntax.tsubst eval]; congruence. Qed.
Lemma holds_rename {m} A : forall n (f : Fin m -> Fin n) env,
  holds (FunctionalSyntax.frename f A) env <-> holds A (fun i => env (f i)).
Proof.
  induction A; intros k f env; cbn [FunctionalSyntax.frename holds]; try (rewrite !eval_rename; reflexivity).
  - reflexivity.
  - rewrite IHA1, IHA2. reflexivity.
  - rewrite IHA1, IHA2. reflexivity.
  - rewrite IHA1, IHA2. reflexivity.
  - assert (HE : forall x,
      holds (FunctionalSyntax.frename (weak f) A) (extend env x) <->
      holds A (extend (fun i => env (f i)) x)).
    { intro x. rewrite IHA. apply holds_ext. intro i. dependent elimination i; reflexivity. }
    split; intros HA x; apply HE; apply HA.
  - assert (HE : forall x,
      holds (FunctionalSyntax.frename (weak f) A) (extend env x) <->
      holds A (extend (fun i => env (f i)) x)).
    { intro x. rewrite IHA. apply holds_ext. intro i. dependent elimination i; reflexivity. }
    split; intros HA HB; apply HA; intro x; intro HX; apply (HB x); apply HE; exact HX.
Qed.
Lemma holds_subst {m} A : forall n (f : Fin m -> FirstOrder.term n) env,
  holds (FunctionalSyntax.fsubst f A) env <-> holds A (fun i => eval (f i) env).
Proof.
  induction A; intros k f env; cbn [FunctionalSyntax.fsubst holds]; try (rewrite !eval_subst; reflexivity).
  - reflexivity.
  - rewrite IHA1, IHA2. reflexivity.
  - rewrite IHA1, IHA2. reflexivity.
  - rewrite IHA1, IHA2. reflexivity.
  - assert (HE : forall x,
      holds (FunctionalSyntax.fsubst (FunctionalSyntax.lift_sub f) A) (extend env x) <->
      holds A (extend (fun i => eval (f i) env) x)).
    { intro x. rewrite IHA. apply holds_ext. intro i. dependent elimination i; [reflexivity |].
      cbn [FunctionalSyntax.lift_sub fin_match]. rewrite eval_rename. reflexivity. }
    split; intros HA x; apply HE; apply HA.
  - assert (HE : forall x,
      holds (FunctionalSyntax.fsubst (FunctionalSyntax.lift_sub f) A) (extend env x) <->
      holds A (extend (fun i => eval (f i) env) x)).
    { intro x. rewrite IHA. apply holds_ext. intro i. dependent elimination i; [reflexivity |].
      cbn [FunctionalSyntax.lift_sub fin_match]. rewrite eval_rename. reflexivity. }
    split; intros HA HB; apply HA; intro x; intro HX; apply (HB x); apply HE; exact HX.
Qed.
Lemma holds_instance {n} A t (env : Fin n -> point) :
  holds (FunctionalSyntax.instantiate A t) env <-> holds A (extend env (eval t env)).
Proof.
  unfold FunctionalSyntax.instantiate. rewrite holds_subst. apply holds_ext.
  intro i. dependent elimination i; reflexivity.
Qed.
Lemma point_dec (x y : point) : {x = y} + {x <> y}.
Proof. decide equality. apply Nat.eq_dec. Qed.
Lemma order_dec x y : {order x y} + {~ order x y}.
Proof. destruct x as [m|], y as [n|]; cbn [order]; try tauto. apply le_dec. Qed.
Lemma decidable_stable (P : Prop) : {P} + {~ P} -> (~ ~ P -> P).
Proof. intros [H|H] Hnn; tauto. Qed.
Theorem holds_stable {n} (A : FirstOrder.formula n) : forall env, ~ ~ holds A env -> holds A env.
Proof.
  induction A; intro env; cbn [holds].
  - apply decidable_stable, point_dec.
  - apply decidable_stable, order_dec.
  - tauto.
  - intros H HA. apply IHA2. intro Hn. apply H. intro Hf. apply Hn, Hf, HA.
  - tauto.
  - tauto.
  - intros H x. apply IHA. intro Hn. apply H. intro Hf. apply Hn, Hf.
  - tauto.
Qed.
Lemma eval_numeral {n} v (env : Fin n -> point) : eval (FunctionalSyntax.numeral v) env = numeral v.
Proof. induction v; cbn [FunctionalSyntax.numeral eval numeral]; congruence. Qed.
Lemma disj_intro {n} xs A (env : Fin n -> point) :
  In A xs -> holds A env -> holds (FunctionalSyntax.flat_disjunction xs) env.
Proof.
  induction xs as [|B xs IH]; cbn [In FunctionalSyntax.flat_disjunction fold_right holds FunctionalSyntax.neg];
    [contradiction |]. intros [<-|HA] H Hn; [contradiction |apply IH; assumption].
Qed.
Lemma disj_refute {n} xs (env : Fin n -> point) :
  (forall A, In A xs -> ~ holds A env) -> ~ holds (FunctionalSyntax.flat_disjunction xs) env.
Proof.
  induction xs as [|B xs IH]; cbn [FunctionalSyntax.flat_disjunction fold_right holds FunctionalSyntax.neg]; [tauto |].
  intros H HD. apply IH; [intros A HA; apply H; right; exact HA |].
  apply HD, H. left. reflexivity.
Qed.
Lemma disj_eliminate {n} xs (env : Fin n -> point) (P : Prop) :
  (~ ~ P -> P) -> (forall A, In A xs -> holds A env -> P) ->
  holds (FunctionalSyntax.flat_disjunction xs) env -> P.
Proof.
  intros HS H HD. apply HS. intro Hn. apply (disj_refute xs env); [|exact HD].
  intros A HA HP. apply Hn, (H A HA), HP.
Qed.
Theorem axiom_sound {n} (A : FirstOrder.formula n) : FunctionalSyntax.axiom A -> forall env, holds A env.
Proof.
  intro H. destruct H; intro env.
  - cbn [holds eval]. rewrite !eval_numeral. apply ground_add.
  - cbn [holds eval]. rewrite !eval_numeral. apply ground_mul.
  - cbn [FunctionalSyntax.neg holds]. rewrite !eval_numeral. apply distinct. assumption.
  - intro x. cbn [holds eval]. rewrite eval_numeral. intro Horder.
    apply bounded in Horder. destruct Horder as [i [Hi Heq]].
    eapply disj_intro with (A:=FirstOrder.equal (FirstOrder.variable fzero) (FunctionalSyntax.numeral i)).
    + apply in_map_iff. exists i. split; [reflexivity |apply in_seq; lia].
    + cbn [holds eval extend fin_match]. rewrite eval_numeral. exact Heq.
  - intro x. destruct (comparable k x) as [Hleft|Hright].
    + eapply disj_intro; [left; reflexivity |]. cbn [holds eval extend fin_match].
      rewrite eval_numeral. exact Hleft.
    + eapply disj_intro; [right; left; reflexivity |]. cbn [holds eval extend fin_match].
      rewrite eval_numeral. exact Hright.
Qed.
Theorem soundness {n} Ξ (A : FirstOrder.formula n) : FunctionalSyntax.derives Ξ A ->
  forall env, (forall B, In B Ξ -> holds B env) -> holds A env.
Proof.
  intro HD. induction HD; intros env Hctx.
  - apply Hctx. exact H.
  - apply axiom_sound. exact H.
  - cbn [holds]. intro HA. apply IHHD. intros C [<-|HC]; [exact HA |apply Hctx; exact HC].
  - exact (IHHD1 env Hctx (IHHD2 env Hctx)).
  - cbn [holds]. intros Hn. apply Hn; [apply IHHD1 |apply IHHD2]; exact Hctx.
  - apply holds_stable. intro Hn. apply (IHHD env Hctx). intros HA HB. exact (Hn HA).
  - apply holds_stable. intro Hn. apply (IHHD env Hctx). intros HA HB. exact (Hn HB).
  - cbn [holds]. intros Hn _. apply Hn, IHHD, Hctx.
  - cbn [holds]. intros _ Hn. apply Hn, IHHD, Hctx.
  - apply holds_stable. intro Hn. apply (IHHD1 env Hctx).
    + intro HA. apply Hn, IHHD2. intros D [<-|HD]; [exact HA |apply Hctx; exact HD].
    + intro HB. apply Hn, IHHD3. intros D [<-|HD]; [exact HB |apply Hctx; exact HD].
  - intro x. apply IHHD. intros C HC. apply in_map_iff in HC. destruct HC as [B [<- HB]].
    apply holds_rename. change (holds B env). apply Hctx. exact HB.
  - apply holds_instance. exact (IHHD env Hctx (eval t env)).
  - cbn [holds]. intro Hn. apply (Hn (eval t env)).
    apply holds_instance, IHHD. exact Hctx.
  - apply holds_stable. intro Hn. apply (IHHD1 env Hctx). intros x HA.
    apply Hn. apply (proj1 (holds_rename B (S n) fsucc (extend env x))).
    apply IHHD2. intros C [<-|HC]; [exact HA |].
    apply in_map_iff in HC. destruct HC as [D [<- HD]].
    apply holds_rename. change (holds D env). apply Hctx. exact HD.
  - apply holds_stable. exact (IHHD env Hctx).
  - reflexivity.
  - apply holds_instance.
    specialize (IHHD1 env Hctx). cbn [holds] in IHHD1.
    rewrite <- IHHD1. apply holds_instance. apply IHHD2. exact Hctx.
Qed.
Definition order_reflexivity_sentence : FirstOrder.formula 0 :=
  FirstOrder.universal (FirstOrder.less_equal (FirstOrder.variable fzero) (FirstOrder.variable fzero)).
Theorem order_reflexivity_underivable : ~ FunctionalSyntax.derives [] order_reflexivity_sentence.
Proof.
  intro H. pose proof (soundness [] _ H (fun i => match i with end)) as HM.
  assert (HC : forall B : FirstOrder.formula 0, In B [] -> holds B (fun i => match i with end)).
  { intros B HB. contradiction. }
  exact (HM HC None).
Qed.
End FunctionalCountermodel.
