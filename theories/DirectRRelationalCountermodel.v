(** A model of the independent source calculus, not a set model of PTS-rk.
    Stability is proved constructively; no native classical axiom is used. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Arith.Compare_dec Lia Setoids.Setoid.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import DirectRCountermodel DirectRRelationalSyntax.
Import ListNotations.
Module RelationalCountermodel.
Import SourceCountermodel.
Definition extend {n} (env : Fin n -> point) x : Fin (S n) -> point := fin_match x env.
Fixpoint eval {n} (t : Relational.term n) (env : Fin n -> point) : point :=
  match t with
  | Relational.variable i => env i
  | Relational.zero => zero
  | Relational.successor u => successor (eval u env)
  end.
Fixpoint holds {n} (A : Relational.formula n) (env : Fin n -> point) : Prop :=
  match A with
  | Relational.equal t u => eval t env = eval u env
  | Relational.less_equal t u => order (eval t env) (eval u env)
  | Relational.add_graph t u v => add_graph (eval t env) (eval u env) (eval v env)
  | Relational.mul_graph t u v => mul_graph (eval t env) (eval u env) (eval v env)
  | Relational.falsity => False
  | Relational.implies B C => holds B env -> holds C env
  | Relational.all B => forall x, holds B (extend env x)
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
  - assert (HE : forall x, holds A (extend env x) <-> holds A (extend env' x)).
    { intro x. apply IHA. intro i. dependent elimination i; [reflexivity |apply H]. }
    split; intros HA x; apply HE; apply HA.
Qed.
Lemma eval_rename {m n} t (f : Fin m -> Fin n) env :
  eval (Relational.trename f t) env = eval t (fun i => env (f i)).
Proof. induction t; cbn [Relational.trename eval]; congruence. Qed.
Lemma eval_subst {m n} t (f : Fin m -> Relational.term n) env :
  eval (Relational.tsubst f t) env = eval t (fun i => eval (f i) env).
Proof. induction t; cbn [Relational.tsubst eval]; congruence. Qed.
Lemma holds_rename {m} A : forall n (f : Fin m -> Fin n) env,
  holds (Relational.frename f A) env <-> holds A (fun i => env (f i)).
Proof.
  induction A; intros k f env; cbn [Relational.frename holds]; try (rewrite !eval_rename; reflexivity).
  - reflexivity.
  - rewrite IHA1, IHA2. reflexivity.
  - assert (HE : forall x,
      holds (Relational.frename (weak f) A) (extend env x) <->
      holds A (extend (fun i => env (f i)) x)).
    { intro x. rewrite IHA. apply holds_ext. intro i. dependent elimination i; reflexivity. }
    split; intros HA x; apply HE; apply HA.
Qed.
Lemma holds_subst {m} A : forall n (f : Fin m -> Relational.term n) env,
  holds (Relational.fsubst f A) env <-> holds A (fun i => eval (f i) env).
Proof.
  induction A; intros k f env; cbn [Relational.fsubst holds]; try (rewrite !eval_subst; reflexivity).
  - reflexivity.
  - rewrite IHA1, IHA2. reflexivity.
  - assert (HE : forall x,
      holds (Relational.fsubst (Relational.lift_sub f) A) (extend env x) <->
      holds A (extend (fun i => eval (f i) env) x)).
    { intro x. rewrite IHA. apply holds_ext. intro i. dependent elimination i; [reflexivity |].
      cbn [Relational.lift_sub fin_match]. rewrite eval_rename. reflexivity. }
    split; intros HA x; apply HE; apply HA.
Qed.
Lemma holds_instance {n} A t (env : Fin n -> point) :
  holds (Relational.instantiate A t) env <-> holds A (extend env (eval t env)).
Proof.
  unfold Relational.instantiate. rewrite holds_subst. apply holds_ext.
  intro i. dependent elimination i; reflexivity.
Qed.
Lemma point_dec (x y : point) : {x = y} + {x <> y}.
Proof. decide equality. apply Nat.eq_dec. Qed.
Lemma order_dec x y : {order x y} + {~ order x y}.
Proof. destruct x as [m|], y as [n|]; cbn [order]; try tauto. apply le_dec. Qed.
Lemma decidable_stable (P : Prop) : {P} + {~ P} -> (~ ~ P -> P).
Proof. intros [H|H] Hnn; tauto. Qed.
Theorem holds_stable {n} (A : Relational.formula n) : forall env, ~ ~ holds A env -> holds A env.
Proof.
  induction A; intro env; cbn [holds].
  - apply decidable_stable, point_dec.
  - apply decidable_stable, order_dec.
  - apply decidable_stable, point_dec.
  - apply decidable_stable, point_dec.
  - tauto.
  - intros H HA. apply IHA2. intro Hn. apply H. intro Hf. apply Hn, Hf, HA.
  - intros H x. apply IHA. intro Hn. apply H. intro Hf. apply Hn, Hf.
Qed.
Lemma eval_numeral {n} v (env : Fin n -> point) : eval (Relational.numeral v) env = numeral v.
Proof. induction v; cbn [Relational.numeral eval numeral]; congruence. Qed.
Lemma iff_intro {n} A B (env : Fin n -> point) :
  (holds A env <-> holds B env) -> holds (Relational.iff A B) env.
Proof. cbn [Relational.iff Relational.conj Relational.neg holds]. tauto. Qed.
Lemma disj_intro {n} xs A (env : Fin n -> point) :
  In A xs -> holds A env -> holds (Relational.disj xs) env.
Proof.
  induction xs as [|B xs IH]; cbn [In Relational.disj fold_right holds Relational.neg];
    [contradiction |]. intros [<-|HA] H Hn; [contradiction |apply IH; assumption].
Qed.
Lemma disj_refute {n} xs (env : Fin n -> point) :
  (forall A, In A xs -> ~ holds A env) -> ~ holds (Relational.disj xs) env.
Proof.
  induction xs as [|B xs IH]; cbn [Relational.disj fold_right holds Relational.neg]; [tauto |].
  intros H HD. apply IH; [intros A HA; apply H; right; exact HA |].
  apply HD, H. left. reflexivity.
Qed.
Lemma disj_eliminate {n} xs (env : Fin n -> point) (P : Prop) :
  (~ ~ P -> P) -> (forall A, In A xs -> holds A env -> P) ->
  holds (Relational.disj xs) env -> P.
Proof.
  intros HS H HD. apply HS. intro Hn. apply (disj_refute xs env); [|exact HD].
  intros A HA HP. apply Hn, (H A HA), HP.
Qed.
Theorem axiom_sound {n} (A : Relational.formula n) : Relational.axiom A -> forall env, holds A env.
Proof.
  intro H. destruct H; intro env.
  - intro x. apply iff_intro. cbn [holds eval]. rewrite !eval_numeral. apply ground_add_graph.
  - intro x. apply iff_intro. cbn [holds eval]. rewrite !eval_numeral. apply ground_mul_graph.
  - cbn [Relational.neg holds]. rewrite !eval_numeral. apply distinct. assumption.
  - intro x. apply iff_intro. split.
    + cbn [holds eval]. rewrite eval_numeral. intro Horder.
      apply bounded in Horder. destruct Horder as [i [Hi Heq]].
      eapply disj_intro with (A:=Relational.equal (Relational.variable fzero) (Relational.numeral i)).
      * apply in_map_iff. exists i. split; [reflexivity |apply in_seq; lia].
      * cbn [holds eval extend fin_match]. rewrite eval_numeral. exact Heq.
    + intro HD. refine (disj_eliminate _ _ _ _ _ HD).
      * apply decidable_stable, order_dec.
      * intros B HB HE. apply in_map_iff in HB. destruct HB as [i [<- Hi]].
        cbn [holds eval extend fin_match] in HE |- *. rewrite !eval_numeral in HE |- *.
        apply bounded. exists i. split; [apply in_seq in Hi; lia |exact HE].
  - intro x. destruct (comparable k x) as [Hleft|Hright].
    + eapply disj_intro; [left; reflexivity |]. cbn [holds eval extend fin_match].
      rewrite eval_numeral. exact Hleft.
    + eapply disj_intro; [right; left; reflexivity |]. cbn [holds eval extend fin_match].
      rewrite eval_numeral. exact Hright.
Qed.
Theorem soundness {n} Ξ (A : Relational.formula n) : Relational.derives Ξ A ->
  forall env, (forall B, In B Ξ -> holds B env) -> holds A env.
Proof.
  intro HD. induction HD; intros env Hctx.
  - apply Hctx. exact H.
  - apply axiom_sound. exact H.
  - cbn [holds]. intro HA. apply IHHD. intros C [<-|HC]; [exact HA |apply Hctx; exact HC].
  - exact (IHHD1 env Hctx (IHHD2 env Hctx)).
  - intro x. apply IHHD. intros C HC. apply in_map_iff in HC. destruct HC as [B [<- HB]].
    apply holds_rename. change (holds B env). apply Hctx. exact HB.
  - apply holds_instance. exact (IHHD env Hctx (eval t env)).
  - apply holds_stable. exact (IHHD env Hctx).
  - reflexivity.
  - apply holds_instance.
    specialize (IHHD1 env Hctx). cbn [holds] in IHHD1.
    rewrite <- IHHD1. apply holds_instance. apply IHHD2. exact Hctx.
Qed.
Definition order_reflexivity_sentence : Relational.formula 0 :=
  Relational.all (Relational.less_equal (Relational.variable fzero) (Relational.variable fzero)).
Theorem order_reflexivity_underivable : ~ Relational.derives [] order_reflexivity_sentence.
Proof.
  intro H. pose proof (soundness [] _ H (fun i => match i with end)) as HM.
  assert (HC : forall B : Relational.formula 0, In B [] -> holds B (fun i => match i with end)).
  { intros B HB. contradiction. }
  exact (HM HC None).
Qed.
End RelationalCountermodel.
