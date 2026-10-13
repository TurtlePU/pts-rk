From Stdlib Require Import Arith.PeanoNat Lia.
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing Preservation Ranks Reduction
  DefEq AbstractRewriting Congruence.
Require Import PTSrk.NormalizationComplexity.Bounds
  PTSrk.NormalizationComplexity.Greedy.

Module ChurchSTLC.

(** Checked embedding used by the manuscript's completeness argument.
    The STLC TOWER-hardness theorem of Nguyen (LMCS 20(3:21), 2024) is NOT
    formalized or assumed here. See README.md for the complexity boundary. *)
(** One ground type suffices for the cited STLC lower bound. The source
    reuses scoped de Bruijn syntax, but has INDEPENDENT simple typing and
    beta rules below. No PTS typing premise defines source typing. Type
    annotations are retained, not erased. The distinguished variable o is
    the ground type; ordinary source environments give it no term binding. *)
Inductive Ty := base | arrow (A B : Ty).
Fixpoint order (A : Ty) : nat :=
  match A with base => 0 | arrow A B => Nat.max (S (order A)) (order B) end.
Fixpoint code {n} (A : Ty) (o : Fin n) : Term nat n :=
  match A with base => var o | arrow A B => Π (code A o) (code B (fsucc o)) end.

Lemma code_rename A : forall m n (f : Fin m -> Fin n) o,
  rename f (code A o) = code A (f o).
Proof. induction A; intros; cbn [code rename]; [reflexivity |]. rewrite IHA1, IHA2; reflexivity. Qed.
Lemma code_replace A : forall m n (s : Fin m -> Term nat n) o p,
  s o = var p -> replace s (code A o) = code A p.
Proof.
  induction A; intros m n s o p H; cbn [code replace]; [exact H |].
  rewrite (IHA1 _ _ _ _ _ H). f_equal. apply IHA2.
  change (shift (s o) = var (fsucc p)). rewrite H; reflexivity.
Qed.
Lemma code_normal A : forall n (o : Fin n), normalb (code A o) = true.
Proof. induction A; intros; cbn [code normalb]; [reflexivity | rewrite IHA1, IHA2; reflexivity]. Qed.
Lemma code_typed A : forall n (G : Ctx nat n) o,
  @typ nat RankSorts n G (var o) (𝓤 0) ->
  @typ nat RankSorts n G (code A o) (𝓤 (order A)).
Proof.
  induction A; intros n G o Ho; cbn [code order]; [exact Ho |].
  eapply typ_Π; [apply IHA1; exact Ho | apply IHA2 | reflexivity].
  change (typ (G & code A1 o) (shift (var o)) (shift (𝓤 0))).
  apply weakening; exact Ho.
Qed.
Lemma code_subst A {n} (o : Fin n) (u : Term nat n) :
  subst (code A (fsucc o)) u = code A o.
Proof. apply code_replace; reflexivity. Qed.

Definition Env n := Fin n -> option Ty.
Definition extend {n} (E : Env n) A : Env (S n) := fin_match (Some A) E.
Inductive has_type : forall {n}, Env n -> Fin n -> Term nat n -> Ty -> Prop :=
| ty_var {n} E (o i : Fin n) A : E i = Some A -> has_type E o (var i) A
| ty_lam {n} E (o : Fin n) A B b :
    has_type (extend E A) (fsucc o) b B ->
    has_type E o (lam (code A o) b) (arrow A B)
| ty_app {n} E (o : Fin n) A B f u :
    has_type E o f (arrow A B) -> has_type E o u A ->
    has_type E o (app f u) B.

Definition EnvTyped {n} (G : Ctx nat n) (E : Env n) o :=
  forall i A, E i = Some A -> @typ nat RankSorts n G (var i) (code A o).
Theorem typing_preserved {n} E o (t : Term nat n) A :
  has_type E o t A -> forall G,
  @typ nat RankSorts n G (var o) (𝓤 0) -> EnvTyped G E o ->
  @typ nat RankSorts n G t (code A o).
Proof.
  intro H; induction H; intros G Ho HE.
  - apply HE; assumption.
  - cbn [code]. eapply typ_λ with (ℓ := order A).
    + apply code_typed; exact Ho.
    + apply IHhas_type.
      * change (typ (G & code A o) (shift (var o)) (shift (𝓤 0))). apply weakening; exact Ho.
      * intros i C HC. dependent elimination i; cbn [extend fin_match] in HC.
        -- inversion HC; subst C. rewrite <- (code_rename A _ _ fsucc o).
           change (typ (G & code A o) (var fzero) ((G & code A o) !! fzero)). constructor.
        -- rewrite <- (code_rename C _ _ fsucc o).
           change (typ (G & code A o) (shift (var f)) (shift (code C o))).
           apply weakening. apply HE; exact HC.
  - rewrite <- (code_subst B o u). eapply typ_app; eauto.
Qed.

(** Ordinary Church beta rules: no Pi rule and no reduction of annotations. *)
Inductive beta : forall {n}, Term nat n -> Term nat n -> Prop :=
| beta_lam {n} (A : Term nat n) b b' : beta b b' -> beta (lam A b) (lam A b')
| beta_left {n} (f f' u : Term nat n) : beta f f' -> beta (app f u) (app f' u)
| beta_right {n} (f u u' : Term nat n) : beta u u' -> beta (app f u) (app f u')
| beta_root {n} (A : Term nat n) b u : beta (app (lam A b) u) (subst b u).
Definition convertible {n} := EquivClosure (@beta n).

Inductive Shape : forall {n}, Fin n -> Term nat n -> Prop :=
| shape_var {n} (o i : Fin n) : Shape o (var i)
| shape_lam {n} (o : Fin n) A b : Shape (fsucc o) b -> Shape o (lam (code A o) b)
| shape_app {n} (o : Fin n) f u : Shape o f -> Shape o u -> Shape o (app f u).
Lemma typed_shape {n} E o (t : Term nat n) A : has_type E o t A -> Shape o t.
Proof. intro H; induction H; constructor; assumption. Qed.
Lemma shape_rename {m} o (t : Term nat m) : Shape o t ->
  forall n (f : Fin m -> Fin n), Shape (f o) (rename f t).
Proof.
  intro H; induction H; intros k ren; cbn [rename].
  - constructor.
  - rewrite code_rename. constructor. exact (IHShape _ (weak ren)).
  - constructor; [apply IHShape1 | apply IHShape2].
Qed.
Lemma shape_replace {m} o (t : Term nat m) : Shape o t ->
  forall n p (s : Fin m -> Term nat n),
  s o = var p -> (forall i, Shape p (s i)) -> Shape p (replace s t).
Proof.
  intro H; induction H; intros k p sigma Ho HI; cbn [replace].
  - apply HI.
  - rewrite (code_replace A _ _ _ _ _ Ho). constructor. apply IHShape.
    + change (shift (sigma o) = var (fsucc p)). rewrite Ho; reflexivity.
    + intro i; dependent elimination i; cbn [transpose fin_match].
      * constructor.
      * apply shape_rename, HI.
  - constructor; [eapply IHShape1 | eapply IHShape2]; eassumption.
Qed.
Lemma shape_subst {n} (o : Fin n) b u :
  Shape (fsucc o) b -> Shape o u -> Shape o (subst b u).
Proof.
  intros Hb Hu. eapply shape_replace; [exact Hb | reflexivity |].
  intro i; dependent elimination i; cbn [fin_match]; [exact Hu | constructor].
Qed.
Lemma beta_preserved {n} (t u : Term nat n) : beta t u -> step nat n t u.
Proof. intro H; induction H; constructor; assumption. Qed.

Theorem step_reflected {n} o (t : Term nat n) : Shape o t -> forall u,
  step nat n t u -> beta t u /\ Shape o u.
Proof.
  intro HS; induction HS; intros v HV; dependent elimination HV.
  - exfalso; eapply normalb_sound; [apply code_normal | eassumption].
  - match goal with H : step _ _ _ _ |- _ => destruct (IHHS _ H) as [Hstep Hshape] end.
    split; constructor; assumption.
  - match goal with H : step _ _ _ _ |- _ => destruct (IHHS1 _ H) as [Hstep Hshape] end.
    split; constructor; assumption.
  - match goal with H : step _ _ _ _ |- _ => destruct (IHHS2 _ H) as [Hstep Hshape] end.
    split; constructor; assumption.
  - split; [constructor |]. dependent elimination HS1. eapply shape_subst; eassumption.
Qed.
Lemma reduction_reflected {n} o (t u : Term nat n) :
  Shape o t -> reduces_to nat n t u -> RTC (@beta n) t u /\ Shape o u.
Proof.
  intros HS HR; induction HR; [split; [constructor | exact HS] |].
  destruct (step_reflected o x HS y H) as [Hxy HSy].
  destruct (IHHR HSy) as [Hyz HSz]. split; [eapply rtc_step; eassumption | exact HSz].
Qed.
Theorem conversion_preserved {n} (t u : Term nat n) :
  convertible t u -> def_equiv nat n t u.
Proof. apply eq_map, beta_preserved. Qed.
Theorem conversion_reflected {n} o (t u : Term nat n) :
  Shape o t -> Shape o u -> def_equiv nat n t u -> convertible t u.
Proof.
  intros Ht Hu HE. apply def_equiv_prop in HE as [v [Htv Huv]].
  destruct (reduction_reflected o t v Ht Htv) as [H1 _].
  destruct (reduction_reflected o u v Hu Huv) as [H2 _].
  assert (lift : forall x y : Term nat n, RTC (@beta n) x y -> convertible x y).
  { intros x y H; induction H; [reflexivity |]. transitivity y; [apply eq_in; exact H | exact IHRTC]. }
  transitivity v; [apply lift; exact H1 | symmetry; apply lift; exact H2].
Qed.

Definition emptyEnv : Env 1 := fun _ => None.
Definition close (t : Term nat 1) : Term nat 0 := lam (𝓤 0) t.
Theorem closed_typing t A : has_type emptyEnv fzero t A ->
  @typ nat RankSorts 0 ε (close t) (Π (𝓤 0) (code A fzero)).
Proof.
  intro H. unfold close. eapply typ_λ with (ℓ := 0); [constructor; reflexivity |].
  eapply typing_preserved; [exact H | |].
  - change (typ (ε & 𝓤 0) (var fzero) ((ε & 𝓤 0) !! fzero)). constructor.
  - intros i B HB; discriminate.
Qed.
Lemma close_reduction t v : reduces_to nat 0 (close t) v ->
  exists u, v = close u /\ reduces_to nat 1 t u.
Proof.
  intro H. remember (close t) as z eqn:Hz. revert t Hz.
  induction H; intros t E; subst x.
  - exists t; split; [reflexivity | constructor].
  - unfold close in H. dependent elimination H.
    + match goal with Hs : step _ _ (𝓤 _) _ |- _ => inversion Hs end.
    + destruct (IHRTC _ eq_refl) as [u [Eu HR]]. exists u; split; [exact Eu |].
      eapply rtc_step; eassumption.
Qed.
Theorem closed_conversion t u : Shape fzero t -> Shape fzero u ->
  (convertible t u <-> def_equiv nat 0 (close t) (close u)).
Proof.
  intros Ht Hu. split.
  - intro HE. unfold close. apply λ_cong_r. apply conversion_preserved; exact HE.
  - intro HE. apply def_equiv_prop in HE as [v [HtV HuV]].
    destruct (close_reduction _ _ HtV) as [t' [Et HRt]].
    destruct (close_reduction _ _ HuV) as [u' [Eu HRu]].
    assert (t' = u') by (rewrite Et in Eu; injection Eu; auto). subst u'.
    eapply conversion_reflected; [exact Ht | exact Hu |].
    apply def_equiv_prop. exists t'; auto.
Qed.

(** With explicit Church annotations counted in input size, the embedding
    retains the whole input and adds only the ground-type binder. *)
Theorem close_size t : encodingSize (close t) = encodingSize t + 2.
Proof. unfold close; cbn [encodingSize]; lia. Qed.
Theorem church_stlc_reduction t u A :
  has_type emptyEnv fzero t A -> has_type emptyEnv fzero u A ->
  @typ nat RankSorts 0 ε (close t) (Π (𝓤 0) (code A fzero)) /\
  @typ nat RankSorts 0 ε (close u) (Π (𝓤 0) (code A fzero)) /\
  (convertible t u <-> def_equiv nat 0 (close t) (close u)) /\
  encodingSize (close t) + encodingSize (close u) = encodingSize t + encodingSize u + 4.
Proof.
  intros Ht Hu. split; [apply closed_typing; exact Ht |].
  split; [apply closed_typing; exact Hu |]. split.
  - apply closed_conversion; eapply typed_shape; eassumption.
  - rewrite !close_size; lia.
Qed.
End ChurchSTLC.
