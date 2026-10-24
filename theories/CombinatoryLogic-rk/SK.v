From Stdlib Require Import Arith.PeanoNat Lia.
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing Ranks Reduction
  Congruence AbstractRewriting DefEq Preservation.
From PTSrk.NormalizationComplexity Require Import Greedy.

(** Intrinsically simply typed SK compilation into the ORIGINAL annotated
    PTS. The input fragment has arbitrary simple types over U_i. No eta
    equation or primitive identity combinator is used. *)
Module SK.

Inductive Ty := ground | arrow (A B : Ty).
Infix "⇒" := arrow (at level 60, right associativity).
Fixpoint order (A : Ty) : nat :=
  match A with ground => 0 | A ⇒ B => Nat.max (S (order A)) (order B) end.
Fixpoint decode {n} (i : nat) (A : Ty) : Term nat n :=
  match A with ground => 𝓤 i | A ⇒ B => Π (decode i A) (decode i B) end.

Lemma decode_rename i A : forall n m (rho : Fin n -> Fin m),
  rename rho (@decode n i A) = @decode m i A.
Proof. induction A; intros; cbn [decode rename]; congruence. Qed.
Lemma decode_replace i A : forall n m (rho : Fin n -> Term nat m),
  replace rho (@decode n i A) = @decode m i A.
Proof. induction A; intros; cbn [decode replace]; congruence. Qed.
Lemma decode_sorted i A : forall n (G : Ctx nat n),
  @typ nat RankSorts n G (decode i A) (𝓤 (order A)).
Proof.
  induction A; intros; cbn [decode order].
  - constructor; reflexivity.
  - eapply typ_Π; [apply IHA1 | apply IHA2 | reflexivity].
Qed.
Lemma decode_app {n} (G : Ctx nat n) i A B f x :
  @typ nat RankSorts n G f (decode i (A ⇒ B)) ->
  @typ nat RankSorts n G x (decode i A) ->
  @typ nat RankSorts n G (f $ x) (decode i B).
Proof.
  intros Hf Hx. rewrite <- (@decode_replace i B (S n) n
    (fin_match x (fun j => var j))). eapply typ_app; eassumption.
Qed.

(** V records free variables, with their simple types. Closed codes use
    the empty family. The only combinator atoms are s and k. *)
Inductive Code (V : Ty -> Type) : Ty -> Type :=
| s {A B D} : Code V ((A ⇒ B ⇒ D) ⇒ (A ⇒ B) ⇒ A ⇒ D)
| k {A B} : Code V (A ⇒ B ⇒ A)
| cv {A} : V A -> Code V A
| ap {A B} : Code V (A ⇒ B) -> Code V A -> Code V B.
Arguments s {V A B D}.
Arguments k {V A B}.
Arguments cv {V A} _.
Arguments ap {V A B} _ _.
Infix "·" := ap (at level 40, left associativity).

Definition identity {V A} : Code V (A ⇒ A) :=
  @s V A (A ⇒ A) A · @k V A (A ⇒ A) · @k V A A.

Local Abbreviation v0 := (var fzero).
Local Abbreviation v1 := (var (fsucc fzero)).
Local Abbreviation v2 := (var (fsucc (fsucc fzero))).

Fixpoint expand {V A n} i (p : Code V A)
    (rho : forall B, V B -> Term nat n) : Term nat n :=
  match p with
  | @s _ A B D => lam (decode i (A ⇒ B ⇒ D))
      (lam (decode i (A ⇒ B)) (lam (decode i A) (v2 $ v0 $ (v1 $ v0))))
  | @k _ A B => lam (decode i A) (lam (decode i B) v1)
  | cv x => rho _ x
  | ap f x => expand i f rho $ expand i x rho
  end.

Lemma expand_rename {V A} i (p : Code V A) :
  forall n m (ren : Fin n -> Fin m) rho,
  rename ren (expand i p rho) =
  expand i p (fun B x => rename ren (rho B x)).
Proof.
  induction p; intros; cbn [expand rename weak fin_match];
    rewrite ?decode_rename; try reflexivity.
  now rewrite IHp1, IHp2.
Qed.
Lemma expand_ext {V A n} i (p : Code V A) rho sigma :
  (forall B x, rho B x = sigma B x) ->
  @expand V A n i p rho = expand i p sigma.
Proof. intro H; induction p; cbn [expand]; congruence. Qed.
Lemma expand_replace {V A} i (p : Code V A) :
  forall n m (sigma : Fin n -> Term nat m) rho,
  replace sigma (expand i p rho) =
  expand i p (fun B x => replace sigma (rho B x)).
Proof.
  induction p; intros; cbn [expand replace transpose shift rename weak fin_match];
    rewrite ?decode_replace, ?decode_rename; try reflexivity.
  now rewrite IHp1, IHp2.
Qed.

Lemma replace_variables {m n} (ren : Fin m -> Fin n) (t : Term nat m) :
  replace (fun j => var (ren j)) t = rename ren t.
Proof.
  revert n ren; induction t; intros; cbn [replace rename]; try congruence.
  - f_equal; [apply IHt1 |].
    transitivity (replace (fun j => var (weak ren j)) t2).
    + apply replace_ext. intro j; dependent elimination j; reflexivity.
    + apply IHt2.
  - f_equal; [apply IHt1 |].
    transitivity (replace (fun j => var (weak ren j)) t2).
    + apply replace_ext. intro j; dependent elimination j; reflexivity.
    + apply IHt2.
  - now rewrite IHt1, IHt2.
Qed.

Local Ltac native_var :=
  lazymatch goal with
  | |- @typ _ _ _ ?G (var ?j) _ =>
      let H := fresh in pose proof (@typ_var nat RankSorts _ G j) as H;
      cbn in H; unfold shift in H; cbn in H;
      rewrite ?decode_rename in H; exact H
  end.

Theorem expansion_typed {V A} (p : Code V A) : forall n (G : Ctx nat n) i rho,
  (forall B x, @typ nat RankSorts n G (rho B x) (decode i B)) ->
  @typ nat RankSorts n G (expand i p rho) (decode i A).
Proof.
  induction p; intros n G i rho HE; cbn [expand].
  - eapply typ_λ; [apply decode_sorted |].
    eapply typ_λ; [apply decode_sorted |].
    eapply typ_λ; [apply decode_sorted |].
    eapply decode_app; [eapply decode_app; native_var |].
    eapply decode_app; native_var.
  - eapply typ_λ; [apply decode_sorted |].
    eapply typ_λ; [apply decode_sorted |]. native_var.
  - apply HE.
  - eapply decode_app; [apply IHp1 | apply IHp2]; exact HE.
Qed.

(** A new typed variable. This family is an index, not a new PTS atom. *)
Inductive Extend (V : Ty -> Type) (A : Ty) : Ty -> Type :=
| here : Extend V A A
| there {B} : V B -> Extend V A B.
Arguments here {V A}.
Arguments there {V A B} _.

Fixpoint abstract {V A B} (p : Code (Extend V A) B) : Code V (A ⇒ B) :=
  match p with
  | s => k · s
  | k => k · k
  | cv x => match x with here => identity | there y => k · cv y end
  | ap f x => s · abstract f · abstract x
  end.

Definition extend_env {V A n} (rho : forall B, V B -> Term nat n)
    B (x : Extend V A B) : Term nat (S n) :=
  match x with here => v0 | there y => shift (rho _ y) end.

Definition plug_env {V A n} (rho : forall B, V B -> Term nat n)
    (a : Term nat n) B (x : Extend V A B) : Term nat n :=
  match x with here => a | there y => rho _ y end.

Local Ltac some_beta :=
  lazymatch goal with
  | |- step _ _ (app (lam _ _) _) _ => apply step_beta
  | |- step _ _ (app _ _) _ =>
      first [apply step_app_left; some_beta | apply step_app_right; some_beta]
  | |- step _ _ (lam _ _) _ => apply step_lam_right; some_beta
  end.
Local Ltac compute_beta :=
  eapply rtc_step; [some_beta | cbn; unfold shift, subst; cbn;
    rewrite ?decode_rename, ?decode_replace;
    autorewrite with syntax].

Theorem abstract_applied {V A B} (p : Code (Extend V A) B) : forall n i rho a,
  @expand V (A ⇒ B) n i (abstract p) rho $ a ↠ᵝ
  expand i p (plug_env rho a).
Proof.
  induction p; intros; cbn [abstract expand plug_env].
  - repeat compute_beta. reflexivity.
  - repeat compute_beta. reflexivity.
  - destruct v; cbn [abstract identity expand plug_env].
    + repeat compute_beta. reflexivity.
    + repeat compute_beta. reflexivity.
  - repeat compute_beta.
    eapply (app_cong_par nat (fun n => reduces_to nat n)); [apply IHp1 | apply IHp2].
Qed.

Theorem abstract_correct {V A B} (p : Code (Extend V A) B) : forall n i rho,
  @expand V (A ⇒ B) n i (abstract p) rho ↠ᵝ
  lam (decode i A) (expand i p (extend_env rho)).
Proof.
  destruct p as [X Y Z | X Y | X x | X Y f x]; intros; cbn [abstract expand].
  - compute_beta. reflexivity.
  - compute_beta. reflexivity.
  - destruct x; cbn [abstract identity expand extend_env].
    + repeat compute_beta. reflexivity.
    + compute_beta. reflexivity.
  - repeat compute_beta.
    cbn [transpose fin_match shift rename]. cbn.
    rewrite replace_variables.
    autorewrite with syntax.
    rewrite !expand_rename.
    fold (reduces_to nat n).
    apply λ_cong_r.
    change (expand i (abstract f) (fun B x => shift (rho B x)) $ v0 $
      (expand i (abstract x) (fun B x => shift (rho B x)) $ v0) ↠ᵝ
      expand i f (plug_env (fun B x => shift (rho B x)) v0) $
      expand i x (plug_env (fun B x => shift (rho B x)) v0)).
    eapply (app_cong_par nat (fun n => reduces_to nat n)); apply abstract_applied.
Qed.

(* BEGINSKCOMPILER *)
(** Intrinsic Church syntax. Lambda annotations are simple types; their
    decoded annotations are retained literally in the original PTS. *)
Inductive Source : (Ty -> Type) -> Ty -> Type :=
| source_var {V A} : V A -> Source V A
| source_app {V A B} : Source V (A ⇒ B) -> Source V A -> Source V B
| source_lam {V A B} : Source (Extend V A) B -> Source V (A ⇒ B).

Fixpoint compile {V A} (t : Source V A) : Code V A :=
  match t with
  | source_var x => cv x
  | source_app f x => compile f · compile x
  | source_lam b => abstract (compile b)
  end.

Fixpoint source_expand {V A n} (i : nat) (t : Source V A)
    (rho : forall B, V B -> Term nat n) : Term nat n :=
  match t in Source W _ return (forall B, W B -> Term nat n) -> Term nat n with
  | source_var x => fun rho => rho _ x
  | source_app f x => fun rho => source_expand i f rho $ source_expand i x rho
  | @source_lam _ A _ b => fun rho =>
      lam (decode i A) (source_expand i b (extend_env rho))
  end rho.

Theorem compile_correct {V A} (t : Source V A) : forall n i rho,
  @expand V A n i (compile t) rho ↠ᵝ source_expand i t rho.
Proof.
  induction t; intros; cbn [compile source_expand expand].
  - reflexivity.
  - eapply (app_cong_par nat (fun n => reduces_to nat n)); auto.
  - transitivity (lam (decode i A) (expand i (compile t) (extend_env rho))).
    + apply abstract_correct.
    + apply λ_cong_r, IHt.
Qed.

Theorem compile_typed {V A} (t : Source V A) n (G : Ctx nat n) i rho :
  (forall B x, @typ nat RankSorts n G (rho B x) (decode i B)) ->
  @typ nat RankSorts n G (expand i (compile t) rho) (decode i A).
Proof. apply expansion_typed. Qed.
(* ENDSKCOMPILER *)

Lemma extend_env_typed {V : Ty -> Type} {A n} (G : Ctx nat n) i
    (rho : forall B, V B -> Term nat n) :
  (forall B x, @typ nat RankSorts n G (rho B x) (decode i B)) ->
  forall B (x : Extend V A B), @typ nat RankSorts (S n) (G & decode i A)
    (extend_env rho B x) (decode i B).
Proof.
  intros HE B x; destruct x; cbn [extend_env].
  - native_var.
  - rewrite <- (@decode_rename i B n (S n) fsucc).
    apply weakening, HE.
Qed.
Theorem source_typed {V A} (t : Source V A) : forall n (G : Ctx nat n) i rho,
  (forall B x, @typ nat RankSorts n G (rho B x) (decode i B)) ->
  @typ nat RankSorts n G (source_expand i t rho) (decode i A).
Proof.
  induction t; intros n G i rho HE; cbn [source_expand].
  - apply HE.
  - eapply decode_app; [apply IHt1 | apply IHt2]; exact HE.
  - eapply typ_λ; [apply decode_sorted |].
    apply IHt, extend_env_typed, HE.
Qed.

(** Correctness is by forward beta only. Consequently normal native inputs
    have a beta-faithful SK representation; no eta quotient is involved. *)
Lemma reduces_equiv {n} (t u : Term nat n) : t ↠ᵝ u -> t =ᵝ u.
Proof. intro H; induction H; [reflexivity |]. transitivity y; auto. apply eq_in; exact H. Qed.

Theorem compilation_conversion_iff {V A B n} i
    (t : Source V A) (u : Source V B) rho :
  @expand V A n i (compile t) rho =ᵝ expand i (compile u) rho <->
  source_expand i t rho =ᵝ source_expand i u rho.
Proof.
  pose proof (reduces_equiv _ _ (compile_correct t n i rho)) as Ht.
  pose proof (reduces_equiv _ _ (compile_correct u n i rho)) as Hu.
  split; intro H.
  - transitivity (expand i (compile t) rho); [symmetry; exact Ht |].
    transitivity (expand i (compile u) rho); assumption.
  - transitivity (source_expand i t rho); [exact Ht |].
    transitivity (source_expand i u rho); [exact H | symmetry; exact Hu].
Qed.

Lemma normal_reduces_equal {n} (t u : Term nat n) :
  normalb t = true -> t ↠ᵝ u -> t = u.
Proof.
  intros HN HR. inversion HR; subst; [reflexivity |].
  exfalso; eapply normalb_sound; eassumption.
Qed.

Theorem normal_compilation_faithful {V A B n} i
    (t : Source V A) (u : Source V B) rho :
  normalb (@source_expand V A n i t rho) = true ->
  normalb (source_expand i u rho) = true ->
  (expand i (compile t) rho =ᵝ expand i (compile u) rho <->
   source_expand i t rho = source_expand i u rho).
Proof.
  intros Ht Hu. rewrite compilation_conversion_iff. split.
  - intro H. apply def_equiv_prop in H as [v [Htv Huv]].
    transitivity v; [eapply normal_reduces_equal; eassumption |].
    symmetry; eapply normal_reduces_equal; eassumption.
  - intro H; rewrite H; reflexivity.
Qed.

Fixpoint atoms {V A} (p : Code V A) : nat :=
  match p with s | k => 1 | cv _ => 0 | ap f x => atoms f + atoms x end.
Definition E := ground ⇒ ground.
Definition N := E ⇒ E.

(** A fixed nine-atom helper, not a third primitive combinator. *)
Definition helper {V} : Code V (E ⇒ E ⇒ E) :=
  s · (k · s) · (s · (k · k) · identity).
Definition zero {V} : Code V N := k · identity.
Definition successor {V} : Code V (N ⇒ N) := s · helper.
Fixpoint numeral {V} (j : nat) : Code V N :=
  match j with 0 => zero | S j => successor · numeral j end.

Theorem numeral_atoms V j : atoms (@numeral V j) = 10 * j + 4.
Proof. induction j; cbn [numeral successor helper zero identity atoms]; lia. Qed.
Theorem helper_successor_atoms V : atoms (@helper V) = 9 /\ atoms (@successor V) = 10.
Proof. split; reflexivity. Qed.
Theorem numeral_type_rank {n} (G : Ctx nat n) i :
  @typ nat RankSorts n G (decode i N) (𝓤 2).
Proof. apply decode_sorted. Qed.
Theorem arithmetic_type_ranks {n} (G : Ctx nat n) i :
  @typ nat RankSorts n G (decode i (N ⇒ N)) (𝓤 3) /\
  @typ nat RankSorts n G (decode i (N ⇒ N ⇒ N)) (𝓤 3).
Proof. split; apply decode_sorted. Qed.

Theorem successor_beta {V n} i rho (q f x : Term nat n) :
  expand i (@successor V) rho $ q $ f $ x ↠ᵝ f $ (q $ f $ x).
Proof.
  cbn [successor helper identity expand]. repeat compute_beta. reflexivity.
Qed.
Theorem zero_beta {V n} i rho (f x : Term nat n) :
  expand i (@zero V) rho $ f $ x ↠ᵝ x.
Proof. cbn [zero identity expand]. repeat compute_beta. reflexivity. Qed.
Fixpoint iterate {n} (j : nat) (f x : Term nat n) : Term nat n :=
  match j with 0 => x | S j => f $ iterate j f x end.
Theorem numeral_beta V j : forall n i rho (f x : Term nat n),
  expand i (@numeral V j) rho $ f $ x ↠ᵝ iterate j f x.
Proof.
  induction j; intros; cbn [numeral expand iterate].
  - apply zero_beta.
  - transitivity (f $ (expand i (numeral j) rho $ f $ x)).
    + apply successor_beta.
    + apply app_cong_r, IHj.
Qed.

Definition church_normal {n} i j : Term nat n :=
  lam (decode i E) (lam (𝓤 i) (iterate j v1 v0)).
Theorem numeral_expansion V j n i rho :
  @expand V N n i (numeral j) rho ↠ᵝ church_normal i j.
Proof.
  destruct j; cbn [numeral zero successor helper identity expand church_normal iterate].
  - repeat compute_beta. reflexivity.
  - repeat compute_beta. cbn [transpose fin_match shift rename]. cbn.
    rewrite ?replace_variables, ?expand_rename.
    fold (reduces_to nat n).
    apply λ_cong_r, λ_cong_r, app_cong_r.
    apply numeral_beta.
Qed.
Theorem church_normal_is_normal n i j : normalb (@church_normal n i j) = true.
Proof.
  cbn [church_normal E decode normalb].
  induction j; cbn in *; [reflexivity | now rewrite IHj].
Qed.

Definition addition_source {V} : Source V (N ⇒ N ⇒ N) :=
  source_lam (source_lam (source_lam (source_lam
    (source_app
      (source_app (source_var (there (there (there here)))) (source_var (there here)))
      (source_app (source_app (source_var (there (there here))) (source_var (there here)))
        (source_var here)))))).
Definition multiplication_source {V} : Source V (N ⇒ N ⇒ N) :=
  source_lam (source_lam (source_lam
    (source_app (source_var (there (there here)))
      (source_app (source_var (there here)) (source_var here))))).
Definition addition {V} : Code V (N ⇒ N ⇒ N) := compile addition_source.
Definition multiplication {V} : Code V (N ⇒ N ⇒ N) := compile multiplication_source.

(** These are the exact sizes for the deliberately unoptimized structural
    bracket compiler, not minimality claims. *)
Theorem arithmetic_atoms V : atoms (@addition V) = 414 /\ atoms (@multiplication V) = 81.
Proof. split; reflexivity. Qed.

Theorem addition_beta {V n} i rho (q r f x : Term nat n) :
  expand i (@addition V) rho $ q $ r $ f $ x ↠ᵝ q $ f $ (r $ f $ x).
Proof.
  transitivity (source_expand i (@addition_source V) rho $ q $ r $ f $ x).
  - apply app_cong_l, app_cong_l, app_cong_l, app_cong_l, compile_correct.
  - cbn [addition_source source_expand extend_env]. repeat compute_beta. reflexivity.
Qed.
Theorem multiplication_beta {V n} i rho (q r f : Term nat n) :
  expand i (@multiplication V) rho $ q $ r $ f ↠ᵝ q $ (r $ f).
Proof.
  transitivity (source_expand i (@multiplication_source V) rho $ q $ r $ f).
  - apply app_cong_l, app_cong_l, app_cong_l, compile_correct.
  - cbn [multiplication_source source_expand extend_env]. repeat compute_beta. reflexivity.
Qed.

Lemma iterate_right {n} j (f x y : Term nat n) :
  x ↠ᵝ y -> iterate j f x ↠ᵝ iterate j f y.
Proof. intro H; induction j; cbn [iterate]; [exact H | now apply app_cong_r]. Qed.
Lemma iterate_plus {n} j l (f x : Term nat n) :
  iterate j f (iterate l f x) = iterate (j + l) f x.
Proof. induction j; cbn [iterate Nat.add]; congruence. Qed.

Theorem successor_numeral {V n} i rho j (f x : Term nat n) :
  expand i (@successor V) rho $ expand i (numeral j) rho $ f $ x ↠ᵝ iterate (S j) f x.
Proof.
  transitivity (f $ (expand i (numeral j) rho $ f $ x)).
  - apply successor_beta.
  - apply app_cong_r, numeral_beta.
Qed.
Theorem addition_numerals {V n} i rho j l (f x : Term nat n) :
  expand i (@addition V) rho $ expand i (numeral j) rho $
    expand i (numeral l) rho $ f $ x ↠ᵝ iterate (j + l) f x.
Proof.
  transitivity (expand i (numeral j) rho $ f $ (expand i (numeral l) rho $ f $ x)).
  - apply addition_beta.
  - transitivity (iterate j f (expand i (numeral l) rho $ f $ x)).
    + apply numeral_beta.
    + rewrite <- iterate_plus. apply iterate_right, numeral_beta.
Qed.
Lemma iterate_numeral {V n} i rho j l (f x : Term nat n) :
  iterate j (expand i (@numeral V l) rho $ f) x ↠ᵝ iterate (j * l) f x.
Proof.
  induction j; cbn [iterate Nat.mul]; [reflexivity |].
  transitivity (iterate l f (iterate j (expand i (numeral l) rho $ f) x)).
  - apply numeral_beta.
  - rewrite <- iterate_plus. apply iterate_right, IHj.
Qed.
Theorem multiplication_numerals {V n} i rho j l (f x : Term nat n) :
  expand i (@multiplication V) rho $ expand i (numeral j) rho $
    expand i (numeral l) rho $ f $ x ↠ᵝ iterate (j * l) f x.
Proof.
  transitivity (expand i (numeral j) rho $ (expand i (numeral l) rho $ f) $ x).
  - apply app_cong_l, multiplication_beta.
  - transitivity (iterate j (expand i (numeral l) rho $ f) x).
    + apply numeral_beta.
    + apply iterate_numeral.
Qed.

Print Assumptions expansion_typed.
Print Assumptions abstract_applied.
Print Assumptions abstract_correct.
Print Assumptions compile_correct.
Print Assumptions compile_typed.
Print Assumptions source_typed.
Print Assumptions compilation_conversion_iff.
Print Assumptions normal_compilation_faithful.
Print Assumptions numeral_atoms.
Print Assumptions helper_successor_atoms.
Print Assumptions numeral_type_rank.
Print Assumptions arithmetic_type_ranks.
Print Assumptions successor_beta.
Print Assumptions zero_beta.
Print Assumptions numeral_beta.
Print Assumptions numeral_expansion.
Print Assumptions church_normal_is_normal.
Print Assumptions addition_beta.
Print Assumptions multiplication_beta.
Print Assumptions arithmetic_atoms.
Print Assumptions successor_numeral.
Print Assumptions addition_numerals.
Print Assumptions multiplication_numerals.

End SK.
