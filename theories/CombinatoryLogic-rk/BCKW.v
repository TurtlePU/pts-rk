From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import Syntax Context Typing Ranks Reduction
  Congruence AbstractRewriting.
From PTSrk.NormalizationComplexity Require Import Greedy.

(** Rank-typed BCKW(I), with original annotated PTS expansions. *)
Module BCKW.

Inductive Ty := ground | arrow (A B : Ty).
Abbreviation O := ground.
Infix "⇒" := arrow (at level 60, right associativity).
Fixpoint order (A : Ty) : nat :=
  match A with O => 0 | A ⇒ B => Nat.max (S (order A)) (order B) end.

Fixpoint decode {n} (i : nat) (A : Ty) : Term nat n :=
  match A with O => 𝓤 i | A ⇒ B => Π (decode i A) (decode i B) end.

Lemma decode_rename i A : forall n m (rho : Fin n -> Fin m),
  rename rho (@decode n i A) = @decode m i A.
Proof.
  induction A; intros; cbn [decode rename]; [reflexivity |].
  now rewrite IHA1, IHA2.
Qed.
Lemma decode_replace i A : forall n m (rho : Fin n -> Term nat m),
  replace rho (@decode n i A) = @decode m i A.
Proof.
  induction A; intros; cbn [decode replace]; [reflexivity |].
  now rewrite IHA1, IHA2.
Qed.
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

Inductive Code : Ty -> Type :=
| B {A D E} : Code ((D ⇒ E) ⇒ (A ⇒ D) ⇒ A ⇒ E)
| C {A D E} : Code ((A ⇒ D ⇒ E) ⇒ D ⇒ A ⇒ E)
| K {A D} : Code (A ⇒ D ⇒ A)
| W {A D} : Code ((A ⇒ A ⇒ D) ⇒ A ⇒ D)
| I {A} : Code (A ⇒ A)
| ap {A D} : Code (A ⇒ D) -> Code A -> Code D.
Infix "·" := ap (at level 40, left associativity).

Local Abbreviation v0 := (var fzero).
Local Abbreviation v1 := (var (fsucc fzero)).
Local Abbreviation v2 := (var (fsucc (fsucc fzero))).

Fixpoint expand {n A} (i : nat) (p : Code A) : Term nat n :=
  match p with
  | @B A D E => lam (decode i (D ⇒ E)) (lam (decode i (A ⇒ D))
      (lam (decode i A) (v2 $ (v1 $ v0))))
  | @C A D E => lam (decode i (A ⇒ D ⇒ E)) (lam (decode i D)
      (lam (decode i A) (v2 $ v0 $ v1)))
  | @K A D => lam (decode i A) (lam (decode i D) v1)
  | @W A D => lam (decode i (A ⇒ A ⇒ D)) (lam (decode i A)
      (v1 $ v0 $ v0))
  | @I A => lam (decode i A) v0
  | ap f x => expand i f $ expand i x
  end.

Lemma expand_rename {A} i (p : Code A) :
  forall n m (rho : Fin n -> Fin m),
  rename rho (@expand n A i p) = @expand m A i p.
Proof.
  induction p; intros; cbn [expand rename weak fin_match];
    rewrite ?decode_rename; try reflexivity.
  now rewrite IHp1, IHp2.
Qed.
Lemma expand_replace {A} i (p : Code A) :
  forall n m (rho : Fin n -> Term nat m),
  replace rho (@expand n A i p) = @expand m A i p.
Proof.
  induction p; intros; cbn [expand replace transpose shift rename weak fin_match];
    rewrite ?decode_replace, ?decode_rename; try reflexivity.
  now rewrite IHp1, IHp2.
Qed.

Local Ltac native_var :=
  lazymatch goal with
  | |- @typ _ _ _ ?G (var ?j) _ =>
      let H := fresh in pose proof (@typ_var nat RankSorts _ G j) as H;
      cbn in H; unfold shift in H; cbn in H;
      rewrite ?decode_rename in H; exact H
  end.

Theorem expansion_typed {A} (p : Code A) : forall n (G : Ctx nat n) i,
  @typ nat RankSorts n G (expand i p) (decode i A).
Proof.
  induction p; intros; cbn [expand].
  - eapply typ_λ; [apply decode_sorted |].
    eapply typ_λ; [apply decode_sorted |].
    eapply typ_λ; [apply decode_sorted |].
    eapply decode_app; [native_var |]. eapply decode_app; native_var.
  - eapply typ_λ; [apply decode_sorted |].
    eapply typ_λ; [apply decode_sorted |].
    eapply typ_λ; [apply decode_sorted |].
    eapply decode_app; [eapply decode_app |]; native_var.
  - eapply typ_λ; [apply decode_sorted |].
    eapply typ_λ; [apply decode_sorted |]. native_var.
  - eapply typ_λ; [apply decode_sorted |].
    eapply typ_λ; [apply decode_sorted |].
    eapply decode_app; [eapply decode_app |]; native_var.
  - eapply typ_λ; [apply decode_sorted |]. native_var.
  - eapply decode_app; [apply IHp1 | apply IHp2].
Qed.

Fixpoint duplications {A} (p : Code A) : nat :=
  match p with W => 1 | ap f x => duplications f + duplications x | _ => 0 end.
Fixpoint atoms {A} (p : Code A) : nat :=
  match p with ap f x => atoms f + atoms x | _ => 1 end.

Definition E := O ⇒ O.
Definition N := E ⇒ E.
Definition F := E ⇒ E ⇒ E.
Definition H : Code (N ⇒ F) := C · (B · B · (C · B)) · B.
Definition zero : Code N := K · I.
Definition successor : Code (N ⇒ N) := B · W · H.
Definition addition : Code (N ⇒ N ⇒ N) :=
  B · (B · (B · W) · (B · B · C)) · (B · B).
Definition multiplication : Code (N ⇒ N ⇒ N) := B.

(** The ground carrier U_i has rank zero; its endomorphisms have rank one,
    Church numerals rank two, and the arithmetic operator types rank three.
    Every simple-type index used below has fixed size independent of k. *)
Theorem numeral_type_rank {n} (G : Ctx nat n) i :
  @typ nat RankSorts n G (decode i N) (𝓤 2).
Proof. apply decode_sorted. Qed.
Theorem arithmetic_type_ranks {n} (G : Ctx nat n) i :
  @typ nat RankSorts n G (decode i (N ⇒ N)) (𝓤 3) /\
  @typ nat RankSorts n G (decode i (N ⇒ N ⇒ N)) (𝓤 3).
Proof. split; apply decode_sorted. Qed.
Theorem arithmetic_counts :
  atoms successor = 8 /\ atoms addition = 9 /\ atoms multiplication = 1 /\
  duplications successor = 1 /\ duplications addition = 1 /\
  duplications multiplication = 0.
Proof. repeat split; reflexivity. Qed.

Fixpoint numeral (k : nat) : Code N :=
  match k with 0 => zero | S k => W · (H · numeral k) end.

Theorem numeral_duplications k : duplications (numeral k) = k.
Proof. induction k; cbn [numeral duplications H zero]; lia. Qed.
Theorem numeral_atoms k : atoms (numeral k) = 7 * k + 2.
Proof. induction k; cbn [numeral atoms H zero]; lia. Qed.
Theorem numeral_typed {n} (G : Ctx nat n) i k :
  @typ nat RankSorts n G (expand i (numeral k)) (decode i N).
Proof. apply expansion_typed. Qed.
Theorem arithmetic_typed {n} (G : Ctx nat n) i :
  @typ nat RankSorts n G (expand i successor) (decode i (N ⇒ N)) /\
  @typ nat RankSorts n G (expand i addition) (decode i (N ⇒ N ⇒ N)) /\
  @typ nat RankSorts n G (expand i multiplication) (decode i (N ⇒ N ⇒ N)).
Proof. repeat split; apply expansion_typed. Qed.

Local Ltac head_beta :=
  first [apply step_beta | apply step_app_left; head_beta].
Local Ltac compute_head :=
  eapply rtc_step; [head_beta | cbn; unfold shift, subst; cbn;
    rewrite ?decode_rename, ?decode_replace;
    autorewrite with syntax].

Lemma B_beta {n} i A D E (f g x : Term nat n) :
  expand i (@B A D E) $ f $ g $ x ↠ᵝ f $ (g $ x).
Proof. cbn [expand]. do 3 compute_head. reflexivity. Qed.
Lemma C_beta {n} i A D E (f x y : Term nat n) :
  expand i (@C A D E) $ f $ x $ y ↠ᵝ f $ y $ x.
Proof. cbn [expand]. do 3 compute_head. reflexivity. Qed.
Lemma K_beta {n} i A D (x y : Term nat n) :
  expand i (@K A D) $ x $ y ↠ᵝ x.
Proof. cbn [expand]. do 2 compute_head. reflexivity. Qed.
Lemma W_beta {n} i A D (f x : Term nat n) :
  expand i (@W A D) $ f $ x ↠ᵝ f $ x $ x.
Proof. cbn [expand]. do 2 compute_head. reflexivity. Qed.
Lemma I_beta {n} i A (x : Term nat n) :
  expand i (@I A) $ x ↠ᵝ x.
Proof. cbn [expand]. compute_head. reflexivity. Qed.

Local Ltac some_beta :=
  lazymatch goal with
  | |- step _ _ (app (lam _ _) _) _ => apply step_beta
  | |- step _ _ (app _ _) _ =>
      first [apply step_app_left; some_beta | apply step_app_right; some_beta]
  | |- step _ _ (lam _ _) _ => apply step_lam_right; some_beta
  end.
Local Ltac compute_beta :=
  eapply rtc_step; [some_beta | cbn; unfold shift, subst; cbn;
    rewrite ?decode_rename, ?decode_replace, ?expand_rename, ?expand_replace;
    autorewrite with syntax].

Theorem H_beta {n} i (k f g x : Term nat n) :
  expand i H $ k $ f $ g $ x ↠ᵝ f $ (k $ g $ x).
Proof. cbn [H expand]. repeat compute_beta. reflexivity. Qed.
Theorem zero_beta {n} i (f x : Term nat n) :
  expand i zero $ f $ x ↠ᵝ x.
Proof. cbn [zero expand]. repeat compute_beta. reflexivity. Qed.
Theorem successor_beta {n} i (k f x : Term nat n) :
  expand i successor $ k $ f $ x ↠ᵝ f $ (k $ f $ x).
Proof. cbn [successor H expand]. repeat compute_beta. reflexivity. Qed.
Theorem addition_beta {n} i (k l f x : Term nat n) :
  expand i addition $ k $ l $ f $ x ↠ᵝ k $ f $ (l $ f $ x).
Proof. cbn [addition expand]. repeat compute_beta. reflexivity. Qed.
Theorem multiplication_beta {n} i (k l f : Term nat n) :
  expand i multiplication $ k $ l $ f ↠ᵝ k $ (l $ f).
Proof. apply B_beta. Qed.

Fixpoint iterate {n} (k : nat) (f x : Term nat n) : Term nat n :=
  match k with 0 => x | S k => f $ iterate k f x end.
Theorem numeral_beta k : forall n i (f x : Term nat n),
  expand i (numeral k) $ f $ x ↠ᵝ iterate k f x.
Proof.
  induction k; intros; cbn [numeral expand iterate].
  - apply zero_beta.
  - transitivity (expand i H $ expand i (numeral k) $ f $ f $ x).
    + apply app_cong_l. apply W_beta.
    + transitivity (f $ (expand i (numeral k) $ f $ x)).
      * apply H_beta.
      * apply app_cong_r. apply IHk.
Qed.

Definition church_normal {n} i k : Term nat n :=
  lam (decode i E) (lam (𝓤 i) (iterate k v1 v0)).
Theorem numeral_expansion k n i :
  @expand n N i (numeral k) ↠ᵝ church_normal i k.
Proof.
  destruct k; cbn [numeral zero H expand church_normal iterate].
  - repeat compute_beta. reflexivity.
  - repeat compute_beta. fold (reduces_to nat n).
    apply λ_cong_r, λ_cong_r, app_cong_r.
    apply numeral_beta.
Qed.
Theorem church_normal_is_normal n i k :
  forall u, ~ step nat n (church_normal i k) u.
Proof.
  apply normalb_sound. cbn [church_normal E decode normalb].
  induction k; cbn in *; [reflexivity | now rewrite IHk].
Qed.

Lemma iterate_right {n} k (f x y : Term nat n) :
  x ↠ᵝ y -> iterate k f x ↠ᵝ iterate k f y.
Proof. intro R; induction k; cbn [iterate]; [exact R | now apply app_cong_r]. Qed.
Lemma iterate_plus {n} k l (f x : Term nat n) :
  iterate k f (iterate l f x) = iterate (k + l) f x.
Proof. induction k; cbn [iterate Nat.add]; congruence. Qed.

Theorem successor_numeral {n} i k (f x : Term nat n) :
  expand i successor $ expand i (numeral k) $ f $ x ↠ᵝ
  iterate (S k) f x.
Proof.
  transitivity (f $ (expand i (numeral k) $ f $ x)).
  - apply successor_beta.
  - apply app_cong_r, numeral_beta.
Qed.
Theorem addition_numerals {n} i k l (f x : Term nat n) :
  expand i addition $ expand i (numeral k) $ expand i (numeral l) $ f $ x ↠ᵝ
  iterate (k + l) f x.
Proof.
  transitivity (expand i (numeral k) $ f $ (expand i (numeral l) $ f $ x)).
  - apply addition_beta.
  - transitivity (iterate k f (expand i (numeral l) $ f $ x)).
    + apply numeral_beta.
    + rewrite <- iterate_plus. apply iterate_right, numeral_beta.
Qed.
Lemma iterate_numeral {n} i k l (f x : Term nat n) :
  iterate k (expand i (numeral l) $ f) x ↠ᵝ iterate (k * l) f x.
Proof.
  induction k; cbn [iterate Nat.mul]; [reflexivity |].
  transitivity (iterate l f (iterate k (expand i (numeral l) $ f) x)).
  - apply numeral_beta.
  - rewrite <- iterate_plus. apply iterate_right. exact IHk.
Qed.
Theorem multiplication_numerals {n} i k l (f x : Term nat n) :
  expand i multiplication $ expand i (numeral k) $ expand i (numeral l) $ f $ x ↠ᵝ
  iterate (k * l) f x.
Proof.
  transitivity (expand i (numeral k) $ (expand i (numeral l) $ f) $ x).
  - apply app_cong_l, multiplication_beta.
  - transitivity (iterate k (expand i (numeral l) $ f) x).
    + apply numeral_beta.
    + apply iterate_numeral.
Qed.

Print Assumptions expansion_typed.
Print Assumptions numeral_type_rank.
Print Assumptions arithmetic_type_ranks.
Print Assumptions arithmetic_counts.
Print Assumptions numeral_duplications.
Print Assumptions numeral_atoms.
Print Assumptions numeral_typed.
Print Assumptions arithmetic_typed.
Print Assumptions B_beta.
Print Assumptions C_beta.
Print Assumptions K_beta.
Print Assumptions W_beta.
Print Assumptions I_beta.
Print Assumptions H_beta.
Print Assumptions successor_beta.
Print Assumptions addition_beta.
Print Assumptions multiplication_beta.
Print Assumptions numeral_beta.
Print Assumptions numeral_expansion.
Print Assumptions church_normal_is_normal.
Print Assumptions successor_numeral.
Print Assumptions addition_numerals.
Print Assumptions multiplication_numerals.

End BCKW.
