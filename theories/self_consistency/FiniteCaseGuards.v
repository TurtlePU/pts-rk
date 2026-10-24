(** Independent finite-case guards and their original-PTS eliminators.
    The finite list contains arbitrary closed points of one closed carrier.
    Neither acceptance nor the desired rejection theorem occurs in the guard.
    All finite indices and lists are external construction parameters. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRStructural.
Import ListNotations.

Module FiniteCaseGuards.
Import CommonCodes Core Structural.

Definition motive_type {n} (A : closed_term) : Term nat n :=
  Arrow (lift_closed A) (𝓤 2).
Definition point_type {n} (P : Term nat n) (c : closed_term) :=
  app P (lift_closed c).
Fixpoint cases_type {n} (cs : list closed_term) (P R : Term nat n) : Term nat n :=
  match cs with
  | [] => R
  | c :: rest => Arrow (point_type P c) (cases_type rest P R)
  end.
Definition cases_rank (cs : list closed_term) :=
  match cs with [] => 2 | _ :: _ => 3 end.
Definition guard_rank a cs := Nat.max (S (S a)) (cases_rank cs).
Definition guard_type {n} A cs (x : Term nat n) : Term nat n :=
  Π (motive_type A)
    (cases_type cs (var fzero) (app (var fzero) (shift x))).

Theorem positive_guard_rank a cs : 1 <= a -> guard_rank a cs = S (S a).
Proof. unfold guard_rank, cases_rank; destruct cs; intro H; lia. Qed.

Lemma motive_type_rename A m n (rho : Fin m -> Fin n) :
  rename rho (motive_type A) = @motive_type n A.
Proof. unfold motive_type; rewrite rename_arrow, rename_lift_closed; reflexivity. Qed.
Lemma motive_type_replace A m n (sigma : Fin m -> Term nat n) :
  replace sigma (motive_type A) = @motive_type n A.
Proof. unfold motive_type; rewrite replace_arrow, replace_lift_closed; reflexivity. Qed.
Lemma point_type_rename m n (rho : Fin m -> Fin n) P c :
  rename rho (point_type P c) = point_type (rename rho P) c.
Proof. unfold point_type; cbn [rename]; rewrite rename_lift_closed; reflexivity. Qed.
Lemma point_type_replace m n (sigma : Fin m -> Term nat n) P c :
  replace sigma (point_type P c) = point_type (replace sigma P) c.
Proof. unfold point_type; cbn [replace]; rewrite replace_lift_closed; reflexivity. Qed.
Lemma cases_type_rename cs : forall m n (rho : Fin m -> Fin n) P R,
  rename rho (cases_type cs P R) = cases_type cs (rename rho P) (rename rho R).
Proof. induction cs; intros; cbn [cases_type]; [reflexivity|].
  rewrite rename_arrow, point_type_rename, IHcs; reflexivity. Qed.
Lemma cases_type_replace cs : forall m n (sigma : Fin m -> Term nat n) P R,
  replace sigma (cases_type cs P R) = cases_type cs (replace sigma P) (replace sigma R).
Proof. induction cs; intros; cbn [cases_type]; [reflexivity|].
  rewrite replace_arrow, point_type_replace, IHcs; reflexivity. Qed.
Lemma guard_type_rename A cs m n (rho : Fin m -> Fin n) x :
  rename rho (guard_type A cs x) = guard_type A cs (rename rho x).
Proof.
  unfold guard_type; cbn [rename]. rewrite motive_type_rename, cases_type_rename.
  cbn [rename]; unfold shift; rewrite !rename_comp; reflexivity.
Qed.
Lemma guard_type_replace A cs m n (sigma : Fin m -> Term nat n) x :
  replace sigma (guard_type A cs x) = guard_type A cs (replace sigma x).
Proof.
  unfold guard_type; cbn [replace]. rewrite motive_type_replace, cases_type_replace.
  cbn [replace]; rewrite replace_shift; reflexivity.
Qed.

Lemma motive_type_sorted A a (HA : Typed ε A (𝓤 a)) n (G : Ctx nat n) :
  Typed G (motive_type A) (𝓤 (S a)).
Proof.
  unfold motive_type, Arrow. replace (S a) with (Nat.max (S a) 0) by lia.
  apply tPi; [|apply tU].
  exact (lift_closed_typed G _ _ HA).
Qed.
Lemma point_type_sorted A c n (G : Ctx nat n) P :
  Typed ε c A -> Typed G P (motive_type A) -> Typed G (point_type P c) (𝓤 2).
Proof.
  intros Hc HP. eapply arrow_application; [exact HP|].
  exact (lift_closed_typed G _ _ Hc).
Qed.
Lemma cases_type_sorted A cs : forall n (G : Ctx nat n) P R,
  Forall (fun c => Typed ε c A) cs -> Typed G P (motive_type A) ->
  Typed G R (𝓤 2) -> Typed G (cases_type cs P R) (𝓤 (cases_rank cs)).
Proof.
  induction cs as [|c cs IH]; intros n G P R Hcs HP HR;
    cbn [cases_type cases_rank]; [exact HR|].
  inversion Hcs; subst. unfold Arrow.
  replace 3 with (Nat.max 3 (cases_rank cs)) by (destruct cs; reflexivity).
  apply tPi; [eapply point_type_sorted; eauto|].
  unfold shift; rewrite cases_type_rename.
  apply IH; auto.
  - rewrite <- (motive_type_rename A n (S n) fsucc). apply weakening; exact HP.
  - exact (weakening RankSorts R (𝓤 2) (point_type P c) HR).
Qed.
Theorem guard_type_sorted A a cs n (G : Ctx nat n) x :
  Typed ε A (𝓤 a) -> Forall (fun c => Typed ε c A) cs ->
  Typed G x (lift_closed A) ->
  Typed G (guard_type A cs x) (𝓤 (guard_rank a cs)).
Proof.
  intros HA Hcs Hx. unfold guard_type, guard_rank. apply tPi.
  - apply motive_type_sorted; exact HA.
  - apply (cases_type_sorted A); [exact Hcs| |].
    + pose proof (tV (G & motive_type A) fzero) as H.
      cbn [index ctx_top ctx_pred fin_match] in H.
      unfold shift in H; rewrite motive_type_rename in H; exact H.
    + eapply arrow_application with (A := lift_closed A).
      * pose proof (tV (G & motive_type A) fzero) as H.
        cbn [index ctx_top ctx_pred fin_match] in H.
        unfold shift in H; rewrite motive_type_rename in H; exact H.
      * rewrite lift_closed_shift. apply weakening; exact Hx.
Qed.

Fixpoint ignore_cases {n} cs (P t : Term nat n) : Term nat n :=
  match cs with
  | [] => t
  | c :: rest => lam (point_type P c) (ignore_cases rest (shift P) (shift t))
  end.
Lemma ignore_cases_typed A cs : forall n (G : Ctx nat n) P t R,
  Forall (fun c => Typed ε c A) cs -> Typed G P (motive_type A) ->
  Typed G t R -> Typed G (ignore_cases cs P t) (cases_type cs P R).
Proof.
  induction cs as [|c cs IH]; intros n G P t R Hcs HP Ht;
    cbn [ignore_cases cases_type]; [exact Ht|].
  inversion Hcs; subst. unfold Arrow. eapply typ_λ with (ℓ := 2).
  - eapply point_type_sorted; eauto.
  - unfold shift at 3. rewrite cases_type_rename. apply IH; auto.
    + rewrite <- (motive_type_rename A n (S n) fsucc). apply weakening; exact HP.
    + apply weakening; exact Ht.
Qed.
Fixpoint select_case {n} cs i (P : Term nat n) : Term nat n :=
  match cs with
  | [] => 𝓤 0
  | c :: rest => lam (point_type P c)
      (match i with
       | 0 => ignore_cases rest (shift P) (var fzero)
       | S j => select_case rest j (shift P)
       end)
  end.
Lemma select_case_typed A cs : forall i c n (G : Ctx nat n) P,
  Forall (fun c => Typed ε c A) cs -> Typed G P (motive_type A) ->
  nth_error cs i = Some c ->
  Typed G (select_case cs i P) (cases_type cs P (point_type P c)).
Proof.
  induction cs as [|d cs IH]; intros i c n G P Hcs HP Hi.
  - destruct i; discriminate Hi.
  - inversion Hcs; subst. cbn [select_case cases_type]. unfold Arrow.
    eapply typ_λ with (ℓ := 2); [eapply point_type_sorted; eauto|].
    unfold shift at 3. rewrite cases_type_rename, point_type_rename.
    assert (HP' : Typed (G & point_type P d) (shift P) (motive_type A)).
    { rewrite <- (motive_type_rename A n (S n) fsucc). apply weakening; exact HP. }
    destruct i as [|i].
    + cbn [nth_error] in Hi; injection Hi as <-.
      apply (ignore_cases_typed A); auto.
      rewrite <- point_type_rename. exact (tV (G & point_type P d) fzero).
    + apply IH; auto.
Qed.
Definition guard_witness A cs i : closed_term :=
  lam (motive_type A) (select_case cs i (var fzero)).
Theorem guard_witness_typed A a cs i c :
  Typed ε A (𝓤 a) -> Forall (fun c => Typed ε c A) cs ->
  nth_error cs i = Some c ->
  Typed ε (guard_witness A cs i) (guard_type A cs c).
Proof.
  intros HA Hcs Hi. unfold guard_witness, guard_type.
  eapply typ_λ with (ℓ := S a); [apply motive_type_sorted; exact HA|].
  replace (shift c) with (@lift_closed 1 c)
    by (rewrite lift_closed_shift, lift_closed_zero; reflexivity).
  apply (select_case_typed A); auto.
  pose proof (tV (ε & motive_type A) fzero) as H.
  cbn [index ctx_top ctx_pred fin_match] in H.
  unfold shift in H; rewrite motive_type_rename in H; exact H.
Qed.

Fixpoint supply_cases {n} (hs : list (Term nat n)) (g : Term nat n) : Term nat n :=
  match hs with [] => g | h :: rest => supply_cases rest (app g h) end.
Lemma supply_cases_typed cs n (G : Ctx nat n) P R g hs :
  Forall2 (fun c h => Typed G h (point_type P c)) cs hs ->
  Typed G g (cases_type cs P R) -> Typed G (supply_cases hs g) R.
Proof.
  intro H; revert g; induction H; intros g Hg; cbn [supply_cases cases_type] in *.
  - exact Hg.
  - apply IHForall2. eapply arrow_application; eauto.
Qed.
Theorem guarded_elimination A cs n (G : Ctx nat n) x g P hs :
  Typed G g (guard_type A cs x) -> Typed G P (motive_type A) ->
  Forall2 (fun c h => Typed G h (point_type P c)) cs hs ->
  Typed G (supply_cases hs (app g P)) (app P x).
Proof.
  intros Hg HP Hhs. eapply (supply_cases_typed cs n G P (app P x)); [exact Hhs|].
  pose proof (tApp Hg HP) as H.
  unfold subst in H; rewrite cases_type_replace in H; cbn [replace] in H.
  rewrite replace_shift_substitution in H; exact H.
Qed.

Definition elimination_type A cs (P : closed_term) : closed_term :=
  Π A (Arrow (guard_type A cs (var fzero)) (app (lift_closed P) (var fzero))).
Definition elimination A cs (P : closed_term) (hs : list closed_term) : closed_term :=
  lam A (lam (guard_type A cs (var fzero))
    (supply_cases (map (@lift_closed 2) hs) (app (var fzero) (lift_closed P)))).
Lemma closed_branches_lift n (G : Ctx nat n) P cs hs :
  Forall2 (fun c h => Typed ε h (app P c)) cs hs ->
  Forall2 (fun c h => Typed G h (point_type (lift_closed P) c))
    cs (map (@lift_closed n) hs).
Proof.
  intro H; induction H; cbn [map]; constructor; auto.
  pose proof (lift_closed_typed G _ _ H) as J.
  unfold point_type, lift_closed in *; exact J.
Qed.
Lemma closed_motive_lift A P n (G : Ctx nat n) :
  Typed ε P (motive_type A) -> Typed G (lift_closed P) (motive_type A).
Proof.
  intro HP. pose proof (lift_closed_typed G _ _ HP) as H.
  unfold lift_closed at 2 in H. rewrite motive_type_rename in H; exact H.
Qed.
Theorem elimination_type_sorted A a cs P :
  Typed ε A (𝓤 a) -> Forall (fun c => Typed ε c A) cs ->
  Typed ε P (motive_type A) ->
  Typed ε (elimination_type A cs P) (𝓤 (S (guard_rank a cs))).
Proof.
  intros HA Hcs HP. unfold elimination_type, Arrow.
  eapply typ_Π with (ℓₜ := a) (ℓᵤ := S (guard_rank a cs)); [exact HA| |].
  - eapply typ_Π with (ℓₜ := guard_rank a cs) (ℓᵤ := 2).
    + apply guard_type_sorted; auto.
      rewrite lift_closed_shift, lift_closed_zero. exact (tV (ε & A) fzero).
    + assert (Hx : Typed (ε & A) (app (lift_closed P) (var fzero)) (𝓤 2)).
      { eapply arrow_application with (A := lift_closed A).
        - apply closed_motive_lift; exact HP.
        - rewrite lift_closed_shift, lift_closed_zero. exact (tV (ε & A) fzero). }
      exact (weakening RankSorts _ (𝓤 2) _ Hx).
    + change (S (guard_rank a cs) = Nat.max (S (guard_rank a cs)) 2).
      unfold guard_rank; lia.
  - change (S (guard_rank a cs) = Nat.max (S a) (S (guard_rank a cs))).
    unfold guard_rank; lia.
Qed.
Theorem elimination_typed A a cs P hs :
  Typed ε A (𝓤 a) -> Forall (fun c => Typed ε c A) cs ->
  Typed ε P (motive_type A) ->
  Forall2 (fun c h => Typed ε h (app P c)) cs hs ->
  Typed ε (elimination A cs P hs) (elimination_type A cs P).
Proof.
  intros HA Hcs HP Hhs. unfold elimination, elimination_type, Arrow.
  eapply typ_λ with (ℓ := a); [exact HA|].
  eapply typ_λ with (ℓ := guard_rank a cs).
  - apply guard_type_sorted; auto.
    rewrite lift_closed_shift, lift_closed_zero. exact (tV (ε & A) fzero).
  - unfold shift. rewrite rename_application, rename_lift_closed.
    cbn [rename].
    apply (guarded_elimination A cs).
    + pose proof (tV (ε & A & guard_type A cs (var fzero)) fzero) as H.
      cbn [index ctx_top ctx_pred fin_match] in H.
      unfold shift in H; rewrite guard_type_rename in H; exact H.
    + apply closed_motive_lift; exact HP.
    + apply closed_branches_lift; exact Hhs.
Qed.

End FiniteCaseGuards.
