From Stdlib Require Import Lists.List Arith.PeanoNat.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks Reduction AbstractRewriting Congruence DefEq.
From PTSrk.Combinatory Require Import ChurchFinite HornProofEncoding.
Import ListNotations.

(** A finite table of TYPES, selected by an internally supplied Church code.
    Universe U_r itself has sort U_0 in the original PTS, so the code uses
    answer rank zero independently of r. No dependent selector elimination,
    exhaustiveness or parametricity principle is assumed. *)
Module FiniteTypeDispatch.
Module CF := ChurchFinite.ChurchFinite.
Module E := HornProofEncoding.HornProofEncoding.

Definition dispatch {n} k r (values : Fin k -> Term nat n) (q : Term nat n) :=
  CF.apps k (app q (𝓤 r)) values.
Definition table {n} k r (values : Fin k -> Term nat n) : Term nat n :=
  lam (CF.choice_type 0 k) (dispatch k r (fun i => shift (values i)) (var fzero)).
Definition table_type {n} k r : Term nat n := Π (CF.choice_type 0 k) (𝓤 r).

Lemma dispatch_ext k r n (values values' : Fin k -> Term nat n) q :
  (forall i, values i = values' i) -> dispatch k r values q = dispatch k r values' q.
Proof. apply CF.apps_ext. Qed.
Lemma dispatch_replace k r m n (sigma : Fin m -> Term nat n) values q :
  replace sigma (dispatch k r values q) =
  dispatch k r (fun i => replace sigma (values i)) (replace sigma q).
Proof. unfold dispatch; rewrite CF.apps_replace; reflexivity. Qed.
Lemma table_replace k r m n (sigma : Fin m -> Term nat n) values :
  replace sigma (table k r values) = table k r (fun i => replace sigma (values i)).
Proof.
  unfold table; cbn [replace]; rewrite CF.choice_type_replace, dispatch_replace.
  cbn [replace transpose fin_match]; f_equal; apply dispatch_ext; intro i.
  apply CF.replace_shift.
Qed.
Lemma table_ext k r n (values values' : Fin k -> Term nat n) :
  (forall i, values i = values' i) -> table k r values = table k r values'.
Proof. intro H; unfold table; f_equal; apply dispatch_ext; intro i; now rewrite H. Qed.
Lemma table_rename k r m n (rho : Fin m -> Fin n) values :
  rename rho (table k r values) = table k r (fun i => rename rho (values i)).
Proof.
  rewrite <- (replace_var (table k r values)) at 1.
  rewrite rename_replace, table_replace.
  apply table_ext; intro i.
  now rewrite <- rename_replace, replace_var.
Qed.

Theorem table_type_sorted {n} (G : Ctx nat n) k r :
  @typ nat RankSorts n G (table_type k r) (𝓤 2).
Proof.
  unfold table_type; eapply typ_Π with (ℓₜ := 1) (ℓᵤ := 0).
  - replace 1 with (CF.choice_rank 0 k) by (unfold CF.choice_rank; destruct k; reflexivity).
    apply CF.choice_type_sorted.
  - constructor; reflexivity.
  - reflexivity.
Qed.
Theorem dispatch_typed {n} (G : Ctx nat n) k r values q :
  @typ nat RankSorts n G q (CF.choice_type 0 k) ->
  (forall i, @typ nat RankSorts n G (values i) (𝓤 r)) ->
  @typ nat RankSorts n G (dispatch k r values q) (𝓤 r).
Proof.
  intros HQ HV; apply CF.dispatch_typed with (r := 0); auto.
  constructor; reflexivity.
Qed.
Theorem table_typed {n} (G : Ctx nat n) k r values :
  (forall i, @typ nat RankSorts n G (values i) (𝓤 r)) ->
  @typ nat RankSorts n G (table k r values) (table_type k r).
Proof.
  intro HV; unfold table, table_type; eapply typ_λ.
  - apply CF.choice_type_sorted.
  - apply dispatch_typed.
    + rewrite <- (@CF.choice_type_rename 0 k n (S n) fsucc).
      change (typ (G & CF.choice_type 0 k) (var fzero)
        ((G & CF.choice_type 0 k) !! fzero)); constructor.
    + intro i; change (typ (G & CF.choice_type 0 k) (shift (values i)) (shift (𝓤 r))).
      apply weakening, HV.
Qed.
Theorem table_app_sorted {n} (G : Ctx nat n) k r values q :
  (forall i, @typ nat RankSorts n G (values i) (𝓤 r)) ->
  @typ nat RankSorts n G q (CF.choice_type 0 k) ->
  @typ nat RankSorts n G (app (table k r values) q) (𝓤 r).
Proof.
  intros HV HQ; change (typ G (app (table k r values) q) (subst (𝓤 r) q)).
  eapply typ_app; [now apply table_typed | exact HQ].
Qed.

Theorem table_app_beta {n} k r values (q : Term nat n) :
  reduces_to nat n (app (table k r values) q) (dispatch k r values q).
Proof.
  unfold table; eapply rtc_step; [apply step_beta |].
  unfold subst; rewrite dispatch_replace; cbn [replace fin_match].
  erewrite dispatch_ext; [reflexivity | intro i; apply CF.subst_shift].
Qed.
Theorem table_selector_beta {n} k r values (i : Fin k) :
  reduces_to nat n (app (table k r values) (CF.selector 0 k i)) (values i).
Proof.
  eapply rtc_trans; [apply table_app_beta | apply CF.selector_dispatch_beta].
Qed.

Theorem rule_type_reduces k ps a : forall n (env env' : Fin k -> Term nat n),
  (forall i, reduces_to nat n (env i) (env' i)) ->
  reduces_to nat n (E.rule_type ps a env) (E.rule_type ps a env').
Proof.
  induction ps; intros n env env' H; cbn [E.rule_type]; [apply H |].
  apply (@Π_cong_par nat (reduces_to nat) _ _); [apply H |].
  apply IHps; intro i; apply rename_rtc, H.
Qed.
Theorem matrix_reduces k cs a : forall n (env env' : Fin k -> Term nat n),
  (forall i, reduces_to nat n (env i) (env' i)) ->
  reduces_to nat n (E.matrix cs a env) (E.matrix cs a env').
Proof.
  induction cs as [|[ps b] rest IH]; intros n env env' H; cbn [E.matrix]; [apply H |].
  apply (@Π_cong_par nat (reduces_to nat) _ _); [now apply rule_type_reduces |].
  apply IH; intro i; apply rename_rtc, H.
Qed.
Theorem reduction_equiv {n} (t u : Term nat n) :
  reduces_to nat n t u -> def_equiv nat n t u.
Proof. intro H; apply def_equiv_prop; exists u; split; [exact H | reflexivity]. Qed.

Print Assumptions dispatch_ext.
Print Assumptions dispatch_replace.
Print Assumptions table_replace.
Print Assumptions table_ext.
Print Assumptions table_rename.
Print Assumptions table_type_sorted.
Print Assumptions dispatch_typed.
Print Assumptions table_typed.
Print Assumptions table_app_sorted.
Print Assumptions table_app_beta.
Print Assumptions table_selector_beta.
Print Assumptions rule_type_reduces.
Print Assumptions matrix_reduces.
Print Assumptions reduction_equiv.
End FiniteTypeDispatch.
