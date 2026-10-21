From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Ranks
  Reduction AbstractRewriting DefEq.
From PTSrk.NormalizationComplexity Require Import Morphisms.
From PTSrk.SelfInterpreter Require Import FullSource.
Import Context.

(** Executable substitution of independently supplied FULL source evidence.
    All source terms, annotations and conversion paths are transformed by
    the original simultaneous substitution. No target quotation is assumed.
    Completeness statements below remain in Prop; no opaque original typing
    proof is extracted into a computational source derivation. *)
Module SourceSubstitution.
Module FS := FullSource.FullSource.

Definition step_rename {m t u} (d : FS.step_data m t u) :
    forall n (rho : Fin m -> Fin n),
    FS.step_data n (rename rho t) (rename rho u).
Proof.
  induction d; intros k rho; cbn [rename].
  - apply FS.s_pi_left; apply IHd.
  - apply FS.s_pi_right; apply IHd.
  - apply FS.s_lam_left; apply IHd.
  - apply FS.s_lam_right; apply IHd.
  - apply FS.s_app_left; apply IHd.
  - apply FS.s_app_right; apply IHd.
  - rewrite rename_subst; apply FS.s_beta.
Defined.

Definition step_replace {m t u} (d : FS.step_data m t u) :
    forall n (sigma : Fin m -> Term nat n),
    FS.step_data n (replace sigma t) (replace sigma u).
Proof.
  induction d; intros k sigma; cbn [replace].
  - apply FS.s_pi_left; apply IHd.
  - apply FS.s_pi_right; apply IHd.
  - apply FS.s_lam_left; apply IHd.
  - apply FS.s_lam_right; apply IHd.
  - apply FS.s_app_left; apply IHd.
  - apply FS.s_app_right; apply IHd.
  - rewrite replace_subst; apply FS.s_beta.
Defined.

Definition reduction_rename {m n t u} (rho : Fin m -> Fin n)
    (d : FS.reduction m t u) :
    FS.reduction n (rename rho t) (rename rho u) :=
  FS.reduction_map (rename rho) (fun _ _ p => step_rename p n rho) d.

Definition reduction_replace {m n t u} (sigma : Fin m -> Term nat n)
    (d : FS.reduction m t u) :
    FS.reduction n (replace sigma t) (replace sigma u) :=
  FS.reduction_map (replace sigma) (fun _ _ p => step_replace p n sigma) d.

Definition conversion_rename {m t u} (d : FS.conversion m t u) :
    forall n (rho : Fin m -> Fin n),
    FS.conversion n (rename rho t) (rename rho u).
Proof.
  induction d; intros k rho.
  - apply FS.c_refl.
  - eapply FS.c_forward; [exact (step_rename s k rho) | apply IHd].
  - eapply FS.c_backward; [exact (step_rename s k rho) | apply IHd].
Defined.

Definition conversion_replace {m t u} (d : FS.conversion m t u) :
    forall n (sigma : Fin m -> Term nat n),
    FS.conversion n (replace sigma t) (replace sigma u).
Proof.
  induction d; intros k sigma.
  - apply FS.c_refl.
  - eapply FS.c_forward; [exact (step_replace s k sigma) | apply IHd].
  - eapply FS.c_backward; [exact (step_replace s k sigma) | apply IHd].
Defined.

(** A strict lookup-preserving renaming is sufficient to bootstrap genuine
    computational weakening; arbitrary typed renamings are supported below. *)
Definition lookup_renaming {m n} (G : Ctx nat m) (D : Ctx nat n)
    (rho : Fin m -> Fin n) :=
  forall i, D !! rho i = rename rho (G !! i).

Lemma lookup_renaming_lift {m n} G D (rho : Fin m -> Fin n) A :
  lookup_renaming G D rho ->
  lookup_renaming (G & A) (D & rename rho A) (weak rho).
Proof.
  intros H i; dependent elimination i as [fzero | fsucc i].
  - change (shift (rename rho A) = rename (weak rho) (shift A)).
    unfold shift; rewrite !rename_comp; reflexivity.
  - change (shift (D !! rho i) = rename (weak rho) (shift (G !! i))).
    rewrite H; unfold shift; rewrite !rename_comp; reflexivity.
Qed.

Lemma lookup_renaming_shift {n} (G : Ctx nat n) A :
  lookup_renaming G (G & A) fsucc.
Proof. intro i; reflexivity. Qed.

Definition derivation_rename_strict {m G t T}
    (d : FS.derivation m G t T) :
    forall n D (rho : Fin m -> Fin n), lookup_renaming G D rho ->
    FS.derivation n D (rename rho t) (rename rho T).
Proof.
  induction d; intros k D rho Hr; cbn [rename].
  - apply FS.d_sort.
  - eapply FS.d_pi; [apply IHd1; exact Hr |].
    apply IHd2; apply lookup_renaming_lift; exact Hr.
  - rewrite <- Hr; apply FS.d_var.
  - eapply FS.d_lam; [apply IHd1; exact Hr |].
    apply IHd2; apply lookup_renaming_lift; exact Hr.
  - rewrite rename_subst; eapply FS.d_app; [apply IHd1 | apply IHd2]; exact Hr.
  - eapply FS.d_conv; [apply IHd1; exact Hr | apply IHd2; exact Hr |].
    apply conversion_rename; exact c.
Defined.

Definition weaken {n G t T} (d : FS.derivation n G t T) A :
    FS.derivation (S n) (G & A) (shift t) (shift T) :=
  derivation_rename_strict d (S n) (G & A) fsucc
    (lookup_renaming_shift G A).

(** The actual variable derivations are data, not an original Prop typing
    oracle. The source context need not be well formed: the transformation
    preserves the exact full original deduction domain. *)
Definition substitution_data {m n} (G : Ctx nat m) (D : Ctx nat n)
    (sigma : Fin m -> Term nat n) : Type :=
  forall i, FS.derivation n D (sigma i) (replace sigma (G !! i)).

Definition substitution_lift {m n G D sigma}
    (ds : @substitution_data m n G D sigma) A :
    substitution_data (G & A) (D & replace sigma A) (transpose sigma).
Proof.
  intro i; dependent elimination i as [fzero | fsucc i];
    cbn [transpose fin_match index ctx_top ctx_pred].
  - rewrite replace_lift_shift; exact (FS.d_var (D & replace sigma A) fzero).
  - rewrite replace_lift_shift; exact (weaken (ds i) (replace sigma A)).
Defined.

Definition derivation_replace {m G t T} (d : FS.derivation m G t T) :
    forall n D (sigma : Fin m -> Term nat n), substitution_data G D sigma ->
    FS.derivation n D (replace sigma t) (replace sigma T).
Proof.
  induction d; intros k D sigma ds; cbn [replace].
  - apply FS.d_sort.
  - eapply FS.d_pi; [apply IHd1; exact ds |].
    apply IHd2; apply substitution_lift; exact ds.
  - apply ds.
  - eapply FS.d_lam; [apply IHd1; exact ds |].
    apply IHd2; apply substitution_lift; exact ds.
  - rewrite replace_subst; eapply FS.d_app; [apply IHd1 | apply IHd2]; exact ds.
  - eapply FS.d_conv; [apply IHd1; exact ds | apply IHd2; exact ds |].
    apply conversion_replace; exact c.
Defined.

Definition renaming_data {m n} (G : Ctx nat m) (D : Ctx nat n)
    (rho : Fin m -> Fin n) : Type :=
  forall i, FS.derivation n D (var (rho i)) (rename rho (G !! i)).

Definition renaming_substitution {m n G D rho}
    (dr : @renaming_data m n G D rho) :
    substitution_data G D (fun i => var (rho i)).
Proof. intro i; rewrite replace_as_rename; exact (dr i). Defined.

Definition derivation_rename {m n G D rho t T}
    (dr : @renaming_data m n G D rho) (d : FS.derivation m G t T) :
    FS.derivation n D (rename rho t) (rename rho T).
Proof.
  rewrite <- !replace_as_rename.
  exact (derivation_replace d n D (fun i => var (rho i))
    (renaming_substitution dr)).
Defined.

Theorem substitution_data_sound {m n G D sigma} :
  @substitution_data m n G D sigma -> TypedSub G D sigma.
Proof. intros ds i; exact (FS.derivation_sound _ _ _ _ (ds i)). Qed.

(** Finite choice here is only an inhabitedness theorem in Prop. It is NOT
    a function that extracts computational data from original typ proofs. *)
Lemma inhabited_fin_function m (P : Fin m -> Type) :
  (forall i, inhabited (P i)) -> inhabited (forall i, P i).
Proof.
  induction m as [|m IH]; intros H.
  - constructor; intro i; dependent elimination i.
  - destruct (H fzero) as [z].
    destruct (IH (fun i => P (fsucc i)) (fun i => H (fsucc i))) as [s].
    constructor; intro i; dependent elimination i as [fzero | fsucc i]; [exact z | exact (s i)].
Qed.

Theorem substitution_data_iff {m n} G D (sigma : Fin m -> Term nat n) :
  inhabited (substitution_data G D sigma) <-> TypedSub G D sigma.
Proof.
  split.
  - intros [ds]; apply substitution_data_sound; exact ds.
  - intro H; apply inhabited_fin_function; intro i.
    apply FS.derivation_complete; apply H.
Qed.

Theorem substituted_derivation_sound {m n G D sigma t T}
    (ds : @substitution_data m n G D sigma) (d : FS.derivation m G t T) :
  @typ nat RankSorts n D (replace sigma t) (replace sigma T).
Proof. exact (FS.derivation_sound _ _ _ _ (derivation_replace d n D sigma ds)). Qed.

Definition beta_substitution_data {n G A u}
    (du : FS.derivation n G u A) :
    substitution_data (G & A) G (fin_match u (fun i => var i)).
Proof.
  intro i; dependent elimination i as [fzero | fsucc i].
  - change (FS.derivation _ G u
      (replace (fin_match u (fun j => var j)) (shift A))).
    unfold shift; rewrite replace_rename.
    change (FS.derivation _ G u (replace (fun j => var j) A)).
    rewrite replace_var; exact du.
  - change (FS.derivation _ G (var i)
      (replace (fin_match u (fun j => var j)) (shift (G !! i)))).
    unfold shift; rewrite replace_rename.
    change (FS.derivation _ G (var i) (replace (fun j => var j) (G !! i))).
    rewrite replace_var; apply FS.d_var.
Defined.

(** This is an executable derivation of the LITERAL original beta
    contractum, including its substituted annotations and result type. *)
Definition beta_contractum_derivation {n G A body B u}
    (db : FS.derivation (S n) (G & A) body B)
    (du : FS.derivation n G u A) :
    FS.derivation n G (subst body u) (subst B u) :=
  derivation_replace db n G (fin_match u (fun i => var i)) (beta_substitution_data du).

Definition beta_redex_derivation {n G A body B u} a
    (dA : FS.derivation n G A (𝓤 a))
    (db : FS.derivation (S n) (G & A) body B)
    (du : FS.derivation n G u A) :
    FS.derivation n G (app (lam A body) u) (subst B u) :=
  FS.d_app (FS.d_lam a dA db) du.

Theorem beta_contractum_sound {n G A body B u}
    (db : FS.derivation (S n) (G & A) body B)
    (du : FS.derivation n G u A) :
  @typ nat RankSorts n G (subst body u) (subst B u).
Proof. exact (FS.derivation_sound _ _ _ _ (beta_contractum_derivation db du)). Qed.

Theorem beta_source_preservation {n G A body B u} a
    (dA : FS.derivation n G A (𝓤 a))
    (db : FS.derivation (S n) (G & A) body B)
    (du : FS.derivation n G u A) :
  @typ nat RankSorts n G (app (lam A body) u) (subst B u) /\
  step nat n (app (lam A body) u) (subst body u) /\
  @typ nat RankSorts n G (subst body u) (subst B u).
Proof.
  split; [exact (FS.derivation_sound _ _ _ _ (beta_redex_derivation a dA db du)) |].
  split; [apply FS.step_sound; apply FS.s_beta | exact (beta_contractum_sound db du)].
Qed.

Print Assumptions step_rename.
Print Assumptions step_replace.
Print Assumptions conversion_replace.
Print Assumptions derivation_rename_strict.
Print Assumptions weaken.
Print Assumptions substitution_data_iff.
Print Assumptions derivation_replace.
Print Assumptions derivation_rename.
Print Assumptions beta_contractum_derivation.
Print Assumptions beta_source_preservation.

End SourceSubstitution.
