From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import ContextualTelescope.
Import Context ListNotations.

(** Uniform dependent-domain PARAMETERS, indexed by a finite rank vector,
    not by concrete domain syntax. The generated domains are applications
    of bound family parameters to the actual telescope variables. *)
Module UniformTelescope.
Module CT := ContextualTelescope.ContextualTelescope.

Fixpoint base_ren (rs : list nat) {n} : Fin n -> Fin (CT.scope rs n) :=
  match rs with [] => fun i => i | _ :: tail => fun i => base_ren tail (fsucc i) end.

Theorem base_typing n rs (D : CT.telescope n rs) G t T :
  @typ nat RankSorts n G t T ->
  @typ nat RankSorts _ (CT.context D G) (rename (base_ren rs) t) (rename (base_ren rs) T).
Proof.
  revert G t T; induction D; intros G t T H; cbn [CT.context base_ren].
  - rewrite !rename_id; exact H.
  - assert (HW : typ (G & A) (shift t) (shift T)) by (apply weakening; exact H).
    pose proof (IHD (G & A) (shift t) (shift T) HW) as HC.
    unfold shift in HC; rewrite !rename_comp in HC; exact HC.
Qed.

Lemma lift_sub_base_variable rs : forall m n (sigma : Fin m -> Term nat n) i,
  CT.lift_sub rs sigma (base_ren rs i) = rename (base_ren rs) (sigma i).
Proof.
  induction rs as [|r rs IH]; intros m n sigma i; cbn [CT.lift_sub base_ren].
  - symmetry; apply rename_id.
  - rewrite IH; cbn [transpose fin_match]; unfold shift; rewrite rename_comp; reflexivity.
Qed.

Theorem lift_sub_base rs m n (sigma : Fin m -> Term nat n) t :
  replace (CT.lift_sub rs sigma) (rename (base_ren rs) t) =
    rename (base_ren rs) (replace sigma t).
Proof.
  rewrite replace_rename, rename_replace; apply replace_ext; apply lift_sub_base_variable.
Qed.

Fixpoint apply_under {n rs} (D : CT.telescope n rs) : Term nat n -> Term nat (CT.scope rs n) :=
  match D in CT.telescope k ranks return Term nat k -> Term nat (CT.scope ranks k) with
  | CT.tnil => fun f => f
  | CT.tcons _ _ E => fun f => apply_under E (app (shift f) (var fzero))
  end.

Lemma fresh_substitution n (t : Term nat (S n)) :
  subst (rename (weak (@fsucc n)) t) (var fzero) = t.
Proof.
  unfold subst; rewrite replace_rename; rewrite <- (replace_var t) at 2.
  apply replace_ext; intro i; dependent elimination i; reflexivity.
Qed.

Theorem apply_under_typed n rs (D : CT.telescope n rs) : forall G f T,
  @typ nat RankSorts n G f (CT.close_type D T) ->
  @typ nat RankSorts _ (CT.context D G) (apply_under D f) T.
Proof.
  induction D; intros G f T Hf; cbn [apply_under CT.context CT.close_type] in *.
  - exact Hf.
  - apply IHD. rewrite <- (fresh_substitution n (CT.close_type D T)).
    eapply (typ_app (shift A)).
    + change (typ (G & A) (shift f) (shift (Π A (CT.close_type D T)))).
      apply weakening; exact Hf.
    + change (typ (G & A) (var fzero) ((G & A) !! fzero)); constructor.
Qed.

Theorem apply_under_replace m rs (D : CT.telescope m rs) : forall n sigma f,
  replace (CT.lift_sub rs sigma) (apply_under D f) =
    apply_under (CT.replace_telescope D n sigma) (replace sigma f).
Proof.
  induction D; intros k sigma f; cbn [apply_under CT.replace_telescope CT.lift_sub]; [reflexivity |].
  etransitivity; [exact (IHD (S k) (transpose sigma) (app (shift f) (var fzero))) |].
  f_equal; cbn [replace transpose fin_match]; rewrite replace_lift_shift; reflexivity.
Qed.

Theorem apply_under_rename m rs (D : CT.telescope m rs) : forall n rho f,
  rename (CT.lift_ren rs rho) (apply_under D f) =
    apply_under (CT.rename_telescope D n rho) (rename rho f).
Proof.
  induction D; intros k rho f; cbn [apply_under CT.rename_telescope CT.lift_ren]; [reflexivity |].
  etransitivity; [exact (IHD (S k) (weak rho) (app (shift f) (var fzero))) |].
  f_equal; cbn [rename weak fin_match]; unfold shift; rewrite !rename_comp; reflexivity.
Qed.

Theorem apply_under_reduces n rs (D : CT.telescope n rs) f g :
  reduces_to nat n f g -> reduces_to nat _ (apply_under D f) (apply_under D g).
Proof.
  revert f g; induction D; intros f g H; cbn [apply_under]; [exact H |].
  apply IHD, (@app_cong_l nat (reduces_to nat) _ (S n)), rename_rtc; exact H.
Qed.

Theorem apply_under_closure n rs (D : CT.telescope n rs) t :
  reduces_to nat _ (apply_under D (CT.close_term D t)) t.
Proof.
  induction D; cbn [apply_under CT.close_term]; [reflexivity |].
  eapply rtc_trans; [apply (apply_under_reduces (S n) rs D) | exact (IHD t)].
  eapply rtc_step; [apply step_beta |].
  rewrite fresh_substitution; reflexivity.
Qed.

Lemma isLambda_rename m (t : Term nat m) n (rho : Fin m -> Fin n) :
  isLambda (rename rho t) = isLambda t.
Proof. destruct t; reflexivity. Qed.

Lemma normalb_rename m (t : Term nat m) : forall n (rho : Fin m -> Fin n),
  normalb (rename rho t) = normalb t.
Proof.
  induction t; intros; cbn [normalb rename]; try reflexivity;
    rewrite IHt1, IHt2; try rewrite isLambda_rename; reflexivity.
Qed.

Theorem apply_under_normal n rs (D : CT.telescope n rs) f :
  normalb f = true -> isLambda f = false -> normalb (apply_under D f) = true.
Proof.
  revert f; induction D; intros f Hf Hlambda; cbn [apply_under]; [exact Hf |].
  apply IHD; [| reflexivity]. cbn [normalb]; unfold shift.
  rewrite normalb_rename, isLambda_rename, Hf, Hlambda; reflexivity.
Qed.

Theorem apply_under_neutral n rs (D : CT.telescope n rs) f :
  isLambda f = false -> isLambda (apply_under D f) = false.
Proof. revert f; induction D; intros f H; cbn [apply_under]; [exact H | apply IHD; reflexivity]. Qed.

Lemma annotations_rename n rs (D : CT.telescope n rs) : forall m rho,
  CT.normal_annotations (CT.rename_telescope D m rho) = CT.normal_annotations D.
Proof.
  induction D; intros; cbn [CT.rename_telescope CT.normal_annotations]; [reflexivity |].
  rewrite normalb_rename, IHD; reflexivity.
Qed.

Fixpoint snoc {n rs} (D : CT.telescope n rs) r :
    Term nat (CT.scope rs n) -> CT.telescope n (rs ++ [r]) :=
  match D in CT.telescope k ranks return
      Term nat (CT.scope ranks k) -> CT.telescope k (ranks ++ [r]) with
  | CT.tnil => fun A => CT.tcons r A CT.tnil
  | CT.tcons q A E => fun B => CT.tcons q A (snoc E r B)
  end.

Theorem snoc_formed n rs (D : CT.telescope n rs) r A G :
  CT.formed G D -> @typ nat RankSorts _ (CT.context D G) A (𝓤 r) ->
  CT.formed G (snoc D r A).
Proof.
  revert G A; induction D; intros G B HD HB; cbn [snoc CT.formed CT.context] in *.
  - split; [exact HB | exact I].
  - destruct HD as [HA HE]; split; [exact HA | apply IHD; assumption].
Qed.

Theorem snoc_normal n rs (D : CT.telescope n rs) r A :
  CT.normal_annotations (snoc D r A) = CT.normal_annotations D && normalb A.
Proof.
  induction D; cbn [snoc CT.normal_annotations]; [apply andb_true_r |].
  rewrite IHD, andb_assoc; reflexivity.
Qed.

(** Each step adds one DOMAIN FAMILY parameter Xi : Pi previous. U_ri.
    Its own formation rank is rank(previous,0), because U_ri : U0. *)
Fixpoint parameter_ranks (prefix todo : list nat) : list nat :=
  match todo with
  | [] => []
  | r :: rest => CT.rank prefix 0 :: parameter_ranks (prefix ++ [r]) rest
  end.
Fixpoint extend_ranks (prefix todo : list nat) : list nat :=
  match todo with [] => prefix | r :: rest => extend_ranks (prefix ++ [r]) rest end.

Definition next_domains {n rs} (D : CT.telescope n rs) r : CT.telescope (S n) (rs ++ [r]) :=
  let E := CT.rename_telescope D (S n) fsucc in
  snoc E r (apply_under E (var fzero)).

Fixpoint generate_from (todo : list nat) {n rs} (D : CT.telescope n rs) :
    CT.telescope n (parameter_ranks rs todo) *
    CT.telescope (CT.scope (parameter_ranks rs todo) n) (extend_ranks rs todo) :=
  match todo as remaining return
      CT.telescope n (parameter_ranks rs remaining) *
      CT.telescope (CT.scope (parameter_ranks rs remaining) n) (extend_ranks rs remaining) with
  | [] => (CT.tnil, D)
  | r :: rest =>
      let '(P, E) := generate_from rest (next_domains D r) in
      (CT.tcons (CT.rank rs 0) (CT.close_type D (𝓤 r)) P, E)
  end.

Definition parameters n rs := fst (generate_from rs (@CT.tnil n)).
Definition domains n rs := snd (generate_from rs (@CT.tnil n)).

Theorem extend_ranks_exact prefix todo : extend_ranks prefix todo = prefix ++ todo.
Proof.
  revert prefix; induction todo; intros; cbn [extend_ranks]; [now rewrite app_nil_r |].
  rewrite IHtodo, <- app_assoc; reflexivity.
Qed.

Theorem parameter_count prefix todo : length (parameter_ranks prefix todo) = length todo.
Proof. revert prefix; induction todo; intros; cbn [parameter_ranks length]; [reflexivity | now rewrite IHtodo]. Qed.

Theorem parameter_ranks_bounded prefix todo k :
  Forall (fun r => r <= k) prefix -> Forall (fun r => r <= k) todo ->
  Forall (fun q => q <= S k) (parameter_ranks prefix todo).
Proof.
  revert prefix; induction todo as [|r todo IH]; intros prefix HP HT; cbn [parameter_ranks].
  - constructor.
  - inversion HT; subst; constructor.
    + pose proof (CT.rank_bounded prefix k 0 HP); lia.
    + apply IH; [apply Forall_app; split; [exact HP | constructor; [assumption | constructor]] | assumption].
Qed.

Theorem parameters_rank_bound rs k s : Forall (fun r => r <= k) rs ->
  CT.rank (parameter_ranks [] rs) s <= Nat.max (k+2) s.
Proof.
  intro H; replace (k+2) with (S (S k)) by lia.
  apply CT.rank_bounded, parameter_ranks_bounded; [constructor | exact H].
Qed.

Theorem apply_under_annotations_irrelevant n rs (D E : CT.telescope n rs) f :
  apply_under D f = apply_under E f.
Proof.
  revert E f; induction D; intros E f; dependent elimination E; cbn [apply_under];
    [reflexivity | apply IHD].
Qed.

Lemma next_domains_formed n rs (D : CT.telescope n rs) G r :
  CT.formed G D -> CT.formed (G & CT.close_type D (𝓤 r)) (next_domains D r).
Proof.
  intro HD; unfold next_domains; apply snoc_formed.
  - apply CT.formed_rename with (G := G); [exact HD | apply typed_ren_shift].
  - apply apply_under_typed.
    pose proof (CT.close_type_rename n rs D (S n) fsucc (𝓤 r)) as Htype.
    cbn [rename] in Htype; rewrite <- Htype.
    change (typ (G & CT.close_type D (𝓤 r)) (var fzero)
      ((G & CT.close_type D (𝓤 r)) !! fzero)); constructor.
Qed.

Lemma next_domains_normal n rs (D : CT.telescope n rs) r :
  CT.normal_annotations D = true -> CT.normal_annotations (next_domains D r) = true.
Proof.
  intro H; unfold next_domains; rewrite snoc_normal, annotations_rename, H.
  cbn; apply apply_under_normal; reflexivity.
Qed.

Theorem generate_from_formed todo : forall n rs (D : CT.telescope n rs) G,
  CT.formed G D ->
  CT.formed G (fst (generate_from todo D)) /\
  CT.formed (CT.context (fst (generate_from todo D)) G) (snd (generate_from todo D)).
Proof.
  induction todo as [|r todo IH]; intros n rs D G HD; cbn [generate_from]; [split; [exact I | exact HD] |].
  destruct (generate_from todo (next_domains D r)) as [P E] eqn:Hgen; cbn.
  pose proof (IH _ _ (next_domains D r) (G & CT.close_type D (𝓤 r))
    (next_domains_formed _ _ D G r HD)) as H.
  rewrite Hgen in H; cbn in H; destruct H as [HP HE]; split.
  - split; [apply CT.close_type_sort; [exact HD | constructor; reflexivity] | exact HP].
  - exact HE.
Qed.

Theorem generate_from_normal todo : forall n rs (D : CT.telescope n rs),
  CT.normal_annotations D = true ->
  CT.normal_annotations (fst (generate_from todo D)) = true /\
  CT.normal_annotations (snd (generate_from todo D)) = true.
Proof.
  induction todo as [|r todo IH]; intros n rs D HD; cbn [generate_from]; [split; [reflexivity | exact HD] |].
  destruct (generate_from todo (next_domains D r)) as [P E] eqn:Hgen; cbn.
  pose proof (IH _ _ (next_domains D r) (next_domains_normal _ _ D r HD)) as H.
  rewrite Hgen in H; cbn in H; destruct H as [HP HE]; split; [| exact HE].
  cbn [CT.normal_annotations]; rewrite CT.close_type_normal, HD, HP; reflexivity.
Qed.

Theorem generated_formed n rs (G : Ctx nat n) :
  CT.formed G (parameters n rs) /\ CT.formed (CT.context (parameters n rs) G) (domains n rs).
Proof. apply generate_from_formed; exact I. Qed.

Theorem generated_normal n rs :
  CT.normal_annotations (parameters n rs) = true /\ CT.normal_annotations (domains n rs) = true.
Proof. apply generate_from_normal; reflexivity. Qed.

Print Assumptions base_typing.
Print Assumptions lift_sub_base.
Print Assumptions apply_under_typed.
Print Assumptions apply_under_replace.
Print Assumptions apply_under_rename.
Print Assumptions apply_under_reduces.
Print Assumptions apply_under_closure.
Print Assumptions apply_under_normal.
Print Assumptions apply_under_neutral.
Print Assumptions snoc_formed.
Print Assumptions snoc_normal.
Print Assumptions extend_ranks_exact.
Print Assumptions parameter_count.
Print Assumptions parameter_ranks_bounded.
Print Assumptions parameters_rank_bound.
Print Assumptions apply_under_annotations_irrelevant.
Print Assumptions generated_formed.
Print Assumptions generated_normal.
End UniformTelescope.
