From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting DefEq.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import LocalQuotationSpine ContextualTelescope
  UniformTelescope UniformTelescopeRecovery OpenTelescopeRecovery ContextReification.
Import Context ListNotations.

Module LocalSpineNaturality.
Module CT := ContextualTelescope.ContextualTelescope.
Module UT := UniformTelescope.UniformTelescope.
Module UR := UniformTelescopeRecovery.UniformTelescopeRecovery.
Module OR := OpenTelescopeRecovery.OpenTelescopeRecovery.
Module CR := ContextReification.ContextReification.

Fixpoint profile {base n} (D : LocalQuotationSpine.LocalQuotationSpine.spine base n) : list nat :=
  match D with LocalQuotationSpine.LocalQuotationSpine.empty => [] | LocalQuotationSpine.LocalQuotationSpine.push E r _ => profile E ++ [r] end.
Fixpoint close_type {base n} (D : LocalQuotationSpine.LocalQuotationSpine.spine base n) : Term nat (n+base) -> Term nat base :=
  match D in LocalQuotationSpine.LocalQuotationSpine.spine _ m return Term nat (m+base) -> Term nat base with
  | LocalQuotationSpine.LocalQuotationSpine.empty => fun T => T
  | LocalQuotationSpine.LocalQuotationSpine.push E _ A => fun T => close_type E (Π A T)
  end.

Lemma push_profile base n m G H condition annotations local_fill
    (P : @LocalQuotationSpine.LocalQuotationSpine.presentation base n m G H condition annotations local_fill) r A :
  LocalQuotationSpine.LocalQuotationSpine.ranks (LocalQuotationSpine.LocalQuotationSpine.present_push P r A) = LocalQuotationSpine.LocalQuotationSpine.ranks P ++ [r].
Proof. destruct P as [rs D es et HE HF HN HS]; destruct et; destruct es; reflexivity. Qed.
Lemma presented_profile base n (D : LocalQuotationSpine.LocalQuotationSpine.spine base n) G : LocalQuotationSpine.LocalQuotationSpine.ranks (LocalQuotationSpine.LocalQuotationSpine.present D G)=profile D.
Proof.
  induction D; [reflexivity |].
  change (LocalQuotationSpine.LocalQuotationSpine.ranks (LocalQuotationSpine.LocalQuotationSpine.present_push (LocalQuotationSpine.LocalQuotationSpine.present D G) r A)=profile D ++ [r]).
  rewrite push_profile, IHD; reflexivity.
Qed.
Lemma rename_profile base n (D : LocalQuotationSpine.LocalQuotationSpine.spine base n) target rho :
  profile (LocalQuotationSpine.LocalQuotationSpine.rename_spine D target rho)=profile D.
Proof. induction D; cbn [profile LocalQuotationSpine.LocalQuotationSpine.rename_spine]; [reflexivity | now rewrite IHD]. Qed.

Lemma snoc_close_type n rs (D : CT.telescope n rs) r A T :
  CT.close_type (UT.snoc D r A) (CR.cast_term (eq_sym (UR.scope_snoc rs n r)) T) =
  CT.close_type D (Π A T).
Proof.
  induction D; cbn [UT.snoc CT.close_type UR.scope_snoc CR.cast_term];
    [reflexivity | f_equal; apply IHD].
Qed.
Lemma push_close_type base n m G H condition annotations local_fill
    (P : @LocalQuotationSpine.LocalQuotationSpine.presentation base n m G H condition annotations local_fill) r A T :
  CT.close_type (LocalQuotationSpine.LocalQuotationSpine.telescope (LocalQuotationSpine.LocalQuotationSpine.present_push P r A)) (LocalQuotationSpine.LocalQuotationSpine.body (LocalQuotationSpine.LocalQuotationSpine.present_push P r A) T) =
  CT.close_type (LocalQuotationSpine.LocalQuotationSpine.telescope P) (LocalQuotationSpine.LocalQuotationSpine.body P (Π A T)).
Proof.
  destruct P as [rs D es et HE HF HN HS]; destruct et; destruct es.
  change (CT.close_type (UT.snoc D r A) (CR.cast_term (eq_sym (UR.scope_snoc rs base r)) T) =
    CT.close_type D (Π A T)).
  apply snoc_close_type.
Qed.
Theorem presented_close_type base n (D : LocalQuotationSpine.LocalQuotationSpine.spine base n) G T :
  CT.close_type (LocalQuotationSpine.LocalQuotationSpine.telescope (LocalQuotationSpine.LocalQuotationSpine.present D G)) (LocalQuotationSpine.LocalQuotationSpine.body (LocalQuotationSpine.LocalQuotationSpine.present D G) T) = close_type D T.
Proof.
  revert T; induction D; intro T; [reflexivity |].
  change (CT.close_type (LocalQuotationSpine.LocalQuotationSpine.telescope (LocalQuotationSpine.LocalQuotationSpine.present_push (LocalQuotationSpine.LocalQuotationSpine.present D G) r A))
    (LocalQuotationSpine.LocalQuotationSpine.body (LocalQuotationSpine.LocalQuotationSpine.present_push (LocalQuotationSpine.LocalQuotationSpine.present D G) r A) T) = close_type D (Π A T)).
  rewrite push_close_type; apply IHD.
Qed.
Theorem close_type_rename base n (D : LocalQuotationSpine.LocalQuotationSpine.spine base n) target rho T :
  rename rho (close_type D T) =
  close_type (LocalQuotationSpine.LocalQuotationSpine.rename_spine D target rho) (rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren n rho) T).
Proof.
  revert T; induction D; intro T; cbn [close_type LocalQuotationSpine.LocalQuotationSpine.rename_spine LocalQuotationSpine.LocalQuotationSpine.lift_ren]; [reflexivity |].
  rewrite IHD; reflexivity.
Qed.

Definition cast_ranks {base rs qs} (e : rs=qs) (D : CT.telescope base rs) : CT.telescope base qs :=
  match e with eq_refl => D end.
Lemma cast_ranks_close_type base rs qs (e : rs=qs) (D : CT.telescope base rs) T :
  CT.close_type (cast_ranks e D) (CR.cast_term (f_equal (fun p => CT.scope p base) e) T) =
  CT.close_type D T.
Proof. destruct e; reflexivity. Qed.
Lemma cast_sort m n (e : m=n) r : CR.cast_term e (𝓤 r)=𝓤 r.
Proof. destruct e; reflexivity. Qed.
Lemma body_sort base n m G H condition annotations local_fill
    (P : @LocalQuotationSpine.LocalQuotationSpine.presentation base n m G H condition annotations local_fill) r : LocalQuotationSpine.LocalQuotationSpine.body P (𝓤 r)=𝓤 r.
Proof. unfold LocalQuotationSpine.LocalQuotationSpine.body; apply cast_sort. Qed.
Lemma telescope_from_closure base rs (D : CT.telescope base rs) : forall E,
  CT.close_type D (𝓤 0)=CT.close_type E (𝓤 0) -> D=E.
Proof.
  induction D; intros E HE; dependent elimination E; [reflexivity |].
  cbn [CT.close_type] in HE; injection HE as HA HT; subst; f_equal; apply IHD; exact HT.
Qed.
Lemma closure_injective base rs (D : CT.telescope base rs) T U :
  CT.close_type D T=CT.close_type D U -> T=U.
Proof. induction D; cbn [CT.close_type]; intro H; [exact H | apply IHD; now injection H]. Qed.

Definition renamed_profile base n (D : LocalQuotationSpine.LocalQuotationSpine.spine base n) G target H rho :
  LocalQuotationSpine.LocalQuotationSpine.ranks (LocalQuotationSpine.LocalQuotationSpine.present D G)=LocalQuotationSpine.LocalQuotationSpine.ranks (LocalQuotationSpine.LocalQuotationSpine.present (LocalQuotationSpine.LocalQuotationSpine.rename_spine D target rho) H).
Proof. rewrite !presented_profile, rename_profile; reflexivity. Defined.

Theorem presented_telescope_rename base n (D : LocalQuotationSpine.LocalQuotationSpine.spine base n) G target H rho :
  cast_ranks (renamed_profile base n D G target H rho)
    (CT.rename_telescope (LocalQuotationSpine.LocalQuotationSpine.telescope (LocalQuotationSpine.LocalQuotationSpine.present D G)) target rho) =
  LocalQuotationSpine.LocalQuotationSpine.telescope (LocalQuotationSpine.LocalQuotationSpine.present (LocalQuotationSpine.LocalQuotationSpine.rename_spine D target rho) H).
Proof.
  apply telescope_from_closure.
  rewrite <- (cast_sort _ _ (f_equal (fun rs => CT.scope rs target)
    (renamed_profile base n D G target H rho)) 0).
  rewrite cast_ranks_close_type, cast_sort.
  change (CT.close_type (CT.rename_telescope (LocalQuotationSpine.LocalQuotationSpine.telescope (LocalQuotationSpine.LocalQuotationSpine.present D G)) target rho)
    (rename (CT.lift_ren (LocalQuotationSpine.LocalQuotationSpine.ranks (LocalQuotationSpine.LocalQuotationSpine.present D G)) rho) (𝓤 0)) =
    CT.close_type (LocalQuotationSpine.LocalQuotationSpine.telescope (LocalQuotationSpine.LocalQuotationSpine.present (LocalQuotationSpine.LocalQuotationSpine.rename_spine D target rho) H)) (𝓤 0)).
  rewrite <- CT.close_type_rename, <- (body_sort _ _ _ _ _ _ _ _ (LocalQuotationSpine.LocalQuotationSpine.present D G) 0),
    presented_close_type, close_type_rename.
  rewrite <- (body_sort _ _ _ _ _ _ _ _ (LocalQuotationSpine.LocalQuotationSpine.present (LocalQuotationSpine.LocalQuotationSpine.rename_spine D target rho) H) 0),
    presented_close_type; reflexivity.
Qed.

(** Replace only the profile presentation. Its telescope field is literally
    the supplied syntax; proof transports never enter an object term. *)
Definition retelescope {base n m G H condition annotations local_fill}
    (P : @LocalQuotationSpine.LocalQuotationSpine.presentation base n m G H condition annotations local_fill)
    rs (e : rs=LocalQuotationSpine.LocalQuotationSpine.ranks P) (D : CT.telescope base rs)
    (HD : cast_ranks e D=LocalQuotationSpine.LocalQuotationSpine.telescope P) :
    @LocalQuotationSpine.LocalQuotationSpine.presentation base n m G H condition annotations local_fill.
Proof.
  refine {| LocalQuotationSpine.LocalQuotationSpine.ranks := rs; LocalQuotationSpine.LocalQuotationSpine.telescope := D;
    LocalQuotationSpine.LocalQuotationSpine.source_scope := eq_trans (f_equal (fun p => CT.scope p 0) e) (LocalQuotationSpine.LocalQuotationSpine.source_scope P);
    LocalQuotationSpine.LocalQuotationSpine.target_scope := eq_trans (f_equal (fun p => CT.scope p base) e) (LocalQuotationSpine.LocalQuotationSpine.target_scope P) |}.
  all: destruct P as [qs E es et HE HF HN HS]; cbn in e; destruct e;
    cbn [cast_ranks LocalQuotationSpine.LocalQuotationSpine.telescope] in HD; subst D;
    cbn [LocalQuotationSpine.LocalQuotationSpine.source_scope LocalQuotationSpine.LocalQuotationSpine.target_scope]; try assumption.
  all: destruct et; destruct es; cbn in *; assumption.
Defined.

Definition renamed_presentation base n (D : LocalQuotationSpine.LocalQuotationSpine.spine base n) G target H rho :=
  retelescope (LocalQuotationSpine.LocalQuotationSpine.present (LocalQuotationSpine.LocalQuotationSpine.rename_spine D target rho) H)
    (LocalQuotationSpine.LocalQuotationSpine.ranks (LocalQuotationSpine.LocalQuotationSpine.present D G)) (renamed_profile base n D G target H rho)
    (CT.rename_telescope (LocalQuotationSpine.LocalQuotationSpine.telescope (LocalQuotationSpine.LocalQuotationSpine.present D G)) target rho)
    (presented_telescope_rename base n D G target H rho).

Lemma retelescope_close_type base n m G H condition annotations local_fill
    (P : @LocalQuotationSpine.LocalQuotationSpine.presentation base n m G H condition annotations local_fill)
    rs e D HD T :
  CT.close_type D (LocalQuotationSpine.LocalQuotationSpine.body (retelescope P rs e D HD) T)=
  CT.close_type (LocalQuotationSpine.LocalQuotationSpine.telescope P) (LocalQuotationSpine.LocalQuotationSpine.body P T).
Proof.
  destruct P as [qs E es et HE HF HN HS]; cbn in e; destruct e;
    cbn [cast_ranks LocalQuotationSpine.LocalQuotationSpine.telescope] in HD; subst D;
    destruct et; destruct es; reflexivity.
Qed.

Theorem renamed_body base n (D : LocalQuotationSpine.LocalQuotationSpine.spine base n) G target H rho t :
  LocalQuotationSpine.LocalQuotationSpine.body (renamed_presentation base n D G target H rho)
    (rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren n rho) t) =
  rename (CT.lift_ren (LocalQuotationSpine.LocalQuotationSpine.ranks (LocalQuotationSpine.LocalQuotationSpine.present D G)) rho) (LocalQuotationSpine.LocalQuotationSpine.body (LocalQuotationSpine.LocalQuotationSpine.present D G) t).
Proof.
  apply (closure_injective _ _ (CT.rename_telescope (LocalQuotationSpine.LocalQuotationSpine.telescope (LocalQuotationSpine.LocalQuotationSpine.present D G)) target rho)).
  unfold renamed_presentation; rewrite retelescope_close_type.
  rewrite <- CT.close_type_rename, !presented_close_type, close_type_rename; reflexivity.
Qed.

Theorem renamed_unbody base n (D : LocalQuotationSpine.LocalQuotationSpine.spine base n) G target H rho t :
  LocalQuotationSpine.LocalQuotationSpine.unbody (renamed_presentation base n D G target H rho)
    (rename (CT.lift_ren (LocalQuotationSpine.LocalQuotationSpine.ranks (LocalQuotationSpine.LocalQuotationSpine.present D G)) rho) (LocalQuotationSpine.LocalQuotationSpine.body (LocalQuotationSpine.LocalQuotationSpine.present D G) t)) =
  rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren n rho) t.
Proof.
  rewrite <- (renamed_body base n D G target H rho t), LocalQuotationSpine.LocalQuotationSpine.unbody_body; reflexivity.
Qed.

Print Assumptions presented_close_type.
Print Assumptions close_type_rename.
Print Assumptions presented_telescope_rename.
Print Assumptions renamed_presentation.
Print Assumptions renamed_body.
Print Assumptions renamed_unbody.

End LocalSpineNaturality.
