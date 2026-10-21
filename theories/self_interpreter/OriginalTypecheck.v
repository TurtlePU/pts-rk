From Stdlib Require Import Bool.Bool Arith.PeanoNat.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Inversions DefEq Reduction AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import Greedy.
From PTSrk.SelfInterpreter Require Import OpenCanonical FullConversion.
Import Context.

(** Executable metalevel inference for the ORIGINAL annotated PTS. This is
    intended to filter independently specified finite signature candidates.
    It neither changes original Typing.typ nor supplies a source quoter. *)
Module OriginalTypecheck.
Module OC := OpenCanonical.OpenCanonical.
Module FC := FullConversion.FullConversion.

Definition sort_view {n} (G : Ctx nat n) (T : Term nat n) : option nat :=
  match OC.nf G T with 𝓤 r => Some r | _ => None end.

Fixpoint infer {n} (G : Ctx nat n) (t : Term nat n) : option (Term nat n) :=
  match t with
  | 𝓤 r => Some (𝓤 0)
  | var i => Some (G !! i)
  | Π A B =>
      match infer G A, infer (G & A) B with
      | Some TA, Some TB =>
          match sort_view G TA, sort_view (G & A) TB with
          | Some a, Some b => Some (𝓤 (Nat.max (S a) b))
          | _, _ => None
          end
      | _, _ => None
      end
  | lam A b =>
      match infer G A, infer (G & A) b with
      | Some TA, Some B =>
          match sort_view G TA with Some _ => Some (Π A B) | None => None end
      | _, _ => None
      end
  | app f u =>
      match infer G f, infer G u with
      | Some TF, Some TU =>
          match OC.nf G TF with
          | Π A B => if FC.convertibleb G TU A then Some (subst B u) else None
          | _ => None
          end
      | _, _ => None
      end
  end.

Lemma sort_view_sound n (G : Ctx nat n) T r :
  sort_view G T = Some r -> def_equiv nat n T (𝓤 r).
Proof.
  unfold sort_view; destruct (OC.nf G T) eqn:HE; intro H; try discriminate.
  inversion H; subst; rewrite <- HE; apply OC.nf_conversion.
Qed.

Lemma sort_retype n (G : Ctx nat n) A T r :
  @typ nat RankSorts n G A T -> sort_view G T = Some r ->
  @typ nat RankSorts n G A (𝓤 r).
Proof.
  intros HA Hr; eapply typ_conv with (T := T) (ℓ := 0).
  - exact HA.
  - apply typ_𝓤; reflexivity.
  - apply (sort_view_sound n G T r); exact Hr.
Qed.

Theorem infer_sound n (t : Term nat n) : forall G T,
  @wf nat RankSorts n G -> infer G t = Some T -> @typ nat RankSorts n G t T.
Proof.
  induction t; intros G T HG H; cbn [infer] in H.
  - inversion H; subst T; apply typ_𝓤; reflexivity.
  - destruct (infer G t1) as [TA |] eqn:HA; try discriminate.
    destruct (infer (G & t1) t2) as [TB |] eqn:HB; try discriminate.
    destruct (sort_view G TA) as [a |] eqn:Hsa; try discriminate.
    destruct (sort_view (G & t1) TB) as [b |] eqn:Hsb; try discriminate.
    inversion H; subst T.
    assert (HAt : typ G t1 (𝓤 a)) by (eapply sort_retype; [apply IHt1; eassumption | exact Hsa]).
    eapply typ_Π with (ℓₜ := a) (ℓᵤ := b); [exact HAt | | reflexivity].
    eapply sort_retype; [apply IHt2; [eapply wf_cons; eassumption | exact HB] | exact Hsb].
  - inversion H; subst T; apply typ_var.
  - destruct (infer G t1) as [TA |] eqn:HA; try discriminate.
    destruct (infer (G & t1) t2) as [B |] eqn:HB; try discriminate.
    destruct (sort_view G TA) as [a |] eqn:Hsa; try discriminate.
    inversion H; subst T.
    assert (HAt : typ G t1 (𝓤 a)) by (eapply sort_retype; [apply IHt1; eassumption | exact Hsa]).
    eapply typ_λ with (ℓ := a); [exact HAt | apply IHt2; [eapply wf_cons; eassumption | exact HB]].
  - destruct (infer G t1) as [TF |] eqn:HF; try discriminate.
    destruct (infer G t2) as [TU |] eqn:HU; try discriminate.
    destruct (OC.nf G TF) as [r | A B | i | A b | f u] eqn:HN; try discriminate.
    destruct (FC.convertibleb G TU A) eqn:HE; try discriminate; inversion H; subst T.
    pose proof (IHt1 G TF HG HF) as Hf.
    pose proof (IHt2 G TU HG HU) as Hu.
    destruct (type_is_correct _ _ Hf HG) as [s HS].
    assert (HP : typ G (Π A B) (𝓤 s)) by (rewrite <- HN; apply OC.nf_typed; assumption).
    pose proof (Π_inversion RankSorts A (𝓤 s) B HP) as HV.
    destruct HV as [a [b [c [Hrule [HA [HB Hsort]]]]]].
    eapply typ_app with (U := A).
    + eapply typ_conv with (T := TF) (ℓ := s); [exact Hf | exact HP | rewrite <- HN; apply OC.nf_conversion].
    + eapply typ_conv with (T := TU) (ℓ := a); [exact Hu | exact HA |].
      unfold FC.convertibleb in HE; destruct (FC.join_attempt G TU A) as [j |];
        [apply (FC.joining_sound _ _ _ j) | discriminate].
Qed.

Lemma infer_sort n (G : Ctx nat n) A T a :
  @wf nat RankSorts n G -> @typ nat RankSorts n G A (𝓤 a) -> infer G A = Some T ->
  sort_view G T = Some a.
Proof.
  intros HG HA HI; pose proof (infer_sound n A G T HG HI) as HT.
  destruct (type_is_correct _ _ HT HG) as [s HS].
  assert (HE : def_equiv nat n T (𝓤 a)) by (eapply uniqueness_of_typing; eassumption).
  assert (HN : OC.nf G T = 𝓤 a).
  { eapply OC.nf_unique; [exact HG | exact HS | reflexivity | exact HE]. }
  unfold sort_view; rewrite HN; reflexivity.
Qed.

Lemma inferred_product n (G : Ctx nat n) f TF A B :
  @wf nat RankSorts n G -> @typ nat RankSorts n G f TF ->
  @typ nat RankSorts n G f (Π A B) ->
  exists A' B', OC.nf G TF = Π A' B' /\
    def_equiv nat n A' A /\ def_equiv nat (S n) B' B.
Proof.
  intros HG HF HP.
  destruct (type_is_correct _ _ HF HG) as [s HS].
  destruct (type_is_correct _ _ HP HG) as [p HPS].
  assert (HE : def_equiv nat n TF (Π A B)) by (eapply uniqueness_of_typing; eassumption).
  assert (HN : OC.nf G TF = OC.nf G (Π A B)).
  { apply (proj2 (OC.nf_conversion_iff n G G TF (Π A B) (𝓤 s) (𝓤 p) HG HG HS HPS)); exact HE. }
  destruct (rtc_Π_repr A (OC.nf G (Π A B)) B (OC.nf_reduces n G (Π A B))) as [A' [B' HPi]].
  exists A', B'; split; [now rewrite HN |].
  apply equiv_Π_inversion.
  rewrite <- HPi; symmetry; apply OC.nf_conversion.
Qed.

Theorem infer_complete n G t T : @typ nat RankSorts n G t T ->
  @wf nat RankSorts n G -> exists U, infer G t = Some U.
Proof.
  intro HT; induction HT as
    [n G r s Hax | n G A B a b c HA IHA HB IHB Hr | n G i |
     n G A t B a HA IHA Ht IHt | n G f B u A Hf IHf Hu IHu |
     n G t B A b Ht IHt HB IHB He]; intro HG.
  - eexists; reflexivity.
  - destruct (IHA HG) as [TA HIA].
    assert (HGA : @wf nat RankSorts _ (G & A)) by (eapply wf_cons; eassumption).
    destruct (IHB HGA) as [TB HIB].
    pose proof (infer_sort n G A TA a HG HA HIA) as Hsa.
    pose proof (infer_sort (S n) (G & A) B TB b HGA HB HIB) as Hsb.
    cbn [infer]; rewrite HIA, HIB, Hsa, Hsb; eexists; reflexivity.
  - eexists; reflexivity.
  - destruct (IHA HG) as [TA HIA].
    assert (HGA : @wf nat RankSorts _ (G & A)) by (eapply wf_cons; eassumption).
    destruct (IHt HGA) as [TB HIB].
    pose proof (infer_sort n G A TA a HG HA HIA) as Hsa.
    cbn [infer]; rewrite HIA, HIB, Hsa; eexists; reflexivity.
  - destruct (IHf HG) as [TF HIF], (IHu HG) as [TU HIU].
    pose proof (infer_sound n f G TF HG HIF) as HF.
    pose proof (infer_sound n u G TU HG HIU) as HU.
    destruct (inferred_product n G f TF A B HG HF Hf) as [A' [B' [HN [HEA HEB]]]].
    destruct (type_is_correct _ _ HF HG) as [s HS].
    assert (HP : typ G (Π A' B') (𝓤 s)) by (rewrite <- HN; apply OC.nf_typed; assumption).
    destruct (Π_inversion RankSorts A' (𝓤 s) B' HP) as [a [b [c [Hr [HA' [HB' HC]]]]]].
    destruct (type_is_correct _ _ HU HG) as [r HUS].
    assert (HE : FC.convertibleb G TU A' = true).
    { apply (proj2 (FC.convertibleb_correct n G TU A' (𝓤 r) (𝓤 a) HG HUS HA')).
      transitivity A; [eapply uniqueness_of_typing; eassumption | symmetry; exact HEA]. }
    cbn [infer]; rewrite HIF, HIU, HN, HE; eexists; reflexivity.
  - apply IHt; exact HG.
Qed.

Theorem inferred_type_agrees n G t T U :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T -> infer G t = Some U ->
  def_equiv nat n U T.
Proof. intros HG HT HI; eapply uniqueness_of_typing; [eapply infer_sound; eassumption | exact HT]. Qed.

Definition type_sort {n} (G : Ctx nat n) (T : Term nat n) : option nat :=
  match infer G T with Some U => sort_view G U | None => None end.

Theorem type_sort_sound n G T r :
  @wf nat RankSorts n G -> type_sort G T = Some r -> @typ nat RankSorts n G T (𝓤 r).
Proof.
  intros HG; unfold type_sort; destruct (infer G T) as [U |] eqn:HI; [| discriminate].
  intro HS; eapply sort_retype; [apply infer_sound; eassumption | exact HS].
Qed.

Theorem type_sort_complete n G T r :
  @wf nat RankSorts n G -> @typ nat RankSorts n G T (𝓤 r) -> type_sort G T = Some r.
Proof.
  intros HG HT; destruct (infer_complete n G T (𝓤 r) HT HG) as [U HU].
  unfold type_sort; rewrite HU; apply (infer_sort n G T U r); assumption.
Qed.

Definition check {n} (G : Ctx nat n) (t T : Term nat n) : bool :=
  match infer G t, type_sort G T with
  | Some U, Some _ => FC.convertibleb G U T
  | _, _ => false
  end.

Theorem check_sound n G t T :
  @wf nat RankSorts n G -> check G t T = true -> @typ nat RankSorts n G t T.
Proof.
  intros HG; unfold check; destruct (infer G t) as [U |] eqn:HI; [| discriminate].
  destruct (type_sort G T) as [r |] eqn:HS; [| discriminate].
  intro HE; eapply typ_conv with (T := U) (ℓ := r).
  - apply infer_sound; eassumption.
  - apply type_sort_sound; assumption.
  - unfold FC.convertibleb in HE; destruct (FC.join_attempt G U T) as [j |];
      [apply (FC.joining_sound _ _ _ j) | discriminate].
Qed.

Theorem check_complete n G t T :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T -> check G t T = true.
Proof.
  intros HG HT; destruct (infer_complete n G t T HT HG) as [U HI].
  destruct (type_is_correct _ _ HT HG) as [r HS].
  pose proof (infer_sound n t G U HG HI) as HU.
  destruct (type_is_correct _ _ HU HG) as [s HUS].
  unfold check; rewrite HI, (type_sort_complete n G T r HG HS).
  apply (proj2 (FC.convertibleb_correct n G U T (𝓤 s) (𝓤 r) HG HUS HS)).
  eapply uniqueness_of_typing; eassumption.
Qed.

Theorem check_iff n G t T :
  @wf nat RankSorts n G -> (check G t T = true <-> @typ nat RankSorts n G t T).
Proof. intro HG; split; [apply check_sound | apply check_complete]; exact HG. Qed.

Example sort_inference_computes : infer ε (𝓤 7) = Some (𝓤 0).
Proof. reflexivity. Qed.
Example dependent_identity_computes :
  check ε (lam (𝓤 0) (lam (var fzero) (var fzero)))
    (Π (𝓤 0) (Π (var fzero) (var (fsucc fzero)))) = true.
Proof. vm_compute; reflexivity. Qed.
Example ill_typed_application_rejected : check ε (app (𝓤 0) (𝓤 0)) (𝓤 0) = false.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions infer_sound.
Print Assumptions infer_complete.
Print Assumptions inferred_type_agrees.
Print Assumptions type_sort_sound.
Print Assumptions type_sort_complete.
Print Assumptions check_sound.
Print Assumptions check_complete.
Print Assumptions check_iff.
End OriginalTypecheck.
