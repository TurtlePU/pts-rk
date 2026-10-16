(** Finite certificates for EXACTLY the original annotated PTS typing rules.
    This exhaustive proof search is separate from the efficient native checker.
    Completeness here supports constructive witness selection, not new rules. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks Reduction DefEq AbstractRewriting.
From Interpretation_of_R Require Import DirectRKernel DirectREval.
Import ListNotations.
Module DerivationCertificates.
Import Core RkEval.
Inductive tree := tip : nat -> tree | node : nat -> tree -> tree -> tree -> tree.
Fixpoint steps {n} (t : Term nat n) : list (Term nat n) :=
  match t with
  | 𝓤 _ | var _ => []
  | Π A B => map (fun A' => Π A' B) (steps A) ++ map (Π A) (steps B)
  | lam A b => map (fun A' => lam A' b) (steps A) ++ map (lam A) (steps b)
  | app f u => map (fun f' => app f' u) (steps f) ++ map (app f) (steps u) ++
      match f with lam A b => [subst b u] | _ => [] end
  end.
Lemma steps_sound {n} (t u : Term nat n) : In u (steps t) -> step nat n t u.
Proof.
  revert u. induction t; intros u H; cbn [steps] in H; try contradiction.
  - apply in_app_iff in H as [H|H]; apply in_map_iff in H as [v [<- H]]; constructor; auto.
  - apply in_app_iff in H as [H|H]; apply in_map_iff in H as [v [<- H]]; constructor; auto.
  - apply in_app_iff in H as [H|H].
    + apply in_map_iff in H as [v [<- H]]. constructor. auto.
    + apply in_app_iff in H as [H|H].
      * apply in_map_iff in H as [v [<- H]]. constructor. auto.
      * destruct t1; try contradiction. destruct H as [<-|[]]. apply step_beta.
Qed.
Lemma steps_complete {n} (t u : Term nat n) : step nat n t u -> In u (steps t).
Proof.
  intro H. induction H; cbn [steps]; apply in_app_iff.
  - left. apply in_map_iff. eexists. split; [reflexivity |exact IHstep].
  - right. apply in_map_iff. eexists. split; [reflexivity |exact IHstep].
  - left. apply in_map_iff. eexists. split; [reflexivity |exact IHstep].
  - right. apply in_map_iff. eexists. split; [reflexivity |exact IHstep].
  - left. apply in_map_iff. eexists. split; [reflexivity |exact IHstep].
  - right. apply in_app_iff. left. apply in_map_iff. eexists. split; [reflexivity |exact IHstep].
  - right. apply in_app_iff. right. left. reflexivity.
Qed.
Fixpoint run {n} (c : tree) (t : Term nat n) : Term nat n :=
  match c with
  | tip _ => t
  | node i tail _ _ => match nth_error (steps t) i with Some u => run tail u | None => t end
  end.
Lemma run_sound c : forall n (t : Term nat n), t ↠ᵝ run c t.
Proof.
  induction c; intros k t; cbn [run]; [reflexivity |].
  destruct (nth_error (steps t) n) as [u|] eqn:E; [|reflexivity].
  eapply rtc_step; [apply steps_sound; eapply nth_error_In; exact E |apply IHc1].
Qed.
Lemma run_complete {n} (t u : Term nat n) : t ↠ᵝ u -> exists c, run c t = u.
Proof.
  intro H. induction H.
  - exists (tip 0). reflexivity.
  - destruct IHRTC as [c Hc]. apply steps_complete in H.
    apply In_nth_error in H as [i Hi]. exists (node i c (tip 0) (tip 0)). cbn [run]. rewrite Hi. exact Hc.
Qed.
Lemma term_eqb_refl {n} (t : Term nat n) : term_eqb t t = true.
Proof.
  induction t; cbn [term_eqb]; try rewrite IHt1, IHt2; try reflexivity.
  - apply Nat.eqb_refl.
  - induction f; cbn [fin_eqb]; auto.
Qed.
Definition conversion {n} c (t u : Term nat n) :=
  match c with tip _ => term_eqb t u | node _ a b _ => term_eqb (run a t) (run b u) end.
Lemma conversion_sound {n} c (t u : Term nat n) : conversion c t u = true -> t =ᵝ u.
Proof.
  destruct c; cbn [conversion]; intro H; apply term_eqb_sound in H.
  - subst. reflexivity.
  - apply def_equiv_prop. exists (run c1 t). split; [apply run_sound |rewrite H; apply run_sound].
Qed.
Lemma conversion_complete {n} (t u : Term nat n) : t =ᵝ u -> exists c, conversion c t u = true.
Proof.
  rewrite def_equiv_prop. intros [v [Ht Hu]].
  apply run_complete in Ht as [a Ha]. apply run_complete in Hu as [b Hb].
  exists (node 0 a b (tip 0)). cbn [conversion]. rewrite Ha, Hb. apply term_eqb_refl.
Qed.
Fixpoint index (n i : nat) : option (Fin n) :=
  match n with 0 => None | S n => match i with 0 => Some fzero | S i => option_map fsucc (index n i) end end.
Lemma index_complete {n} (i : Fin n) : exists k, index n k = Some i.
Proof. induction i; [exists 0; reflexivity |destruct IHi as [k Hk]; exists (S k); cbn; rewrite Hk; reflexivity]. Qed.
Fixpoint derive (c : tree) {n} (Γ : Ctx nat n) : option (Term nat n * Term nat n) :=
  match c with
  | tip r => Some (𝓤 r, 𝓤 0)
  | node tag a b e =>
    match tag with
    | 0 => match a with tip i => match index n i with Some j => Some (var j, Γ !! j) |None => None end | _ => None end
    | 1 => match derive a Γ with
      | Some (A, 𝓤 r) => match derive b (Γ & A) with
        | Some (B, 𝓤 s) => Some (Π A B, 𝓤 (Nat.max (S r) s)) | _ => None end | _ => None end
    | 2 => match derive a Γ with
      | Some (A, 𝓤 r) => match derive b (Γ & A) with
        | Some (t, B) => Some (lam A t, Π A B) | _ => None end | _ => None end
    | 3 => match derive a Γ, derive b Γ with
      | Some (f, Π A B), Some (u, A') => if term_eqb A' A then Some (app f u, subst B u) else None
      | _, _ => None end
    | 4 => match derive a Γ, derive b Γ with
      | Some (t, A), Some (B, 𝓤 r) => if conversion e A B then Some (t, B) else None
      | _, _ => None end
    | _ => None end
  end.
Theorem derive_sound c : forall n (Γ : Ctx nat n) t A,
  derive c Γ = Some (t,A) -> Typed Γ t A.
Proof.
  induction c as [r|tag a IHa b IHb e IHe]; intros n Γ t A H; cbn [derive] in H.
  - inversion H; subst. constructor. reflexivity.
  - destruct tag as [|[|[|[|[|tag]]]]]; try discriminate.
    + destruct a; try discriminate. destruct (index n n0) eqn:E; try discriminate.
      inversion H; subst. constructor.
    + destruct (derive a Γ) as [[T R]|] eqn:Ha; try discriminate.
      destruct R; try discriminate. destruct (derive b (Γ & T)) as [[U S]|] eqn:Hb; try discriminate.
      destruct S; try discriminate. inversion H; subst.
      eapply typ_Π; [eapply IHa; exact Ha |eapply IHb; exact Hb |reflexivity].
    + destruct (derive a Γ) as [[T R]|] eqn:Ha; try discriminate.
      destruct R; try discriminate. destruct (derive b (Γ & T)) as [[u U]|] eqn:Hb; try discriminate.
      inversion H; subst. eapply typ_λ; [eapply IHa; exact Ha |eapply IHb; exact Hb].
    + destruct (derive a Γ) as [[f R]|] eqn:Ha; try discriminate.
      destruct R; try discriminate. destruct (derive b Γ) as [[u U]|] eqn:Hb; try discriminate.
      destruct (term_eqb U R1) eqn:Heq; try discriminate. apply term_eqb_sound in Heq. subst U.
      inversion H; subst. eapply typ_app; [eapply IHa; exact Ha |eapply IHb; exact Hb].
    + destruct (derive a Γ) as [[u U]|] eqn:Ha; try discriminate.
      destruct (derive b Γ) as [[T R]|] eqn:Hb; try discriminate. destruct R; try discriminate.
      destruct (conversion e U T) eqn:Heq; try discriminate. inversion H; subst.
      eapply typ_conv; [eapply IHa; exact Ha |eapply IHb; exact Hb |eapply conversion_sound; exact Heq].
Qed.
Theorem derive_complete {n} (Γ : Ctx nat n) t A : Typed Γ t A -> exists c, derive c Γ = Some (t,A).
Proof.
  intro H. induction H.
  - change (ℓ' = 0) in H. subst. exists (tip ℓ). reflexivity.
  - destruct IHtyp1 as [a Ha], IHtyp2 as [b Hb].
    change (ℓ = Nat.max (S ℓₜ) ℓᵤ) in H1. subst.
    exists (node 1 a b (tip 0)). cbn [derive]. rewrite Ha, Hb. reflexivity.
  - destruct (index_complete i) as [j Hj]. exists (node 0 (tip j) (tip 0) (tip 0)). cbn [derive]. rewrite Hj. reflexivity.
  - destruct IHtyp1 as [a Ha], IHtyp2 as [b Hb].
    exists (node 2 a b (tip 0)). cbn [derive]. rewrite Ha, Hb. reflexivity.
  - destruct IHtyp1 as [a Ha], IHtyp2 as [b Hb].
    exists (node 3 a b (tip 0)). cbn [derive]. rewrite Ha, Hb, term_eqb_refl. reflexivity.
  - destruct IHtyp1 as [a Ha], IHtyp2 as [b Hb].
    destruct (conversion_complete _ _ H1) as [e He].
    exists (node 4 a b e). cbn [derive]. rewrite Ha, Hb, He. reflexivity.
Qed.
End DerivationCertificates.
