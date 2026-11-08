(** Uniform finite cuts for the corrected observer equality.
    The final existential is flattened: the motive has rank fifteen. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural DirectRLogic DirectRFiniteUp.
From Interpretation_of_R.relational Require Import DirectRUnary.
From OrderedSemiring Require Import RigCodes ObservationEquality.
Import ListNotations.

Module FiniteCuts.
Import CommonCodes Core Structural NegativeLogic FiniteUp.
Module RC := RigCodes.
Module OE := ObservationEquality.

Definition nD := NClosed Unary.Domain.
Definition nS := NClosed Unary.successor.
Definition nZ := NClosed Unary.zero.
Definition nG11 d := NApp (NClosed (RC.Good 11)) d.
Definition nBot := NClosed Bottom.
Definition nE d e := OE.nEq d e.
Definition nK f d := NPi 503 nD
  (nArrow (nG11 (NVar 503))
    (nArrow (nE d (NApp f (NVar 503))) nBot)).
Definition nLarge := nlams [(500,nArrow nD nD);(501,nD)]
  (nArrow (nK (NVar 500) (NVar 501)) nBot).
Definition large := close nLarge eq_refl.
Definition nL f d := napps (NClosed large) [f;d].
Definition nLargeIntro := nlams
  [(500,nArrow nD nD);(501,nD);(502,nD);(504,nG11 (NVar 502));
   (505,nE (NVar 501) (NApp (NVar 500) (NVar 502)));
   (506,nK (NVar 500) (NVar 501))]
  (napps (NVar 506) [NVar 502;NVar 504;NVar 505]).
Definition large_intro := close nLargeIntro eq_refl.
Definition large_intro_type := close
  (npis [(500,nArrow nD nD);(501,nD);(502,nD);(504,nG11 (NVar 502));
   (505,nE (NVar 501) (NApp (NVar 500) (NVar 502)))]
    (nL (NVar 500) (NVar 501))) eq_refl.
Definition nComm f := NPi 503 nD
  (nE (NApp nS (NApp f (NVar 503))) (NApp f (NApp nS (NVar 503)))).
Definition nLargeSuccessor := nlams
  [(500,nArrow nD nD);(507,nComm (NVar 500));(501,nD);
   (508,nL (NVar 500) (NVar 501));
   (506,nK (NVar 500) (NApp nS (NVar 501)))]
  (NApp (NVar 508)
    (nlams [(502,nD);(504,nG11 (NVar 502));
      (505,nE (NVar 501) (NApp (NVar 500) (NVar 502)))]
      (napps (NVar 506)
        [NApp nS (NVar 502);
         napps (NClosed (RC.good_successor 11)) [NVar 502;NVar 504];
         napps (NClosed OE.transitivity)
           [NApp nS (NVar 501);NApp nS (NApp (NVar 500) (NVar 502));
            NApp (NVar 500) (NApp nS (NVar 502));
            napps (NClosed OE.successor_congruence)
              [NVar 501;NApp (NVar 500) (NVar 502);NVar 505];
            NApp (NVar 507) (NVar 502)]]))).
Definition large_successor := close nLargeSuccessor eq_refl.
Definition large_successor_type := close
  (npis [(500,nArrow nD nD);(507,nComm (NVar 500));(501,nD);
    (508,nL (NVar 500) (NVar 501))]
    (nL (NVar 500) (NApp nS (NVar 501)))) eq_refl.
Definition large_stability := close
  (nlams [(500,nArrow nD nD);(501,nD);
    (508,RC.neg (RC.neg (nL (NVar 500) (NVar 501))));
    (506,nK (NVar 500) (NVar 501))]
    (NApp (NVar 508)
      (NLam 509 (nL (NVar 500) (NVar 501)) (NApp (NVar 509) (NVar 506))))) eq_refl.
Definition large_stability_type := close
  (npis [(500,nArrow nD nD);(501,nD)]
    (nArrow (RC.neg (RC.neg (nL (NVar 500) (NVar 501))))
      (nL (NVar 500) (NVar 501)))) eq_refl.

Lemma large_formation : Typed ε large
  (Arrow (Arrow Unary.Domain Unary.Domain) (Arrow Unary.Domain (𝓤 15))).
Proof. RkCheck.certify_with 4096. Qed.
Lemma large_intro_typed : Typed ε large_intro large_intro_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma large_successor_typed : Typed ε large_successor large_successor_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma large_stability_typed : Typed ε large_stability large_stability_type.
Proof. RkCheck.certify_with 4096. Qed.

Definition E {n} (d e : Term nat n) := app (app (lift_closed OE.Equality) d) e.
Definition G {n} r (d : Term nat n) := app (lift_closed (RC.Good r)) d.
Definition Succ {n} (d : Term nat n) := app (lift_closed Unary.successor) d.
Definition Large {n} (f d : Term nat n) := app (app (lift_closed large) f) d.
Definition Comm {n} (f : Term nat n) := Π (lift_closed Unary.Domain)
  (E (Succ (app (shift f) V0)) (app (shift f) (Succ V0))).

Lemma replace_E {m n} (s : Fin m -> Term nat n) d e :
  replace s (E d e) = E (replace s d) (replace s e).
Proof. unfold E. rewrite !replace_application, replace_lift_closed. reflexivity. Qed.
Lemma shift_E {n} (d e : Term nat n) : shift (E d e) = E (shift d) (shift e).
Proof. unfold shift. rewrite !rename_as_replace, replace_E. reflexivity. Qed.
Lemma shift_Succ {n} (d : Term nat n) : shift (Succ d) = Succ (shift d).
Proof. unfold Succ, shift. rewrite rename_application, rename_lift_closed. reflexivity. Qed.
Lemma shift_Large {n} (f d : Term nat n) :
  shift (Large f d) = Large (shift f) (shift d).
Proof. unfold Large, shift. rewrite !rename_application, rename_lift_closed. reflexivity. Qed.
Lemma equality_formation {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ e (lift_closed Unary.Domain) ->
  Typed Γ (E d e) (𝓤 7).
Proof.
  intros Hd He. pose proof (lift_closed_typed Γ _ _ OE.equality_formation) as H.
  change (Typed Γ (lift_closed OE.Equality)
    (Arrow (lift_closed Unary.Domain) (Arrow (lift_closed Unary.Domain) (𝓤 7)))) in H.
  exact (arrow_application _ _ _ _ _ (arrow_application _ _ _ _ _ H Hd) He).
Qed.
Lemma successor_formation {n} (Γ : Ctx nat n) d :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ (Succ d) (lift_closed Unary.Domain).
Proof.
  intro Hd. apply (arrow_application _ _ _ _ _ (Unary.successor_in_context Γ) Hd).
Qed.
Lemma large_formation_in_context {n} (Γ : Ctx nat n) f d :
  Typed Γ f (Arrow (lift_closed Unary.Domain) (lift_closed Unary.Domain)) ->
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ (Large f d) (𝓤 15).
Proof.
  intros Hf Hd. pose proof (lift_closed_typed Γ _ _ large_formation) as H.
  change (Typed Γ (lift_closed large)
    (Arrow (Arrow (lift_closed Unary.Domain) (lift_closed Unary.Domain))
      (Arrow (lift_closed Unary.Domain) (𝓤 15)))) in H.
  exact (arrow_application _ _ _ _ _ (arrow_application _ _ _ _ _ H Hf) Hd).
Qed.
Ltac cut_substitution H :=
  unfold E, G, Succ, Large, Comm in H; structural_substitution_in H.
Ltac cut_feed H Hu :=
  let J := fresh "Happ" in pose proof (tApp H Hu) as J;
  cut_substitution J; clear H; rename J into H.

Lemma equality_reflexivity {n} (Γ : Ctx nat n) d :
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (E d d).
Proof.
  intro Hd. pose proof (lift_closed_typed Γ _ _ OE.reflexivity_typed) as H.
  change (Typed Γ (lift_closed OE.reflexivity)
    (Π (lift_closed Unary.Domain) (E V0 V0))) in H.
  cut_feed H Hd. eexists. exact H.
Qed.
Lemma equality_successor {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ e (lift_closed Unary.Domain) ->
  inhabited Γ (E d e) -> inhabited Γ (E (Succ d) (Succ e)).
Proof.
  intros Hd He [p Hp]. pose proof (lift_closed_typed Γ _ _ OE.successor_congruence_typed) as H.
  change (Typed Γ (lift_closed OE.successor_congruence)
    (Π (lift_closed Unary.Domain) (Π (lift_closed Unary.Domain)
      (Arrow (E (shift V0) V0) (E (Succ (shift V0)) (Succ V0)))))) in H.
  cut_feed H Hd. cut_feed H He. eexists.
  exact (arrow_application _ _ _ _ _ H Hp).
Qed.
Lemma large_intro_in_context {n} (Γ : Ctx nat n) f d t :
  Typed Γ f (Arrow (lift_closed Unary.Domain) (lift_closed Unary.Domain)) ->
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ t (lift_closed Unary.Domain) ->
  inhabited Γ (G 11 t) -> inhabited Γ (E d (app f t)) -> inhabited Γ (Large f d).
Proof.
  intros Hf Hd Ht [g Hg] [e He].
  pose proof (lift_closed_typed Γ _ _ large_intro_typed) as H.
  change (Typed Γ (lift_closed large_intro)
    (Π (Arrow (lift_closed Unary.Domain) (lift_closed Unary.Domain))
      (Π (lift_closed Unary.Domain) (Π (lift_closed Unary.Domain)
        (Arrow (G 11 V0) (Arrow (E (shift V0) (app (shift (shift V0)) V0))
          (Large (shift (shift V0)) (shift V0)))))))) in H.
  cut_feed H Hf. cut_feed H Hd. cut_feed H Ht.
  eexists. exact (arrow_application _ _ _ _ _ (arrow_application _ _ _ _ _ H Hg) He).
Qed.
Lemma large_successor_in_context {n} (Γ : Ctx nat n) f d :
  Typed Γ f (Arrow (lift_closed Unary.Domain) (lift_closed Unary.Domain)) ->
  inhabited Γ (Comm f) -> Typed Γ d (lift_closed Unary.Domain) ->
  inhabited Γ (Large f d) -> inhabited Γ (Large f (Succ d)).
Proof.
  intros Hf [c Hc] Hd [p Hp].
  pose proof (lift_closed_typed Γ _ _ large_successor_typed) as H.
  change (Typed Γ (lift_closed large_successor)
    (Π (Arrow (lift_closed Unary.Domain) (lift_closed Unary.Domain))
      (Π (Comm V0) (Π (lift_closed Unary.Domain)
        (Arrow (Large (shift (shift V0)) V0)
          (Large (shift (shift V0)) (Succ V0))))))) in H.
  cut_feed H Hf. cut_feed H Hc. cut_feed H Hd.
  eexists. exact (arrow_application _ _ _ _ _ H Hp).
Qed.
Lemma large_stable {n} (Γ : Ctx nat n) f d :
  Typed Γ f (Arrow (lift_closed Unary.Domain) (lift_closed Unary.Domain)) ->
  Typed Γ d (lift_closed Unary.Domain) -> stable Γ (Large f d).
Proof.
  intros Hf Hd. pose proof (lift_closed_typed Γ _ _ large_stability_typed) as H.
  change (Typed Γ (lift_closed large_stability)
    (Π (Arrow (lift_closed Unary.Domain) (lift_closed Unary.Domain))
      (Π (lift_closed Unary.Domain)
        (Arrow (Neg (Neg (Large (shift V0) V0))) (Large (shift V0) V0))))) in H.
  unfold Neg in H. cut_feed H Hf. cut_feed H Hd. eexists. exact H.
Qed.

Fixpoint iterate {n} k (d : Term nat n) : Term nat n :=
  match k with 0 => d | S j => Succ (iterate j d) end.
Lemma iterate_typed {n} (Γ : Ctx nat n) k d :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ (iterate k d) (lift_closed Unary.Domain).
Proof. intro Hd. induction k; cbn [iterate]; auto using successor_formation. Qed.
Lemma iterate_commute {n} k (d : Term nat n) : iterate k (Succ d) = Succ (iterate k d).
Proof. induction k; cbn [iterate]; [reflexivity |]. rewrite IHk. reflexivity. Qed.
Lemma replace_iterate {m n} (s : Fin m -> Term nat n) k d :
  replace s (iterate k d) = iterate k (replace s d).
Proof.
  induction k; cbn [iterate]; [reflexivity |].
  unfold Succ. rewrite replace_application, replace_lift_closed, IHk. reflexivity.
Qed.
Definition iter_function k : closed_term := lam Unary.Domain (iterate k V0).
Lemma iter_function_typed k :
  Typed ε (iter_function k) (Arrow Unary.Domain Unary.Domain).
Proof.
  apply (tLam Unary.domain_formation), iterate_typed.
  exact (tV (ε & Unary.Domain) fzero).
Qed.
Lemma iter_function_beta {n} k (d : Term nat n) :
  app (lift_closed (iter_function k)) d =ᵝ iterate k d.
Proof.
  unfold iter_function, lift_closed. cbn [rename].
  transitivity (subst (rename (weak empty_renaming) (iterate k V0)) d).
  - apply beta_contract.
  - unfold subst. rewrite replace_rename, replace_iterate.
    change (iterate k d =ᵝ iterate k d). reflexivity.
Qed.
Lemma equation_of_beta {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ e (lift_closed Unary.Domain) ->
  d =ᵝ e -> inhabited Γ (E d e).
Proof.
  intros Hd He Hde. eapply inhabited_conversion.
  - apply equality_reflexivity. exact Hd.
  - apply equality_formation; assumption.
  - unfold E. apply beta_app; [reflexivity |exact Hde].
Qed.
Lemma iter_comm_realized k : Realizes (Comm (iter_function k)).
Proof.
  unfold Comm. rewrite Unary.shift_closed. apply product_intro.
  - exists 3. exact Unary.domain_formation.
  - assert (Hv : Typed (ε & Unary.Domain) V0 (lift_closed Unary.Domain))
      by exact (tV (ε & Unary.Domain) fzero).
    pose proof (lift_closed_typed (ε & Unary.Domain) _ _ (iter_function_typed k)) as Hf.
    change (Typed (ε & Unary.Domain) (lift_closed (iter_function k))
      (Arrow (lift_closed Unary.Domain) (lift_closed Unary.Domain))) in Hf.
    apply equation_of_beta.
    + apply successor_formation. exact (arrow_application _ _ _ _ _ Hf Hv).
    + apply (arrow_application _ _ _ _ _ Hf), successor_formation. exact Hv.
    + transitivity (Succ (iterate k (@V0 0))).
      * unfold Succ. apply beta_app; [reflexivity |apply iter_function_beta].
      * rewrite <- iterate_commute. symmetry. apply iter_function_beta.
Qed.

(** A flat list of equality continuations followed directly by a stable tail.
    Adding an extra negative-disjunction wrapper around that tail would
    unnecessarily increase the motive rank from fifteen to seventeen. *)
Fixpoint Branches {n} (xs : list (Term nat n)) (T : Term nat n) :=
  match xs with [] => T | A::rest => Arrow (Neg A) (Branches rest T) end.
Lemma shift_branches {n} (xs : list (Term nat n)) T :
  shift (Branches xs T) = Branches (map shift xs) (shift T).
Proof.
  induction xs as [|A xs IH]; cbn [Branches map]; [reflexivity |].
  rewrite shift_arrow, shift_neg, IH. reflexivity.
Qed.
Lemma branches_formation {n} (Γ : Ctx nat n) xs T :
  Forall (fun A => Typed Γ A (𝓤 7)) xs -> Typed Γ T (𝓤 15) ->
  Typed Γ (Branches xs T) (𝓤 15).
Proof.
  intros H HT. induction H; cbn [Branches]; [exact HT |].
  exact (arrow_formation _ _ _ _ _ (neg_formation _ _ _ H) IHForall).
Qed.
Lemma branches_formed {n} (Γ : Ctx nat n) xs T :
  Forall (formed Γ) xs -> formed Γ T -> formed Γ (Branches xs T).
Proof.
  intros H HT. induction H; cbn [Branches]; auto.
  apply arrow_formed; [apply neg_formed |]; assumption.
Qed.
Lemma branches_stable {n} (Γ : Ctx nat n) xs T :
  Forall (formed Γ) xs -> formed Γ T -> stable Γ T -> stable Γ (Branches xs T).
Proof.
  intros H HT HS. induction H; cbn [Branches]; [exact HS |].
  apply arrow_stable; auto using neg_formed, branches_formed.
Qed.
Lemma branches_refute {n} (Γ : Ctx nat n) xs T :
  inhabited Γ (Branches xs T) ->
  (forall A, In A xs -> inhabited Γ (Neg A)) -> inhabited Γ T.
Proof.
  induction xs as [|A xs IH]; intros Hh Hks; [exact Hh |].
  apply IH.
  - eapply arrow_elim; [exact Hh |apply Hks; left; reflexivity].
  - intros B HB. apply Hks. right. exact HB.
Qed.
Lemma branches_eliminate {n} (Γ : Ctx nat n) xs T C :
  Forall (formed Γ) xs -> formed Γ C -> stable Γ C ->
  inhabited Γ (Branches xs T) -> inhabited Γ (Arrow T C) ->
  (forall A, In A xs -> inhabited Γ (Arrow A C)) -> inhabited Γ C.
Proof.
  intros Hxs HC HS Hh Htail Hbranches. unfold stable in HS.
  eapply arrow_elim; [exact HS |].
  apply arrow_intro; [apply neg_formed; exact HC |].
  rewrite <- lift_closed_shift.
  pose proof (newest Γ (Neg C)) as Hnc. normalize_shifts Hnc.
  eapply arrow_elim; [exact Hnc |].
  pose proof (inhabited_shift _ _ (Neg C) Htail) as Htail'.
  rewrite shift_arrow in Htail'. eapply arrow_elim; [exact Htail' |].
  apply (branches_refute _ (map shift xs)).
  - pose proof (inhabited_shift _ _ (Neg C) Hh) as Hh'.
    rewrite shift_branches in Hh'. exact Hh'.
  - intros A HA. apply in_map_iff in HA. destruct HA as [B [<- HB]].
    unfold Neg. apply arrow_intro.
    + apply formed_shift. rewrite Forall_forall in Hxs. apply Hxs. exact HB.
    + rewrite <- lift_closed_shift.
      weaken_copy Hnc (shift B) Hnc2. eapply arrow_elim; [exact Hnc2 |].
      pose proof (Hbranches B HB) as Hb.
      weaken_copy Hb (Neg C) Hb1. weaken_copy Hb1 (shift B) Hb2.
      eapply arrow_elim; [exact Hb2 |apply newest].
Qed.
Lemma stable_from_bottom {n} (Γ : Ctx nat n) C :
  formed Γ C -> stable Γ C -> inhabited Γ (lift_closed Bottom) -> inhabited Γ C.
Proof.
  intros HC HS HB. eapply arrow_elim; [exact HS |].
  apply arrow_intro; [apply neg_formed; exact HC |].
  apply inhabited_shift. exact HB.
Qed.
Lemma branches_tail : forall n (Γ : Ctx nat n) xs T,
  Forall (formed Γ) xs -> inhabited Γ T -> inhabited Γ (Branches xs T).
Proof.
  assert (Haux : forall k n (Γ : Ctx nat n) xs T, length xs = k ->
    Forall (formed Γ) xs -> inhabited Γ T -> inhabited Γ (Branches xs T)).
  { induction k as [|k IH]; intros n Γ xs T Hlen Hxs HT;
      destruct xs as [|A xs]; cbn in Hlen; try discriminate.
    - exact HT.
    - injection Hlen as Hlen. subst k. inversion Hxs; subst.
      apply arrow_intro; [apply neg_formed; assumption |].
      rewrite shift_branches. apply (IH _ _ _ _ (length_map shift xs)).
      + apply formed_list_shift. assumption.
      + apply inhabited_shift. exact HT. }
  intros n Γ xs T. apply (Haux (length xs) n Γ xs T eq_refl).
Qed.
Lemma branches_injection : forall n (Γ : Ctx nat n) xs T A,
  Forall (formed Γ) xs -> formed Γ T -> stable Γ T ->
  In A xs -> inhabited Γ A -> inhabited Γ (Branches xs T).
Proof.
  assert (Haux : forall k n (Γ : Ctx nat n) xs T A, length xs = k ->
    Forall (formed Γ) xs -> formed Γ T -> stable Γ T ->
    In A xs -> inhabited Γ A -> inhabited Γ (Branches xs T)).
  { induction k as [|k IH]; intros n Γ xs T A Hlen Hxs HT HS Hin HA;
      destruct xs as [|B xs]; cbn in Hlen; try discriminate.
    - contradiction.
    - injection Hlen as Hlen. subst k.
      inversion Hxs as [|? ? HB Htail]; subst.
      apply arrow_intro; [apply neg_formed; exact HB |].
      rewrite shift_branches. destruct Hin as [Heq|Hin].
      + subst A. apply stable_from_bottom.
        * apply branches_formed; [apply formed_list_shift; exact Htail |apply formed_shift; exact HT].
        * apply branches_stable.
          -- apply formed_list_shift. exact Htail.
          -- apply formed_shift. exact HT.
          -- unfold stable in *. pose proof (inhabited_shift _ _ (Neg B) HS) as HS'.
             rewrite shift_arrow, !shift_neg in HS'. exact HS'.
        * apply (arrow_elim _ (shift B)).
          -- change (inhabited (Γ & Neg B) (Neg (shift B))). rewrite <- shift_neg. apply newest.
          -- apply inhabited_shift. exact HA.
      + apply (IH _ _ _ _ (shift A) (length_map shift xs)).
        * apply formed_list_shift. exact Htail.
        * apply formed_shift. exact HT.
        * unfold stable in *. pose proof (inhabited_shift _ _ (Neg B) HS) as HS'.
          rewrite shift_arrow, !shift_neg in HS'. exact HS'.
        * apply in_map. exact Hin.
        * apply inhabited_shift. exact HA. }
  intros n Γ xs T A. apply (Haux (length xs) n Γ xs T A eq_refl).
Qed.

Lemma iter_function_in_context {n} (Γ : Ctx nat n) k :
  Typed Γ (lift_closed (iter_function k))
    (Arrow (lift_closed Unary.Domain) (lift_closed Unary.Domain)).
Proof. exact (lift_closed_typed Γ _ _ (iter_function_typed k)). Qed.
Lemma iter_comm_in_context {n} (Γ : Ctx nat n) k :
  inhabited Γ (Comm (lift_closed (iter_function k))).
Proof.
  unfold Comm. rewrite <- lift_closed_shift. apply product_intro.
  - exists 3. exact (lift_closed_typed Γ _ _ Unary.domain_formation).
  - assert (Hv : Typed (Γ & lift_closed Unary.Domain) V0 (lift_closed Unary.Domain)).
    { rewrite lift_closed_shift. exact (tV (Γ & lift_closed Unary.Domain) fzero). }
    pose proof (iter_function_in_context (Γ & lift_closed Unary.Domain) k) as Hf.
    apply equation_of_beta.
    + apply successor_formation. exact (arrow_application _ _ _ _ _ Hf Hv).
    + apply (arrow_application _ _ _ _ _ Hf), successor_formation. exact Hv.
    + transitivity (Succ (iterate k (@V0 n))).
      * unfold Succ. apply beta_app; [reflexivity |apply iter_function_beta].
      * rewrite <- iterate_commute. symmetry. apply iter_function_beta.
Qed.
Lemma iterate_zero {n} k :
  iterate k (@lift_closed n Unary.zero) = lift_closed (Unary.numeral k).
Proof. induction k; cbn [iterate Unary.numeral]; [reflexivity |]. rewrite IHk. reflexivity. Qed.
Lemma iter_zero_beta {n} k :
  app (lift_closed (iter_function k)) (@lift_closed n Unary.zero) =ᵝ
    lift_closed (Unary.numeral k).
Proof. rewrite <- iterate_zero. apply iter_function_beta. Qed.
Definition atoms {n} cutoff (d : Term nat n) :=
  map (fun i => E d (lift_closed (Unary.numeral i))) (seq 0 (S cutoff)).
Definition Tail {n} cutoff (d : Term nat n) :=
  Large (lift_closed (iter_function (S cutoff))) d.
Definition Cut {n} cutoff (d : Term nat n) := Branches (atoms cutoff d) (Tail cutoff d).
Lemma atoms_typed {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) -> Forall (fun A => Typed Γ A (𝓤 7)) (atoms cutoff d).
Proof.
  intro Hd. unfold atoms. apply Forall_map, Forall_forall. intros i Hi.
  apply equality_formation; [exact Hd |apply lift_closed_typed, Unary.numeral_typed].
Qed.
Lemma atoms_formed {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) -> Forall (formed Γ) (atoms cutoff d).
Proof.
  intro Hd. eapply Forall_impl; [|exact (atoms_typed Γ cutoff d Hd)].
  intros A HA. exists 7. exact HA.
Qed.
Lemma tail_formation {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ (Tail cutoff d) (𝓤 15).
Proof. intro Hd. apply large_formation_in_context; [apply iter_function_in_context |exact Hd]. Qed.
Lemma tail_stable {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) -> stable Γ (Tail cutoff d).
Proof. intro Hd. apply large_stable; [apply iter_function_in_context |exact Hd]. Qed.
Lemma cut_formation {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ (Cut cutoff d) (𝓤 15).
Proof. intro Hd. apply branches_formation; auto using atoms_typed, tail_formation. Qed.
Lemma cut_stable {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) -> stable Γ (Cut cutoff d).
Proof.
  intro Hd. apply branches_stable; [apply atoms_formed |exists 15; apply tail_formation |apply tail_stable]; exact Hd.
Qed.
Lemma shift_atoms {n} cutoff (d : Term nat n) :
  map shift (atoms cutoff d) = atoms cutoff (shift d).
Proof.
  unfold atoms. rewrite map_map. apply map_ext. intro i.
  rewrite shift_E, <- lift_closed_shift. reflexivity.
Qed.
Lemma shift_tail {n} cutoff (d : Term nat n) : shift (Tail cutoff d) = Tail cutoff (shift d).
Proof. unfold Tail. rewrite shift_Large, <- lift_closed_shift. reflexivity. Qed.
Lemma shift_cut {n} cutoff (d : Term nat n) : shift (Cut cutoff d) = Cut cutoff (shift d).
Proof. unfold Cut. rewrite shift_branches, shift_atoms, shift_tail. reflexivity. Qed.
Lemma cut_inject_equality {n} (Γ : Ctx nat n) cutoff d i :
  Typed Γ d (lift_closed Unary.Domain) -> i <= cutoff ->
  inhabited Γ (E d (lift_closed (Unary.numeral i))) -> inhabited Γ (Cut cutoff d).
Proof.
  intros Hd Hi He. apply (branches_injection n Γ _ _ (E d (lift_closed (Unary.numeral i)))).
  - apply atoms_formed. exact Hd.
  - exists 15. apply tail_formation. exact Hd.
  - apply tail_stable. exact Hd.
  - unfold atoms. apply in_map_iff. exists i. split; [reflexivity |apply in_seq; lia].
  - exact He.
Qed.
Lemma cut_inject_large {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (Tail cutoff d) -> inhabited Γ (Cut cutoff d).
Proof. intros Hd HT. apply branches_tail; [apply atoms_formed; exact Hd |exact HT]. Qed.
Lemma cut_zero_in_context {n} (Γ : Ctx nat n) cutoff :
  inhabited Γ (Cut cutoff (lift_closed Unary.zero)).
Proof.
  apply (cut_inject_equality Γ cutoff _ 0).
  - apply lift_closed_typed, Unary.zero_typed.
  - lia.
  - apply equality_reflexivity, lift_closed_typed, Unary.zero_typed.
Qed.
Lemma cut_successor_equality {n} (Γ : Ctx nat n) cutoff d i :
  Typed Γ d (lift_closed Unary.Domain) -> i <= cutoff ->
  inhabited Γ (E d (lift_closed (Unary.numeral i))) -> inhabited Γ (Cut cutoff (Succ d)).
Proof.
  intros Hd Hi He.
  pose proof (successor_formation Γ d Hd) as Hsd.
  pose proof (equality_successor Γ _ _ Hd
    (lift_closed_typed Γ _ _ (Unary.numeral_typed i)) He) as Hse.
  change (inhabited Γ (E (Succ d) (lift_closed (Unary.numeral (S i))))) in Hse.
  destruct (Nat.eq_dec i cutoff) as [->|Hne].
  - apply cut_inject_large; [exact Hsd |].
    unfold Tail. apply (large_intro_in_context Γ _ _ (lift_closed Unary.zero)).
    + apply iter_function_in_context.
    + exact Hsd.
    + apply lift_closed_typed, Unary.zero_typed.
    + exists (lift_closed (RC.good_zero 11)).
      exact (lift_closed_typed Γ _ _ RC.good_zero_11_typed).
    + eapply inhabited_conversion; [exact Hse | |].
      * apply equality_formation; [exact Hsd |].
        apply (arrow_application _ _ _ _ _ (iter_function_in_context Γ (S cutoff))).
        apply lift_closed_typed, Unary.zero_typed.
      * unfold E. apply beta_app; [reflexivity |symmetry; apply iter_zero_beta].
  - apply (cut_inject_equality Γ cutoff _ (S i)); [exact Hsd |lia |exact Hse].
Qed.
Lemma cut_successor_large {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (Tail cutoff d) ->
  inhabited Γ (Cut cutoff (Succ d)).
Proof.
  intros Hd HT. apply cut_inject_large; [apply successor_formation; exact Hd |].
  apply large_successor_in_context; [apply iter_function_in_context |apply iter_comm_in_context |exact Hd |exact HT].
Qed.
Theorem cut_successor_in_context {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (Cut cutoff d) ->
  inhabited Γ (Cut cutoff (Succ d)).
Proof.
  intros Hd HC. pose proof (atoms_formed Γ cutoff d Hd) as Hformed.
  eapply branches_eliminate.
  - exact Hformed.
  - exists 15. apply cut_formation, successor_formation. exact Hd.
  - apply cut_stable, successor_formation. exact Hd.
  - exact HC.
  - apply arrow_intro; [exists 15; apply tail_formation; exact Hd |].
    rewrite shift_cut, shift_Succ. apply cut_successor_large.
    + rewrite lift_closed_shift. apply weakening. exact Hd.
    + pose proof (newest Γ (Tail cutoff d)) as H. rewrite shift_tail in H. exact H.
  - intros A Hin. apply arrow_intro.
    + rewrite Forall_forall in Hformed. apply Hformed. exact Hin.
    + rewrite shift_cut, shift_Succ.
      pose proof (weakening RankSorts _ _ A Hd) as Hd'. rewrite <- lift_closed_shift in Hd'.
      pose proof (newest Γ A) as HA.
      apply in_map_iff in Hin. destruct Hin as [i [<- Hi]].
      rewrite shift_E, <- lift_closed_shift in HA.
      apply (cut_successor_equality _ cutoff _ i); [exact Hd' |apply in_seq in Hi; lia |exact HA].
Qed.

Lemma replace_branches {m n} (s : Fin m -> Term nat n) xs T :
  replace s (Branches xs T) = Branches (map (replace s) xs) (replace s T).
Proof.
  induction xs as [|A xs IH]; cbn [Branches map]; [reflexivity |].
  rewrite replace_arrow, IH. unfold Neg.
  rewrite replace_arrow, replace_lift_closed. reflexivity.
Qed.
Lemma replace_cut {m n} (s : Fin m -> Term nat n) cutoff d :
  replace s (Cut cutoff d) = Cut cutoff (replace s d).
Proof.
  unfold Cut, atoms, Tail, Large.
  rewrite replace_branches, map_map, !replace_application, !replace_lift_closed.
  f_equal. apply map_ext. intro i. rewrite replace_E, replace_lift_closed. reflexivity.
Qed.
Definition cut_family cutoff : closed_term := lam Unary.Domain (Cut cutoff V0).
Lemma cut_family_typed cutoff :
  Typed ε (cut_family cutoff) (Arrow Unary.Domain (𝓤 15)).
Proof.
  apply (tLam Unary.domain_formation), cut_formation.
  exact (tV (ε & Unary.Domain) fzero).
Qed.
Lemma cut_family_beta {n} cutoff (d : Term nat n) :
  app (lift_closed (cut_family cutoff)) d =ᵝ Cut cutoff d.
Proof.
  unfold cut_family, lift_closed. cbn [rename].
  transitivity (subst (rename (weak empty_renaming) (Cut cutoff V0)) d).
  - apply beta_contract.
  - unfold subst. rewrite replace_rename, replace_cut.
    change (Cut cutoff d =ᵝ Cut cutoff d). reflexivity.
Qed.
Definition cut_closure_type cutoff : closed_term := Π Unary.Domain
  (Arrow (Cut cutoff V0) (Cut cutoff (Succ V0))).
Lemma cut_closure_realized cutoff : Realizes (cut_closure_type cutoff).
Proof.
  assert (Hd : Typed (ε & Unary.Domain) V0 (lift_closed Unary.Domain))
    by exact (tV (ε & Unary.Domain) fzero).
  unfold cut_closure_type. apply product_intro; [exists 3; exact Unary.domain_formation |].
  apply arrow_intro; [exists 15; apply cut_formation; exact Hd |].
  rewrite shift_cut, shift_Succ. apply cut_successor_in_context.
  - rewrite lift_closed_shift. apply weakening. exact Hd.
  - pose proof (newest (ε & Unary.Domain) (Cut cutoff V0)) as H.
    rewrite shift_cut in H. exact H.
Qed.
Definition nEliminateFields :=
  [(600,nArrow nD (NSort 15)); (601,NApp (NVar 600) nZ);
   (602,NPi 603 nD (nArrow (NApp (NVar 600) (NVar 603))
     (NApp (NVar 600) (NApp nS (NVar 603)))));
   (604,nD); (605,NApp (NClosed (RC.Good 15)) (NVar 604))].
Definition eliminate15 := close
  (nlams nEliminateFields (napps (NVar 605) [NVar 600;NVar 601;NVar 602])) eq_refl.
Definition eliminate15_type := close
  (npis nEliminateFields (NApp (NVar 600) (NVar 604))) eq_refl.
Lemma eliminate15_typed : Typed ε eliminate15 eliminate15_type.
Proof. RkCheck.certify_with 4096. Qed.

Definition family_step {n} (C : Term nat n) := Π (lift_closed Unary.Domain)
  (Arrow (app (shift C) V0) (app (shift C) (Succ V0))).
Definition family_result {n} (C : Term nat n) := Π (lift_closed Unary.Domain)
  (Arrow (G 15 V0) (app (shift C) V0)).
Lemma family_step_formation {n} (Γ : Ctx nat n) C :
  Typed Γ C (Arrow (lift_closed Unary.Domain) (𝓤 15)) ->
  Typed Γ (family_step C) (𝓤 16).
Proof.
  intro HC. pose proof (weakening RankSorts _ _ (lift_closed Unary.Domain) HC) as HC'.
  rewrite shift_arrow, <- lift_closed_shift in HC'.
  assert (Hd : Typed (Γ & lift_closed Unary.Domain) V0 (lift_closed Unary.Domain)).
  { rewrite lift_closed_shift. exact (tV (Γ & lift_closed Unary.Domain) fzero). }
  apply (tPi (b:=16) (lift_closed_typed Γ _ _ Unary.domain_formation)).
  apply (arrow_formation _ _ _ 15 15).
  - exact (arrow_application _ _ _ _ _ HC' Hd).
  - apply (arrow_application _ _ _ _ _ HC'), successor_formation. exact Hd.
Qed.
Lemma eliminate15_application C c0 cs :
  Typed ε C (Arrow Unary.Domain (𝓤 15)) -> Typed ε c0 (app C Unary.zero) ->
  Typed ε cs (family_step C) ->
  Typed ε (table_apply eliminate15 [C;c0;cs]) (family_result C).
Proof.
  intros HC H0 HS. pose proof eliminate15_typed as H.
  change (Typed ε eliminate15
    (Π (Arrow Unary.Domain (𝓤 15))
      (Π (app V0 (lift_closed Unary.zero))
        (Π (family_step (shift V0)) (family_result (shift (shift V0))))))) in H.
  unfold family_step, family_result in H.
  cut_feed H HC. cut_feed H H0. cut_feed H HS. exact H.
Qed.
Lemma family_step_beta cutoff : family_step (cut_family cutoff) =ᵝ cut_closure_type cutoff.
Proof.
  unfold family_step, cut_closure_type. rewrite Unary.shift_closed.
  apply beta_pi; [reflexivity |]. apply arrow_beta; apply cut_family_beta.
Qed.
Definition finite_cut_type cutoff : closed_term := Π Unary.Domain
  (Arrow (G 15 V0) (Cut cutoff V0)).
Lemma finite_cut_formation cutoff : Typed ε (finite_cut_type cutoff) (𝓤 18).
Proof.
  apply (tPi (b:=18) Unary.domain_formation), (arrow_formation _ _ _ 17 15).
  - pose proof (lift_closed_typed (ε & Unary.Domain) _ _ RC.good_15_formation) as HG.
    change (Typed (ε & Unary.Domain) (lift_closed (RC.Good 15))
      (Arrow (lift_closed Unary.Domain) (𝓤 17))) in HG.
    exact (arrow_application _ _ _ _ _ HG (tV (ε & Unary.Domain) fzero)).
  - apply cut_formation. exact (tV (ε & Unary.Domain) fzero).
Qed.

(** All external cutoffs, with one fixed guard and one equality. The proof
    instantiates the supplied Good15 certificate of an arbitrary raw d;
    it does not enumerate standard inputs or assume the desired cut. *)
Theorem finite_cut_realized cutoff : Realizes (finite_cut_type cutoff).
Proof.
  destruct (cut_zero_in_context ε cutoff) as [c0 H0]. rewrite lift_closed_zero in H0.
  destruct (cut_closure_realized cutoff) as [cs HS].
  pose proof (cut_family_typed cutoff) as HC.
  assert (H0' : Typed ε c0 (app (cut_family cutoff) Unary.zero)).
  { eapply tConv; [exact H0 |exact (arrow_application _ _ _ _ _ HC Unary.zero_typed) |].
    symmetry. rewrite <- (lift_closed_zero (cut_family cutoff)). apply cut_family_beta. }
  assert (HS' : Typed ε cs (family_step (cut_family cutoff))).
  { eapply tConv; [exact HS |apply family_step_formation; exact HC |].
    symmetry. apply family_step_beta. }
  exists (table_apply eliminate15 [cut_family cutoff;c0;cs]).
  eapply tConv.
  - exact (eliminate15_application _ _ _ HC H0' HS').
  - apply finite_cut_formation.
  - unfold family_result, finite_cut_type. rewrite Unary.shift_closed.
    apply beta_pi; [reflexivity |]. apply arrow_beta; [reflexivity |apply cut_family_beta].
Qed.
Lemma finite_cut_in_context {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (G 15 d) ->
  inhabited Γ (Cut cutoff d).
Proof.
  intros Hd [g Hg]. destruct (finite_cut_realized cutoff) as [p Hp].
  pose proof (lift_closed_typed Γ _ _ Hp) as H.
  unfold lift_closed at 2 in H. unfold finite_cut_type in H.
  rewrite rename_as_replace, replace_product, replace_arrow, replace_cut in H.
  change (Typed Γ (lift_closed p)
    (Π (lift_closed Unary.Domain) (Arrow (G 15 V0) (Cut cutoff V0)))) in H.
  pose proof (tApp H Hd) as H1. unfold subst in H1.
  rewrite replace_arrow, replace_cut in H1. cut_substitution H1.
  eexists. exact (arrow_application _ _ _ _ _ H1 Hg).
Qed.

Print Assumptions large_intro_typed.
Print Assumptions large_successor_typed.
Print Assumptions cut_formation.
Print Assumptions cut_successor_in_context.
Print Assumptions finite_cut_realized.
Print Assumptions finite_cut_in_context.
End FiniteCuts.
