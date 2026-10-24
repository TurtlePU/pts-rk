From Stdlib Require Import Bool.Bool.
From PTSrk Require Import Syntax Context Typing Ranks Reduction DefEq
  AbstractRewriting Preservation.
From PTSrk.SelfConsistency Require Import NativeProofCodes.
Import NativeProofCodes.NativeProofCodes.

Lemma matchesb_correct {n} (p : Certificate n) t A :
  matchesb p t A = true <-> matches p t A.
Proof. unfold matchesb, matches; rewrite andb_true_iff, !term_eqb_correct; reflexivity. Qed.

Theorem step_code_sound {n} (p : StepCode n) :
  step nat n (step_source p) (step_target p).
Proof. induction p; cbn; constructor; assumption. Qed.

Theorem step_code_complete {n} (t u : Term nat n) :
  step nat n t u -> exists p, step_source p = t /\ step_target p = u.
Proof.
  intro H; induction H;
    try (destruct IHstep as [p [<- <-]]).
  - exists (PiLeft p U); auto.
  - exists (PiRight T p); auto.
  - exists (LamLeft p t); auto.
  - exists (LamRight T p); auto.
  - exists (AppLeft p t); auto.
  - exists (AppRight f p); auto.
  - exists (Contract T f t); auto.
Qed.

Theorem equality_code_sound {n} (p : EqualityCode n) :
  equality_check p = true -> equality_source p =ᵝ equality_target p.
Proof.
  induction p; cbn; intro H.
  - reflexivity.
  - apply eq_in, step_code_sound.
  - symmetry; auto.
  - repeat rewrite andb_true_iff in H.
    destruct H as [[Hp Hq] E]; apply term_eqb_correct in E.
    transitivity (equality_target p1); [auto | rewrite E; auto].
Qed.

Theorem equality_code_complete {n} (t u : Term nat n) :
  t =ᵝ u -> exists p, equality_check p = true /\
    equality_source p = t /\ equality_target p = u.
Proof.
  intro H; induction H.
  - exists (Refl x); auto.
  - destruct IHRTC as [q [Hq [EqS EqT]]].
    destruct H; destruct (step_code_complete _ _ H) as [p [Ep Et]].
    + exists (Transitivity (Reduce p) q); cbn.
      rewrite Hq, Et, EqS; cbn; split; [apply term_eqb_correct; reflexivity | auto].
    + exists (Transitivity (Symmetry (Reduce p)) q); cbn.
      rewrite Hq, Ep, EqS; cbn; split; [apply term_eqb_correct; reflexivity | auto].
Qed.

Lemma retarget {n} (G : Ctx nat n) p t A :
  @typ nat RankSorts n G (subject p) (type p) -> matches p t A ->
  @typ nat RankSorts n G t A.
Proof. intros H [<- <-]; exact H. Qed.

Theorem certificate_sound {n} (p : Certificate n) : forall G,
  check G p = true -> @typ nat RankSorts n G (subject p) (type p).
Proof.
  induction p; intros G H; cbn in H |- *.
  - constructor; reflexivity.
  - apply term_eqb_correct in H; rewrite <- H; constructor.
  - repeat rewrite andb_true_iff in H.
    destruct H as [[[Hp Hq] Ep] Eq].
    apply matchesb_correct in Ep, Eq.
    eapply typ_Π; [eapply retarget; eauto | eapply retarget; eauto | reflexivity].
  - repeat rewrite andb_true_iff in H.
    destruct H as [[[Hp Hq] Ep] Eq].
    apply matchesb_correct in Ep, Eq.
    eapply typ_λ; eapply retarget; eauto.
  - repeat rewrite andb_true_iff in H.
    destruct H as [[[Hp Hq] Ep] Eq].
    apply matchesb_correct in Ep, Eq.
    pose proof (retarget _ _ _ _ (IHp1 _ Hp) Ep) as TP.
    pose proof (retarget _ _ _ _ (IHp2 _ Hq) Eq) as TQ.
    eapply typ_app; eassumption.
  - repeat rewrite andb_true_iff in H.
    destruct H as [[[[[[Hp Hq] Ep] Eq] He] Es] Et].
    apply matchesb_correct in Ep, Eq.
    apply term_eqb_correct in Es, Et.
    pose proof (retarget _ _ _ _ (IHp1 _ Hp) Ep) as TP.
    pose proof (retarget _ _ _ _ (IHp2 _ Hq) Eq) as TQ.
    eapply typ_conv; [exact TP | exact TQ |].
    rewrite <- Es, <- Et; apply equality_code_sound; exact He.
Qed.

Theorem certificate_complete {n} (G : Ctx nat n) t A :
  @typ nat RankSorts n G t A ->
  exists p, check G p = true /\ matches p t A.
Proof.
  intro H; induction H.
  - change (ℓ' = 0) in H; subst; exists (SortRule ℓ); repeat split; reflexivity.
  - destruct IHtyp1 as [p [Hp Ep]], IHtyp2 as [q [Hq Eq]].
    change (ℓ = Nat.max (S ℓₜ) ℓᵤ) in H1; subst.
    exists (ProductRule T U ℓₜ ℓᵤ p q); split; [|split; reflexivity].
    cbn [check]; repeat rewrite andb_true_iff; repeat split;
      try assumption; apply matchesb_correct; assumption.
  - exists (VariableRule i (Γ !! i)); split; [apply term_eqb_correct |];
      repeat split; reflexivity.
  - destruct IHtyp1 as [p [Hp Ep]], IHtyp2 as [q [Hq Eq]].
    exists (AbstractionRule U t T ℓ p q); split; [|split; reflexivity].
    cbn [check]; repeat rewrite andb_true_iff; repeat split;
      try assumption; apply matchesb_correct; assumption.
  - destruct IHtyp1 as [p [Hp Ep]], IHtyp2 as [q [Hq Eq]].
    exists (ApplicationRule t u U T p q); split; [|split; reflexivity].
    cbn [check]; repeat rewrite andb_true_iff; repeat split;
      try assumption; apply matchesb_correct; assumption.
  - destruct IHtyp1 as [p [Hp Ep]], IHtyp2 as [q [Hq Eq]].
    destruct (equality_code_complete _ _ H1) as [e [He [Es Et]]].
    exists (ConversionRule t T T' ℓ p q e); split; [|split; reflexivity].
    cbn [check]; repeat rewrite andb_true_iff; repeat split; try assumption;
      first [apply matchesb_correct; assumption | apply term_eqb_correct; assumption].
Qed.

Theorem certificate_adequacy {n} (G : Ctx nat n) t A :
  @typ nat RankSorts n G t A <-> exists p, check G p = true /\ matches p t A.
Proof.
  split; [apply certificate_complete | intros [p [Hp E]]].
  eapply retarget; [apply certificate_sound; exact Hp | exact E].
Qed.

Theorem context_code_sound {n} (c : ContextCode n) :
  context_check c = true -> @wf nat RankSorts n (context c).
Proof.
  induction c; cbn; intro H; [constructor |].
  repeat rewrite andb_true_iff in H; destruct H as [[Hc Hp] E].
  apply term_eqb_correct in E.
  eapply wf_cons; [auto | rewrite <- E; apply certificate_sound; exact Hp].
Qed.

Theorem bottom_acceptance_sound (p : Certificate 0) :
  accepts_bottom p = true -> @typ nat RankSorts 0 ε (subject p) Bottom.
Proof.
  unfold accepts_bottom; rewrite andb_true_iff, term_eqb_correct.
  intros [H <-]; apply certificate_sound; exact H.
Qed.

Theorem context_code_complete {n} (G : Ctx nat n) :
  @wf nat RankSorts n G -> exists c, context c = G /\ context_check c = true.
Proof.
  intro W; induction W as [|n G A r W IHW HT].
  - exists EmptyContext; auto.
  - destruct IHW as [c [Ec Hc]].
    destruct (certificate_complete _ _ _ HT) as [p [Hp [Et EA]]].
    exists (ExtendContext c r p); cbn [context context_check].
    rewrite Ec, Et, Hc, Hp; split; [reflexivity |].
    cbn; apply term_eqb_correct; exact EA.
Qed.

Theorem bottom_acceptance_complete t : @typ nat RankSorts 0 ε t Bottom ->
  exists p, subject p = t /\ accepts_bottom p = true.
Proof.
  intro H; destruct (certificate_complete _ _ _ H) as [p [Hp [Et EA]]].
  exists p; split; [exact Et |].
  unfold accepts_bottom; rewrite Bool.andb_true_iff; split; auto.
  apply term_eqb_correct; exact EA.
Qed.

(** Ordinary positive judgments and malformed local evidence, not only the
    externally empty contradiction case. *)
Example sort_accepted : check ε (SortRule 17) = true.
Proof. reflexivity. Qed.
Example identity_accepted : check ε
  (AbstractionRule (𝓤 0) (var fzero) (𝓤 0) 0
    (SortRule 0) (VariableRule fzero (𝓤 0))) = true.
Proof. reflexivity. Qed.
Example forged_variable_rejected : check (ε & 𝓤 0)
  (VariableRule fzero (𝓤 1)) = false.
Proof. reflexivity. Qed.
Example forged_rank_rejected : check ε
  (ProductRule (𝓤 0) (𝓤 0) 1 0 (SortRule 0) (SortRule 0)) = false.
Proof. reflexivity. Qed.
Example mismatched_equality_rejected : equality_check
  (Transitivity (@Refl 0 (𝓤 0)) (Refl (𝓤 1))) = false.
Proof. reflexivity. Qed.

Example malformed_context_rejected :
  context_check (ExtendContext EmptyContext 1 (SortRule 0)) = false.
Proof. reflexivity. Qed.

Example product_accepted : check ε
  (ProductRule (𝓤 0) (𝓤 0) 0 0 (SortRule 0) (SortRule 0)) = true.
Proof. reflexivity. Qed.

Example application_accepted : check ε
  (ApplicationRule (lam (𝓤 0) (var fzero)) (𝓤 0) (𝓤 0) (𝓤 0)
    (AbstractionRule (𝓤 0) (var fzero) (𝓤 0) 0
      (SortRule 0) (VariableRule fzero (𝓤 0))) (SortRule 0)) = true.
Proof. reflexivity. Qed.

Example conversion_accepted : check ε
  (ConversionRule (𝓤 17) (𝓤 0) (𝓤 0) 0 (SortRule 17) (SortRule 0)
    (Refl (𝓤 0))) = true.
Proof. reflexivity. Qed.
