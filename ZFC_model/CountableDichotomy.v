(** A countable injection from an explicit choice operation on subsets of X.
    The recursion is native Rocq: bounding its graph is proved here, while
    first-order bounded recursion remains a foundation-audit obligation. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From ZFC Require Import Sets Axioms Cartesian.
From PTSrkModel Require Import SetFunctions SetApplication SetBijections
  ProductEmbedding CodeUniverses CountableCodes FiniteClassification.
Import CodeUniverses.CodeUniverses.

Definition subset_choice X c := forall Y, IN Y (Power X) ->
  (exists y, IN y Y) -> IN (apply_set c Y) Y.
Definition remaining X S := Comp X (fun x => ~ IN x S).
Lemma remaining_predicate S x y : (~ IN x S) -> EQ x y -> ~ IN y S.
Proof. intros H E Hy; apply H; exact (IN_sound_left y x S (EQ_sym _ _ E) Hy). Qed.
Lemma remaining_spec X S x : IN x (remaining X S) <-> IN x X /\ ~ IN x S.
Proof.
  split.
  - intro H; split; [exact (Comp_INC _ _ _ H) | exact (IN_Comp_P _ _ _ (remaining_predicate S) H)].
  - intros [Hx Hn]. apply IN_P_Comp; [apply remaining_predicate | exact Hx | exact Hn].
Qed.
Fixpoint chosen_stage X c n := match n with
  | 0 => Vide
  | S k => Union (Paire (chosen_stage X c k)
      (Sing (apply_set c (remaining X (chosen_stage X c k)))))
  end.
Definition chosen X c n := apply_set c (remaining X (chosen_stage X c n)).
Lemma chosen_stage_spec X c n x :
  IN x (chosen_stage X c n) <-> exists i, i < n /\ EQ x (chosen X c i).
Proof.
  induction n as [|n IH].
  - split; [intro H; destruct (Vide_est_vide x H) | intros [i [Hi _]]; lia].
  - change (IN x (Union (Paire (chosen_stage X c n) (Sing (chosen X c n)))) <->
      exists i, i < S n /\ EQ x (chosen X c i)).
    split.
    + intro H. destruct (Union_IN _ _ H) as [Y [HY Hx]].
      destruct (Paire_IN _ _ _ HY) as [E | E].
      * destruct (proj1 IH (IN_sound_right x _ _ E Hx)) as [i [Hi Ei]]. exists i; split; [lia | exact Ei].
      * exists n; split; [lia | apply IN_Sing_EQ; exact (IN_sound_right x _ _ E Hx)].
    + intros [i [Hi Ei]]. destruct (Nat.eq_dec i n) as [E | E].
      * subst i. eapply IN_Union; [apply IN_Paire_right |].
        exact (IN_sound_left _ x _ (EQ_sym _ _ Ei) (IN_Sing _)).
      * eapply IN_Union; [apply IN_Paire_left |]. apply IH; exists i; split; [lia | exact Ei].
Qed.

Section Infinite.
Variable classical_logic : forall P : Prop, P \/ ~ P.
Variables X c : Ens.
Hypothesis HC : subset_choice X c.
Hypothesis Hinf : forall n, ~ equinumerous X (finite_carrier n).

Lemma chosen_prefix n :
  (forall i, i < n -> IN (chosen X c i) X) /\
  (forall i j, i < n -> j < n -> EQ (chosen X c i) (chosen X c j) -> i = j).
Proof.
  induction n as [|n [HT HI]]; [split; intros; lia |].
  assert (HN : exists y, IN y (remaining X (chosen_stage X c n))).
  { destruct (classical_logic (exists y, IN y (remaining X (chosen_stage X c n)))) as [H | H]; [exact H |].
    exfalso; apply (Hinf n). apply equinumerous_sym.
    exists (finite_enumeration_graph n (chosen X c)).
    apply finite_enumeration_bijection; [exact HT | exact HI |].
    intros x Hx. apply chosen_stage_spec.
    destruct (classical_logic (IN x (chosen_stage X c n))) as [HS | HS]; [exact HS |].
    exfalso; apply H; exists x; apply remaining_spec; auto. }
  pose proof (HC _ (INC_IN_Power X _ (Comp_INC _ _)) HN) as Hnext.
  apply remaining_spec in Hnext as [Htyped Hfresh].
  change (IN (chosen X c n) X) in Htyped.
  change (~ IN (chosen X c n) (chosen_stage X c n)) in Hfresh.
  assert (Hneq : forall i, i < n -> ~ EQ (chosen X c n) (chosen X c i)).
  { intros i Hi E. apply Hfresh, chosen_stage_spec. exists i; auto. }
  split.
  - intros i Hi. destruct (Nat.eq_dec i n); [subst; exact Htyped | apply HT; lia].
  - intros i j Hi Hj E. destruct (Nat.eq_dec i n), (Nat.eq_dec j n); subst; try reflexivity.
    + exfalso; exact (Hneq j ltac:(lia) E).
    + exfalso; exact (Hneq i ltac:(lia) (EQ_sym _ _ E)).
    + apply HI; [lia | lia | exact E].
Qed.
Lemma chosen_typed n : IN (chosen X c n) X.
Proof. exact (proj1 (chosen_prefix (S n)) n (Nat.lt_succ_diag_r n)). Qed.
Lemma chosen_injective i j : EQ (chosen X c i) (chosen X c j) -> i = j.
Proof. apply (proj2 (chosen_prefix (S (i+j)))); lia. Qed.

Definition choice_sequence_graph := sup nat (fun i => Couple (numeral i) (chosen X c i)).
Lemma choice_sequence_application x y : application choice_sequence_graph x y <->
  exists i, EQ x (numeral i) /\ EQ y (chosen X c i).
Proof.
  split.
  - intros [i E]. exists i; split; [exact (Couple_inj_left _ _ _ _ E) | exact (Couple_inj_right _ _ _ _ E)].
  - intros [i [Ex Ey]]. exists i.
    eapply EQ_tran; [apply Couple_sound_left; exact Ex | apply Couple_sound_right; exact Ey].
Qed.
Theorem choice_sequence_injection : injection omega_codes X choice_sequence_graph.
Proof.
  split.
  - apply bounded_function_member.
    + intros e [i E]. apply (IN_sound_left _ e _ (EQ_sym _ _ E)).
      apply Couple_IN_Prod; [apply numeral_in_omega | apply chosen_typed].
    + split.
      * intros x [i E]. exists (chosen X c i); apply choice_sequence_application.
        exists i; split; [exact E | apply EQ_refl].
      * split.
        -- intros x y H. apply choice_sequence_application in H as [i [Ex Ey]].
           split; [exists i; exact Ex |]. exact (IN_sound_left _ y X (EQ_sym _ _ Ey) (chosen_typed i)).
        -- intros x y z H H'. apply choice_sequence_application in H as [i [Ex Ey]].
           apply choice_sequence_application in H' as [j [Ex' Ez]].
           assert (Eij : i = j) by (apply numeral_injective; eapply EQ_tran; [apply EQ_sym; exact Ex | exact Ex']).
           subst j. eapply EQ_tran; [exact Ey | apply EQ_sym; exact Ez].
  - intros x x' y H H'. apply choice_sequence_application in H as [i [Ex Ey]].
    apply choice_sequence_application in H' as [j [Ex' Ey']].
    assert (Eij : i = j).
    { apply chosen_injective; eapply EQ_tran; [apply EQ_sym; exact Ey | exact Ey']. }
    subst j. eapply EQ_tran; [exact Ex | apply EQ_sym; exact Ex'].
Qed.
End Infinite.

Theorem finite_countable_dichotomy (classical_logic : forall P : Prop, P \/ ~ P) X c :
  subset_choice X c ->
  (exists n, equinumerous X (finite_carrier n)) \/ embeds omega_codes X.
Proof.
  intro HC. destruct (classical_logic (exists n, equinumerous X (finite_carrier n))) as [H | H]; [left; exact H |].
  right; exists (choice_sequence_graph X c). apply choice_sequence_injection; [exact classical_logic | exact HC |].
  intros n Hn; apply H; exists n; exact Hn.
Qed.
Print Assumptions chosen_prefix.
Print Assumptions choice_sequence_injection.
Print Assumptions finite_countable_dichotomy.
Check finite_countable_dichotomy.

(** Ordinary family choice, stated as an explicit principle rather than a
    global Rocq axiom. The family here is a subset of Power X. *)
Definition family_choice := forall A : Ens,
  (forall Y, IN Y A -> exists y, IN y Y) ->
  exists c, IN c (dependent_product A (fun Y => Y)).
Definition nonempty_subsets X := Comp (Power X) (fun Y => exists y, IN y Y).
Lemma nonempty_predicate Y Z : (exists y, IN y Y) -> EQ Y Z -> exists y, IN y Z.
Proof. intros [y Hy] E; exists y; exact (IN_sound_right y Y Z E Hy). Qed.
Theorem subset_choice_from_family_choice : family_choice -> forall X, exists c, subset_choice X c.
Proof.
  intros AC X. destruct (AC (nonempty_subsets X)) as [c Hc].
  - intros Y HY. exact (IN_Comp_P _ _ _ nonempty_predicate HY).
  - exists c; intros Y HY Hne. apply (apply_set_typed (nonempty_subsets X) (fun Y => Y) c Y Hc).
    apply IN_P_Comp; [exact nonempty_predicate | exact HY | exact Hne].
Qed.
Theorem finite_countable_from_choice (classical_logic : forall P : Prop, P \/ ~ P) :
  family_choice -> forall X,
  (exists n, equinumerous X (finite_carrier n)) \/ embeds omega_codes X.
Proof.
  intros AC X. destruct (subset_choice_from_family_choice AC X) as [c Hc].
  exact (finite_countable_dichotomy classical_logic X c Hc).
Qed.
Print Assumptions subset_choice_from_family_choice.
Print Assumptions finite_countable_from_choice.
