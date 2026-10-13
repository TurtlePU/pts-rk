(** Bounded first-order certificate for bijections, including exclusion of
    non-pair graph elements. No choice or cardinal classification is assumed. *)
From ZFC Require Import Sets Axioms Cartesian.
From PTSrk Require Import Syntax.
From PTSrkModel Require Import SetFunctions SetApplication SetBijections
  BoundedFormulas BoundedProducts SuppliedHierarchy HierarchyBounds CardinalGrowth.
Import Bounded.

Definition graphF {n} (A B f : Fin n) :=
  all f (ex (fsucc A) (ex (fsucc (fsucc B))
    (coupleF (fsucc (fsucc fzero)) (fsucc fzero) fzero))).
Definition injectiveF {n} (A B f : Fin n) :=
  all A (all (fsucc A) (all (fsucc (fsucc B))
    (impl (applicationF (fsucc (fsucc (fsucc f))) (fsucc (fsucc fzero)) fzero)
      (impl (applicationF (fsucc (fsucc (fsucc f))) (fsucc fzero) fzero)
        (equal (fsucc (fsucc fzero)) (fsucc fzero)))))).
Definition surjectiveF {n} (A B f : Fin n) :=
  all B (ex (fsucc A) (applicationF (fsucc (fsucc f)) fzero (fsucc fzero))).
Definition bijectionF {n} (A B f : Fin n) :=
  conj (graphF A B f) (conj (totalF A B f)
    (conj (uniqueF A B f) (conj (injectiveF A B f) (surjectiveF A B f)))).

Lemma graph_formula_correct {n} (r : Fin n -> Ens) A B f :
  holds (graphF A B f) r <-> INC (r f) (Prod (r A) (r B)).
Proof.
  unfold graphF. cbn [holds]. setoid_rewrite couple_correct. cbn [fin_match].
  split.
  - intros H e He. destruct (H e He) as [x [Hx [y [Hy E]]]].
    apply (IN_sound_left (Couple x y) e _ (EQ_sym _ _ E)).
    apply Couple_IN_Prod; assumption.
  - intros H e He. pose proof (H e He) as Hp.
    destruct (IN_Prod_EXType _ _ _ Hp) as [x [y E]].
    pose proof (IN_sound_left e (Couple x y) _ (EQ_sym _ _ E) Hp) as Hxy.
    destruct (Couple_Prod_IN _ _ _ _ Hxy) as [Hx Hy].
    exists x; split; [exact Hx |]. exists y; split; [exact Hy | apply EQ_sym; exact E].
Qed.

Theorem bijection_formula_correct {n} (r : Fin n -> Ens) A B f :
  holds (bijectionF A B f) r <-> bijection (r A) (r B) (r f).
Proof.
  unfold bijectionF. cbn [holds]. rewrite graph_formula_correct.
  unfold totalF, uniqueF, injectiveF, surjectiveF. cbn [holds].
  setoid_rewrite application_correct. cbn [fin_match].
  split.
  - intros [HG [HT [HU [HI HS]]]]. split.
    + apply bounded_function_member; [exact HG |]. split.
      * intros x Hx. destruct (HT x Hx) as [y [_ Hy]]. exists y; exact Hy.
      * split.
        -- intros x y Hxy. exact (graph_arguments_bound _ _ _ _ _ HG Hxy).
        -- intros x y z Hxy Hxz.
           destruct (graph_arguments_bound _ _ _ _ _ HG Hxy) as [Hx Hy].
           destruct (graph_arguments_bound _ _ _ _ _ HG Hxz) as [_ Hz].
           exact (HU x Hx y Hy z Hz Hxy Hxz).
    + split.
      * intros x x' y Hxy Hx'y.
        destruct (graph_arguments_bound _ _ _ _ _ HG Hxy) as [Hx Hy].
        destruct (graph_arguments_bound _ _ _ _ _ HG Hx'y) as [Hx' _].
        exact (HI x Hx x' Hx' y Hy Hxy Hx'y).
      * intros y Hy. destruct (HS y Hy) as [x [_ Hxy]]. exists x; exact Hxy.
  - intros [HF [HI HS]].
    destruct (dependent_product_elimination _ _ _ HF) as [HT [HB HU]].
    split; [apply typed_graph_cartesian_bound; exact HF |]. split.
    + intros x Hx. destruct (HT x Hx) as [y Hxy]. exists y; split; [| exact Hxy].
      exact (proj2 (HB x y Hxy)).
    + split.
      * intros x Hx y Hy z Hz Hxy Hxz; exact (HU x y z Hxy Hxz).
      * split.
        -- intros x Hx x' Hx' y Hy Hxy Hx'y; exact (HI x x' y Hxy Hx'y).
        -- intros y Hy. destruct (HS y Hy) as [x Hxy]. exists x; split; [| exact Hxy].
           exact (proj1 (HB x y Hxy)).
Qed.

Definition eligibleF {n} (A T F e : Fin n) :=
  ex T (ex (fsucc F) (conj
    (coupleF (fsucc (fsucc e)) (fsucc fzero) fzero)
    (bijectionF (fsucc (fsucc A)) (fsucc fzero) fzero))).
Definition eligible A T F e := exists K, IN K T /\ exists f,
  IN f F /\ EQ e (Couple K f) /\ bijection A K f.
Lemma eligible_formula_correct {n} (r : Fin n -> Ens) A T F e :
  holds (eligibleF A T F e) r <-> eligible (r A) (r T) (r F) (r e).
Proof.
  unfold eligibleF, eligible. cbn [holds].
  setoid_rewrite couple_correct. setoid_rewrite bijection_formula_correct. reflexivity.
Qed.
Definition eligible_env (A T F e : Ens) := fin_match A (fin_match T
  (fin_match F (fin_match e (fun i : Fin 0 => match i with end)))).
Definition eligible_certificate : Formula 4 :=
  eligibleF fzero (fsucc fzero) (fsucc (fsucc fzero)) (fsucc (fsucc (fsucc fzero))).
Lemma eligible_certificate_correct A T F e :
  holds eligible_certificate (eligible_env A T F e) <-> eligible A T F e.
Proof. apply eligible_formula_correct. Qed.
Lemma eligible_extensional A T F e e' :
  eligible A T F e -> EQ e e' -> eligible A T F e'.
Proof.
  intros [K [HK [f [Hf [E Hb]]]]] E'.
  exists K; split; [exact HK |]. exists f; split; [exact Hf |]. split; [| exact Hb].
  exact (EQ_tran _ _ _ (EQ_sym _ _ E') E).
Qed.
Lemma eligible_certificate_extensional A T F e e' :
  holds eligible_certificate (eligible_env A T F e) -> EQ e e' ->
  holds eligible_certificate (eligible_env A T F e').
Proof. rewrite !eligible_certificate_correct. apply eligible_extensional. Qed.

Definition eligible_bijections A T F := Comp (Prod T F)
  (fun e => holds eligible_certificate (eligible_env A T F e)).
Theorem eligible_bijections_spec A T F e :
  IN e (eligible_bijections A T F) <-> eligible A T F e.
Proof.
  split.
  - intro H. apply eligible_certificate_correct.
    exact (IN_Comp_P _ _ _ (eligible_certificate_extensional A T F) H).
  - intro H. apply IN_P_Comp.
    + apply eligible_certificate_extensional.
    + destruct H as [K [HK [f [Hf [E Hb]]]]].
      apply (IN_sound_left (Couple K f) e _ (EQ_sym _ _ E)).
      apply Couple_IN_Prod; assumption.
    + apply eligible_certificate_correct; exact H.
Qed.

(** The graph bound does not discard any eligible bijection when all target
    carriers are subsets of W. Nonemptiness for cardinal targets remains open. *)
Theorem eligible_bijections_complete W A T K f :
  transitive_set W -> INC A W -> INC K W -> IN K T -> bijection A K f ->
  IN (Couple K f) (eligible_bijections A T (iterated_power W 4)).
Proof.
  intros HW HA HK HKT Hf. apply eligible_bijections_spec.
  exists K; split; [exact HKT |]. exists f; split.
  - exact (coding_bijection_rank_bound W A K f HW HA HK Hf).
  - split; [apply EQ_refl | exact Hf].
Qed.

Theorem eligible_bijections_rank_bound W A T :
  transitive_set W -> INC A W -> (forall K, IN K T -> INC K W) ->
  IN (eligible_bijections A T (iterated_power W 4)) (iterated_power W 8).
Proof.
  intros HW HA HT. apply INC_IN_Power. intros e He.
  apply eligible_bijections_spec in He as [K [HK [f [Hf [E Hb]]]]].
  apply (IN_sound_left (Couple K f) e _ (EQ_sym _ _ E)).
  apply (coding_witness_rank_bound W A K f); [exact HW | exact HA | apply HT; exact HK | exact Hb].
Qed.

Print Assumptions eligible_bijections_rank_bound.
Print Assumptions eligible_formula_correct.
Print Assumptions eligible_bijections_spec.
Print Assumptions eligible_bijections_complete.
Print Assumptions graph_formula_correct.
Print Assumptions bijection_formula_correct.
Check bijection_formula_correct.
