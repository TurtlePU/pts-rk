(** Bounded graph laws for a set-coded dependent family. Bounds are explicit
    parameters; equivalence is proved, not assumed as a model field. *)
From ZFC Require Import Sets Axioms Cartesian.
From PTSrk Require Import Syntax.
From PTSrkModel Require Import SetFunctions SetApplication BoundedFormulas.
Import Bounded.

Definition totalF {n} (A W g : Fin n) :=
  all A (ex (fsucc W) (applicationF (fsucc (fsucc g)) (fsucc fzero) fzero)).
Definition fiberF {n} (A W P f g : Fin n) :=
  all A (all (fsucc W)
    (impl (applicationF (fsucc (fsucc g)) (fsucc fzero) fzero)
      (ex (fsucc (fsucc P))
        (conj (applicationF (fsucc (fsucc (fsucc f))) (fsucc (fsucc fzero)) fzero)
          (member (fsucc fzero) fzero))))).
Definition uniqueF {n} (A W g : Fin n) :=
  all A (all (fsucc W) (all (fsucc (fsucc W))
    (impl (applicationF (fsucc (fsucc (fsucc g))) (fsucc (fsucc fzero)) (fsucc fzero))
      (impl (applicationF (fsucc (fsucc (fsucc g))) (fsucc (fsucc fzero)) fzero)
        (equal (fsucc fzero) fzero))))).
Definition lawsF {n} (A W P f g : Fin n) :=
  conj (totalF A W g) (conj (fiberF A W P f g) (uniqueF A W g)).
Definition bounded_laws A W P f g :=
  (forall x, IN x A -> exists y, IN y W /\ application g x y) /\
  (forall x, IN x A -> forall y, IN y W -> application g x y ->
    exists b, IN b P /\ application f x b /\ IN y b) /\
  (forall x, IN x A -> forall y, IN y W -> forall z, IN z W ->
    application g x y -> application g x z -> EQ y z).
Theorem laws_formula_correct {n} (r : Fin n -> Ens) A W P f g :
  holds (lawsF A W P f g) r <-> bounded_laws (r A) (r W) (r P) (r f) (r g).
Proof.
  unfold lawsF, totalF, fiberF, uniqueF, bounded_laws. cbn [holds].
  setoid_rewrite application_correct. reflexivity.
Qed.

Lemma graph_arguments_bound A W g x y :
  INC g (Prod A W) -> application g x y -> IN x A /\ IN y W.
Proof. intros Hg Hxy. apply Couple_Prod_IN. exact (Hg _ Hxy). Qed.

Theorem bounded_laws_equivalence A W f g :
  IN f (dependent_product A (fun _ => Power W)) -> INC g (Prod A W) ->
  (bounded_laws A W (Power W) f g <-> function_laws A (apply_set f) g).
Proof.
  intros Hf Hg. split.
  - intros [HT [HB HU]]. split.
    + intros x Hx. destruct (HT x Hx) as [y [_ Hy]]. exists y; exact Hy.
    + split.
      * intros x y Hxy. destruct (graph_arguments_bound A W g x y Hg Hxy) as [Hx Hy].
        split; [exact Hx |]. destruct (HB x Hx y Hy Hxy) as [b [Hb [Hxb Hyb]]].
        assert (E : EQ (apply_set f x) b).
        { apply apply_set_value; [exact Hxb |].
          destruct (dependent_product_elimination _ _ _ Hf) as [_ [_ Huniq]].
          intros z Hz; exact (Huniq x z b Hz Hxb). }
        exact (IN_sound_right y b (apply_set f x) (EQ_sym _ _ E) Hyb).
      * intros x y z Hxy Hxz.
        destruct (graph_arguments_bound A W g x y Hg Hxy) as [Hx Hy].
        destruct (graph_arguments_bound A W g x z Hg Hxz) as [_ Hz].
        exact (HU x Hx y Hy z Hz Hxy Hxz).
  - intros [HT [HB HU]]. split.
    + intros x Hx. destruct (HT x Hx) as [y Hy]. exists y; split; [| exact Hy].
      exact (proj2 (graph_arguments_bound A W g x y Hg Hy)).
    + split.
      * intros x Hx y Hy Hxy. exists (apply_set f x). split.
        -- apply (apply_set_typed A (fun _ => Power W)); assumption.
        -- split.
           ++ apply (apply_set_spec A (fun _ => Power W)); assumption.
           ++ exact (proj2 (HB x y Hxy)).
      * intros x Hx y Hy z Hz Hxy Hxz; exact (HU x y z Hxy Hxz).
Qed.

Lemma bounded_laws_extensional A W P f g h :
  bounded_laws A W P f g -> EQ g h -> bounded_laws A W P f h.
Proof.
  intros [HT [HB HU]] E. split.
  - intros x Hx. destruct (HT x Hx) as [y [Hy Hxy]]. exists y; split; [exact Hy |].
    exact (application_extensional g h x y E Hxy).
  - split.
    + intros x Hx y Hy Hxy. apply (HB x Hx y Hy).
      exact (application_extensional h g x y (EQ_sym _ _ E) Hxy).
    + intros x Hx y Hy z Hz Hxy Hxz. apply (HU x Hx y Hy z Hz).
      * exact (application_extensional h g x y (EQ_sym _ _ E) Hxy).
      * exact (application_extensional h g x z (EQ_sym _ _ E) Hxz).
Qed.

Definition laws_env (A W P f g : Ens) := fin_match A (fin_match W
  (fin_match P (fin_match f (fin_match g (fun i : Fin 0 => match i with end))))).
Definition laws_certificate : Formula 5 := lawsF fzero (fsucc fzero)
  (fsucc (fsucc fzero)) (fsucc (fsucc (fsucc fzero)))
  (fsucc (fsucc (fsucc (fsucc fzero)))).
Lemma laws_certificate_correct A W P f g :
  holds laws_certificate (laws_env A W P f g) <-> bounded_laws A W P f g.
Proof. apply laws_formula_correct. Qed.
Lemma laws_certificate_extensional A W P f g h :
  holds laws_certificate (laws_env A W P f g) -> EQ g h ->
  holds laws_certificate (laws_env A W P f h).
Proof. rewrite !laws_certificate_correct. apply bounded_laws_extensional. Qed.

Definition bounded_product A W f := Comp (Power (Prod A W))
  (fun g => holds laws_certificate (laws_env A W (Power W) f g)).
Theorem bounded_product_spec A W f g :
  IN g (bounded_product A W f) <->
  INC g (Prod A W) /\ bounded_laws A W (Power W) f g.
Proof.
  split.
  - intro H. split.
    + apply IN_Power_INC. exact (Comp_INC _ _ _ H).
    + apply laws_certificate_correct.
      exact (IN_Comp_P _ _ _ (laws_certificate_extensional A W (Power W) f) H).
  - intros [Hg Hl]. apply IN_P_Comp.
    + apply laws_certificate_extensional.
    + apply INC_IN_Power; exact Hg.
    + apply laws_certificate_correct; exact Hl.
Qed.

Theorem bounded_product_equivalence A W f :
  IN f (dependent_product A (fun _ => Power W)) ->
  EQ (bounded_product A W f) (dependent_product A (apply_set f)).
Proof.
  intro Hf. apply INC_EQ.
  - intros g Hg. apply bounded_product_spec in Hg as [Hg Hl].
    apply (proj1 (bounded_laws_equivalence A W f g Hf Hg)) in Hl.
    unfold dependent_product. apply IN_P_Comp.
    + intros u v Hu E; exact (function_laws_extensional A (apply_set f) u v Hu E).
    + apply INC_IN_Power. intros e He.
      destruct (IN_Prod_EXType _ _ _ (Hg e He)) as [x [y E]].
      assert (Hxy : application g x y).
      { exact (IN_sound_left e (Couple x y) g (EQ_sym _ _ E) He). }
      destruct (proj1 (proj2 Hl) x y Hxy) as [Hx Hy].
      apply (IN_sound_left (Couple x y) e _ E). apply Couple_IN_Prod; [exact Hx |].
      apply (IN_Union (family_range A (apply_set f)) (apply_set f x) y); [| exact Hy].
      destruct (IN_EXType A x Hx) as [i Ei]. exists i.
      apply apply_set_extensional; [apply EQ_refl | exact Ei].
    + exact Hl.
  - intros g Hg.
    assert (Hb : INC g (Prod A W)).
    { intros e He.
      destruct (dependent_product_pair A (apply_set f) g e Hg He) as [x [y [E [Hx Hxy]]]].
      apply (IN_sound_left (Couple x y) e _ E). apply Couple_IN_Prod; [exact Hx |].
      apply (IN_Power_INC W (apply_set f x)).
      - apply (apply_set_typed A (fun _ => Power W)); assumption.
      - exact (proj2 (proj1 (proj2 (dependent_product_elimination _ _ _ Hg)) x y Hxy)). }
    apply bounded_product_spec. split; [exact Hb |].
    apply (proj2 (bounded_laws_equivalence A W f g Hf Hb)).
    exact (dependent_product_elimination _ _ _ Hg).
Qed.

Print Assumptions laws_formula_correct.
Print Assumptions bounded_laws_equivalence.
Print Assumptions bounded_product_spec.
Print Assumptions bounded_product_equivalence.
Check bounded_product_equivalence.
