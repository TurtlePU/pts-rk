(** Bounded formula for the least region in Schroeder--Bernstein. Application
    is expanded by BoundedFormulas; no function symbol or opaque Prop atom. *)
From ZFC Require Import Sets Axioms Cartesian.
From PTSrk Require Import Syntax.
From PTSrkModel Require Import SetFunctions SetApplication SetBijections
  ProductEmbedding CantorBernstein BoundedFormulas.
Import Bounded.

Definition baseF {n} (B g x : Fin n) :=
  all B (impl (applicationF (fsucc g) fzero (fsucc x)) falsum).
Lemma base_formula_correct {n} (r : Fin n -> Ens) B g x :
  holds (baseF B g x) r <-> cb_base (r B) (r g) (r x).
Proof.
  unfold baseF, cb_base. cbn [holds]. setoid_rewrite application_correct. reflexivity.
Qed.
Definition closedF {n} (A B f g X : Fin n) :=
  conj
    (all A (impl (baseF (fsucc B) (fsucc g) fzero) (member fzero (fsucc X))))
    (all A (impl (member fzero (fsucc X))
      (all (fsucc B) (all (fsucc (fsucc A))
        (impl (applicationF (fsucc (fsucc (fsucc f))) (fsucc (fsucc fzero)) (fsucc fzero))
          (impl (applicationF (fsucc (fsucc (fsucc g))) (fsucc fzero) fzero)
            (member fzero (fsucc (fsucc (fsucc X)))))))))).

Theorem closed_formula_correct {n} (r : Fin n -> Ens) A B f g X :
  injection (r A) (r B) (r f) -> injection (r B) (r A) (r g) ->
  (holds (closedF A B f g X) r <-> cb_closed (r A) (r B) (r f) (r g) (r X)).
Proof.
  intros Hf Hg. unfold closedF. cbn [holds].
  setoid_rewrite base_formula_correct. setoid_rewrite application_correct. cbn [fin_match].
  split.
  - intros [HB HC]. split; [exact HB |]. intros x Hx HX.
    apply (HC x Hx HX (apply_set (r f) x)).
    + exact (apply_set_typed (r A) (fun _ => r B) (r f) x (proj1 Hf) Hx).
    + exact (cb_step_typed (r A) (r B) (r f) (r g) Hf Hg x Hx).
    + exact (apply_set_spec (r A) (fun _ => r B) (r f) x (proj1 Hf) Hx).
    + apply (apply_set_spec (r B) (fun _ => r A)); [exact (proj1 Hg) |].
      exact (apply_set_typed (r A) (fun _ => r B) (r f) x (proj1 Hf) Hx).
  - intros [HB HC]. split; [exact HB |]. intros x Hx HX y Hy z Hz Hxy Hyz.
    assert (E : EQ (cb_step (r f) (r g) x) z).
    { eapply EQ_tran; [apply apply_set_extensional; [apply EQ_refl |] |].
      - exact (function_value (r A) (r B) (r f) x y (proj1 Hf) Hxy).
      - exact (function_value (r B) (r A) (r g) y z (proj1 Hg) Hyz). }
    exact (IN_sound_left _ z (r X) E (HC x Hx HX)).
Qed.

Definition regionF {n} (P A B f g x : Fin n) :=
  all P (impl (closedF (fsucc A) (fsucc B) (fsucc f) (fsucc g) fzero)
    (member (fsucc x) fzero)).
Theorem region_formula_correct {n} (r : Fin n -> Ens) P A B f g x :
  EQ (r P) (Power (r A)) -> injection (r A) (r B) (r f) -> injection (r B) (r A) (r g) ->
  (holds (regionF P A B f g x) r <-> cb_predicate (r A) (r B) (r f) (r g) (r x)).
Proof.
  intros EP Hf Hg. unfold regionF, cb_predicate. cbn [holds]. split.
  - intros H X HX HC. apply (H X).
    + exact (IN_sound_right X _ _ (EQ_sym _ _ EP) HX).
    + apply (proj2 (closed_formula_correct (fin_match X r)
        (fsucc A) (fsucc B) (fsucc f) (fsucc g) fzero Hf Hg)); exact HC.
  - intros H X HX HC. apply (H X).
    + exact (IN_sound_right X _ _ EP HX).
    + apply (proj1 (closed_formula_correct (fin_match X r)
        (fsucc A) (fsucc B) (fsucc f) (fsucc g) fzero Hf Hg)); exact HC.
Qed.

Definition comparison_env (P A B f g x : Ens) := fin_match P (fin_match A
  (fin_match B (fin_match f (fin_match g (fin_match x (fun i : Fin 0 => match i with end)))))).
Definition region_certificate : Formula 6 := regionF fzero (fsucc fzero)
  (fsucc (fsucc fzero)) (fsucc (fsucc (fsucc fzero)))
  (fsucc (fsucc (fsucc (fsucc fzero)))) (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))).
Lemma region_certificate_correct A B f g x : injection A B f -> injection B A g ->
  (holds region_certificate (comparison_env (Power A) A B f g x) <-> cb_predicate A B f g x).
Proof. intros Hf Hg. apply region_formula_correct; [apply EQ_refl | exact Hf | exact Hg]. Qed.
Definition region_by_formula A B f g := Comp A
  (fun x => holds region_certificate (comparison_env (Power A) A B f g x)).
Theorem region_bounded_separation A B f g : injection A B f -> injection B A g ->
  EQ (cb_region A B f g) (region_by_formula A B f g).
Proof.
  intros Hf Hg.
  assert (HP : forall x y,
    holds region_certificate (comparison_env (Power A) A B f g x) -> EQ x y ->
    holds region_certificate (comparison_env (Power A) A B f g y)).
  { intros x y H E. apply (proj2 (region_certificate_correct A B f g y Hf Hg)).
    exact (cb_predicate_extensional A B f g x y
      (proj1 (region_certificate_correct A B f g x Hf Hg) H) E). }
  apply INC_EQ.
  - intros x Hx. apply cb_region_spec in Hx as [Hx Hp].
    apply IN_P_Comp; [exact HP | exact Hx |].
    apply (region_certificate_correct A B f g x Hf Hg); exact Hp.
  - intros x Hx. apply cb_region_spec; split; [exact (Comp_INC _ _ _ Hx) |].
    apply (region_certificate_correct A B f g x Hf Hg).
    exact (IN_Comp_P _ _ _ HP Hx).
Qed.

Print Assumptions region_bounded_separation.
Print Assumptions base_formula_correct.
Print Assumptions closed_formula_correct.
Print Assumptions region_formula_correct.

(** C is the already constructed least region. All witnesses in the glued
    graph are bounded by A and B; even ordered pairs are expanded formulas. *)
Definition relationF {n} (C f g x y : Fin n) :=
  disj (conj (member x C) (applicationF f x y))
    (conj (impl (member x C) falsum) (applicationF g y x)).
Lemma relation_formula_correct {n} (r : Fin n -> Ens) C f g x y :
  holds (relationF C f g x y) r <->
  ((IN (r x) (r C) /\ application (r f) (r x) (r y)) \/
   (~ IN (r x) (r C) /\ application (r g) (r y) (r x))).
Proof.
  unfold relationF. cbn [holds]. setoid_rewrite application_correct. reflexivity.
Qed.
Definition edgeF {n} (A B C f g e : Fin n) :=
  ex A (ex (fsucc B)
    (conj (coupleF (fsucc (fsucc e)) (fsucc fzero) fzero)
      (relationF (fsucc (fsucc C)) (fsucc (fsucc f))
        (fsucc (fsucc g)) (fsucc fzero) fzero))).
Theorem edge_formula_correct {n} (r : Fin n -> Ens) A B C f g e :
  EQ (r C) (cb_region (r A) (r B) (r f) (r g)) ->
  (holds (edgeF A B C f g e) r <-> cb_edge (r A) (r B) (r f) (r g) (r e)).
Proof.
  intro EC. unfold edgeF, cb_edge, cb_relation. cbn [holds].
  setoid_rewrite couple_correct. setoid_rewrite relation_formula_correct.
  cbn [fin_match].
  assert (HC : forall x, IN x (r C) <-> IN x (cb_region (r A) (r B) (r f) (r g))).
  { intro x; split; intro H.
    - exact (IN_sound_right x _ _ EC H).
    - exact (IN_sound_right x _ _ (EQ_sym _ _ EC) H). }
  setoid_rewrite HC. reflexivity.
Qed.
Definition edge_certificate : Formula 6 := edgeF (fsucc fzero)
  (fsucc (fsucc fzero)) fzero (fsucc (fsucc (fsucc fzero)))
  (fsucc (fsucc (fsucc (fsucc fzero)))) (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))).
Lemma edge_certificate_correct A B f g e :
  holds edge_certificate (comparison_env (cb_region A B f g) A B f g e) <-> cb_edge A B f g e.
Proof. apply edge_formula_correct; apply EQ_refl. Qed.
Definition graph_by_formula A B f g := Comp (Prod A B)
  (fun e => holds edge_certificate (comparison_env (cb_region A B f g) A B f g e)).
Theorem graph_bounded_separation A B f g :
  EQ (cb_graph A B f g) (graph_by_formula A B f g).
Proof.
  assert (HP : forall e e',
    holds edge_certificate (comparison_env (cb_region A B f g) A B f g e) -> EQ e e' ->
    holds edge_certificate (comparison_env (cb_region A B f g) A B f g e')).
  { intros e e' H E. apply (proj2 (edge_certificate_correct A B f g e')).
    exact (cb_edge_extensional A B f g e e'
      (proj1 (edge_certificate_correct A B f g e) H) E). }
  apply INC_EQ; intros e H.
  - apply IN_P_Comp; [exact HP | exact (Comp_INC _ _ _ H) |].
    apply (proj2 (edge_certificate_correct A B f g e)).
    exact (IN_Comp_P _ _ _ (cb_edge_extensional A B f g) H).
  - apply IN_P_Comp; [exact (cb_edge_extensional A B f g) | exact (Comp_INC _ _ _ H) |].
    apply (proj1 (edge_certificate_correct A B f g e)).
    exact (IN_Comp_P _ _ _ HP H).
Qed.
Theorem bounded_comparison_bijection (classical_logic : forall P : Prop, P \/ ~ P) A B f g :
  injection A B f -> injection B A g -> bijection A B (graph_by_formula A B f g).
Proof.
  intros Hf Hg. unfold graph_by_formula.
  assert (E : EQ (cb_graph A B f g)
    (Comp (Prod A B) (fun e => holds edge_certificate
      (comparison_env (cb_region A B f g) A B f g e)))).
  { apply graph_bounded_separation. }
  pose proof (cb_graph_bijection A B f g Hf Hg classical_logic) as HB.
  unfold bijection in *. destruct HB as [HT [HI HS]]. split.
  - exact (IN_sound_left _ _ _ E HT).
  - split.
    + intros x x' y H H'. apply (HI x x' y).
      * exact (IN_sound_right _ _ _ (EQ_sym _ _ E) H).
      * exact (IN_sound_right _ _ _ (EQ_sym _ _ E) H').
    + intros y Hy. destruct (HS y Hy) as [x Hx]. exists x.
      exact (IN_sound_right _ _ _ E Hx).
Qed.
Print Assumptions graph_bounded_separation.
Print Assumptions bounded_comparison_bijection.

Definition successorF {n} (B C f g z : Fin n) :=
  disj (baseF B g z)
    (ex C (ex (fsucc B)
      (conj (applicationF (fsucc (fsucc f)) (fsucc fzero) fzero)
        (applicationF (fsucc (fsucc g)) fzero (fsucc (fsucc z)))))).
Theorem successor_formula_correct {n} (r : Fin n -> Ens) A B C f g z :
  EQ (r C) (cb_region (r A) (r B) (r f) (r g)) ->
  injection (r A) (r B) (r f) -> injection (r B) (r A) (r g) ->
  (holds (successorF B C f g z) r <->
    cb_successor_predicate (r A) (r B) (r f) (r g) (r z)).
Proof.
  intros EC Hf Hg. unfold successorF, cb_successor_predicate.
  cbn [holds]. setoid_rewrite base_formula_correct.
  setoid_rewrite application_correct. cbn [fin_match]. split.
  - intros [HB | [x [Hx [y [Hy [Hxy Hyz]]]]]]; [left; exact HB |].
    right; exists x; split; [exact (IN_sound_right x _ _ EC Hx) |].
    apply EQ_sym. unfold cb_step. eapply EQ_tran.
    + apply apply_set_extensional; [apply EQ_refl |].
      exact (function_value (r A) (r B) (r f) x y (proj1 Hf) Hxy).
    + exact (function_value (r B) (r A) (r g) y (r z) (proj1 Hg) Hyz).
  - intros [HB | [x [Hx E]]]; [left; exact HB |]. right.
    exists x; split; [exact (IN_sound_right x _ _ (EQ_sym _ _ EC) Hx) |].
    assert (HxA : IN x (r A)) by exact (Comp_INC _ _ _ Hx).
    pose proof (apply_set_typed (r A) (fun _ => r B) (r f) x (proj1 Hf) HxA) as Hy.
    exists (apply_set (r f) x); split; [exact Hy |]. split.
    + exact (apply_set_spec (r A) (fun _ => r B) (r f) x (proj1 Hf) HxA).
    + eapply application_arguments; [apply EQ_refl | apply EQ_refl | apply EQ_sym; exact E |].
      exact (apply_set_spec (r B) (fun _ => r A) (r g) (apply_set (r f) x) (proj1 Hg) Hy).
Qed.
Definition successor_certificate : Formula 6 := successorF
  (fsucc (fsucc fzero)) fzero (fsucc (fsucc (fsucc fzero)))
  (fsucc (fsucc (fsucc (fsucc fzero)))) (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))).
Lemma successor_certificate_correct A B f g z : injection A B f -> injection B A g ->
  (holds successor_certificate (comparison_env (cb_region A B f g) A B f g z) <->
    cb_successor_predicate A B f g z).
Proof.
  intros Hf Hg. exact (successor_formula_correct
    (comparison_env (cb_region A B f g) A B f g z)
    (fsucc fzero) (fsucc (fsucc fzero)) fzero (fsucc (fsucc (fsucc fzero)))
    (fsucc (fsucc (fsucc (fsucc fzero)))) (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))
    (EQ_refl _) Hf Hg).
Qed.
Definition successor_by_formula A B f g := Comp A
  (fun z => holds successor_certificate (comparison_env (cb_region A B f g) A B f g z)).
Theorem successor_bounded_separation A B f g : injection A B f -> injection B A g ->
  EQ (cb_successor A B f g) (successor_by_formula A B f g).
Proof.
  intros Hf Hg.
  assert (HP : forall z z',
    holds successor_certificate (comparison_env (cb_region A B f g) A B f g z) -> EQ z z' ->
    holds successor_certificate (comparison_env (cb_region A B f g) A B f g z')).
  { intros z z' H E. apply (proj2 (successor_certificate_correct A B f g z' Hf Hg)).
    exact (cb_successor_extensional A B f g z z'
      (proj1 (successor_certificate_correct A B f g z Hf Hg) H) E). }
  apply INC_EQ; intros z H.
  - apply IN_P_Comp; [exact HP | exact (Comp_INC _ _ _ H) |].
    apply (proj2 (successor_certificate_correct A B f g z Hf Hg)).
    exact (IN_Comp_P _ _ _ (cb_successor_extensional A B f g) H).
  - apply IN_P_Comp; [exact (cb_successor_extensional A B f g) | exact (Comp_INC _ _ _ H) |].
    apply (proj1 (successor_certificate_correct A B f g z Hf Hg)).
    exact (IN_Comp_P _ _ _ HP H).
Qed.
Print Assumptions successor_bounded_separation.
Check bounded_comparison_bijection.
