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
