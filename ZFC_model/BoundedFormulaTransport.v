(** Extensional semantics for every formula in the bounded syntax. *)
From Equations Require Import Equations.
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax.
From PTSrkModel Require Import BoundedFormulas.
Import Bounded.

Lemma formula_environment_extend {n} x (r r' : Fin n -> Ens) :
  (forall i, EQ (r i) (r' i)) ->
  forall i, EQ (fin_match x r i) (fin_match x r' i).
Proof. intros E i; dependent elimination i; cbn; [apply EQ_refl | apply E]. Qed.

Theorem holds_extensional {n} (p : Formula n) :
  forall r r', (forall i, EQ (r i) (r' i)) -> (holds p r <-> holds p r').
Proof.
  induction p; intros r r' E; cbn [holds].
  - split; intro H.
    + eapply EQ_tran; [apply EQ_sym, E |]. eapply EQ_tran; [exact H | apply E].
    + eapply EQ_tran; [apply E |]. eapply EQ_tran; [exact H | apply EQ_sym, E].
  - split; intro H.
    + eapply IN_sound_right; [apply E |]. eapply IN_sound_left; [apply E | exact H].
    + eapply IN_sound_right; [apply EQ_sym, E |]. eapply IN_sound_left; [apply EQ_sym, E | exact H].
  - tauto.
  - rewrite (IHp1 r r' E), (IHp2 r r' E); reflexivity.
  - rewrite (IHp1 r r' E), (IHp2 r r' E); reflexivity.
  - rewrite (IHp1 r r' E), (IHp2 r r' E); reflexivity.
  - split; intros H x Hx.
    + apply (proj1 (IHp _ _ (formula_environment_extend x r r' E))).
      apply H. eapply IN_sound_right; [apply EQ_sym, E | exact Hx].
    + apply (proj2 (IHp _ _ (formula_environment_extend x r r' E))).
      apply H. eapply IN_sound_right; [apply E | exact Hx].
  - split; intros [x [Hx HP]]; exists x; split.
    + eapply IN_sound_right; [apply E | exact Hx].
    + apply (proj1 (IHp _ _ (formula_environment_extend x r r' E))); exact HP.
    + eapply IN_sound_right; [apply EQ_sym, E | exact Hx].
    + apply (proj2 (IHp _ _ (formula_environment_extend x r r' E))); exact HP.
Qed.
Print Assumptions holds_extensional.

Fixpoint rename_formula {n m} (f : Fin n -> Fin m) (p : Formula n) : Formula m :=
  match p in Formula k return (Fin k -> Fin m) -> Formula m with
  | @equal _ x y => fun f => equal (f x) (f y)
  | @member _ x y => fun f => member (f x) (f y)
  | @falsum _ => fun _ => falsum
  | @conj _ p q => fun f => conj (rename_formula f p) (rename_formula f q)
  | @disj _ p q => fun f => disj (rename_formula f p) (rename_formula f q)
  | @impl _ p q => fun f => impl (rename_formula f p) (rename_formula f q)
  | @all _ b p => fun f => all (f b) (rename_formula (weak f) p)
  | @ex _ b p => fun f => ex (f b) (rename_formula (weak f) p)
  end f.

Theorem holds_rename {n} (p : Formula n) : forall m (f : Fin n -> Fin m) r,
  holds (rename_formula f p) r <-> holds p (fun i => r (f i)).
Proof.
  induction p; intros m f r; cbn [rename_formula holds]; try reflexivity.
  - rewrite IHp1, IHp2; reflexivity.
  - rewrite IHp1, IHp2; reflexivity.
  - rewrite IHp1, IHp2; reflexivity.
  - assert (E : forall x, holds (rename_formula (weak f) p) (fin_match x r) <->
        holds p (fin_match x (fun i => r (f i)))).
    { intro x. rewrite IHp. apply holds_extensional.
      intro i; dependent elimination i; apply EQ_refl. }
    setoid_rewrite E; reflexivity.
  - assert (E : forall x, holds (rename_formula (weak f) p) (fin_match x r) <->
        holds p (fin_match x (fun i => r (f i)))).
    { intro x. rewrite IHp. apply holds_extensional.
      intro i; dependent elimination i; apply EQ_refl. }
    setoid_rewrite E; reflexivity.
Qed.
Print Assumptions holds_rename.
