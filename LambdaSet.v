Require Import Stdlib.Program.Equality.
Require Import Setoid.
Require Import Syntax.
Require Import DefinitionalEquivalence.

Generalizable Variables L X₀.

Class Λ_Set L X₀ :=
{ models: forall n, Term L n -> X₀ -> Prop }.

Infix "⊨" := (models _) (at level 60).

Inductive head_β_expansion {L n}: relation (Term L n) :=
| head_β_there t t' u:
    head_β_expansion t t' ->
    head_β_expansion (t $ u) (t' $ u)
| head_β_here U t u:
    SN U -> SN u ->
    head_β_expansion (λ U t $ u) (t ◁ u).

Definition Saturated {L}
  (𝓒: forall n, Term L n -> Prop) :=
  (forall n t, 𝓒 n t -> SN t)
  /\ (forall n t, SN t -> Atomic t -> 𝓒 n t)
  /\ (forall n t t', head_β_expansion t t' ->
      𝓒 n t' -> 𝓒 n t).

Class Saturated_Λ_Set `(X : Λ_Set L X₀) :=
{ realizers_SN {n} (t: Term L n) x: t ⊨ x -> SN t
; center: X₀
; center_realized {n} (t: Term L n):
    Atomic t -> SN t -> t ⊨ center
; realizers_expansion_closed {n} (t t': Term L n) x:
    head_β_expansion t t' -> t' ⊨ x -> t ⊨ x
}.

Remark realizers_are_saturated
  `(X: Saturated_Λ_Set L X₀):
  Saturated (fun _ t => exists x, t ⊨ x).
Proof. split;[|split].
- intros n t [x H].
  apply realizers_SN with (x := x).
  auto.
- intros. exists center. apply center_realized; auto.
- intros n t t' H1 [x H2]. exists x.
  apply realizers_expansion_closed with (t' := t');
  auto.
Qed.

Generalizable Variable Y₀.

Definition Λ_morphism
  `(X: Λ_Set L X₀) `(Y: Λ_Set L Y₀) :=
  { p: X₀ -> Y₀ | forall n (t: Term L n) x,
      t ⊨ x -> t ⊨ p x }.

Definition Λ_iso `(X: Λ_Set L X₀) `(Y: Λ_Set L Y₀) :=
  { pq: Λ_morphism X Y * Λ_morphism Y X |
      let '(exist _ p _, exist _ q _) := pq in
        (forall x, q (p x) = x)
        /\ (forall y, p (q y) = y) }.

Generalizable Variables 𝔈 𝔄.

Class 𝔈_Set L 𝔈 𝔄 :=
{ Λ_set: 𝔄 -> Type
; Λ_set_inst α: Λ_Set L (Λ_set α)
; set_equiv: 𝔈 -> relation 𝔄
; set_equiv_inst i: Equivalence (set_equiv i)
; carriers_equiv: 𝔈 -> relation (sigT Λ_set)
; carriers_equiv_inst i: Equivalence (carriers_equiv i)
}.

Instance Λ_Set_from_𝔈_Set `(𝔈_Set L 𝔈 𝔄) (α: 𝔄):
  Λ_Set L (Λ_set α) := Λ_set_inst α.

Infix "⟪ i ⟫" := (set_equiv i) (at level 50).

Notation "x ⟨ i ⟩ y" :=
  (carriers_equiv i
    (existT Λ_set _ x)
    (existT Λ_set _ y))
  (at level 50).

Generalizable Variable 𝔅.

Fixpoint adjust {m n}: Fin n -> Fin (m + n) :=
match m with
| 0 => fun i => i
| S m => fun i => fsucc (adjust i)
end.

Definition Π' `{𝔈_Set L 𝔈 𝔄} `{𝔈_Set L 𝔈 𝔅}
  (X: 𝔄) (Y: Λ_set X -> 𝔅): Type :=
    { f: forall α, Λ_set (Y α)
    | forall α α' i, α ⟨ i ⟩ α' -> f α ⟨ i ⟩ f α'
    }.

Instance Product `{𝔈_Set L 𝔈 𝔄} `{𝔈_Set L 𝔈 𝔅}
  (X: 𝔄) (Y: Λ_set X -> 𝔅): Λ_Set L (Π' X Y) :=
{ models := fun n t f =>
    forall α m (u: Term L (m + n)),
    u ⊨ α -> rename adjust t $ u ⊨ proj1_sig f α
}.

Lemma product_has_center `{𝔈_Set L 𝔈 𝔄} `{𝔈_Set L 𝔈 𝔅}
  {X: 𝔄} {Y: Λ_set X -> 𝔅}
  {Xs: Saturated_Λ_Set (Λ_set_inst X)}
  {Ys: forall α, Saturated_Λ_Set (Λ_set_inst (Y α))}:
  forall α α' i, α ⟨ i ⟩ α' ->
    @center _ _ _ (Ys α) ⟨ i ⟩ @center _ _ _ (Ys α').
Proof. Admitted. (* FIXME: discover equiv props *)

Lemma adjust_SN {L n} m (t: Term L n):
  SN (rename (@adjust m _) t) -> SN t.
Proof. intros. dependent induction H. constructor.
intros. apply H0 with (m := m) (y := rename adjust y);
auto. apply rename_step. auto. Qed.

Lemma rename_whe {L m n} (f: Fin m -> Fin n)
  (t t': Term L m):
  head_β_expansion t t' ->
  head_β_expansion (rename f t) (rename f t').
Proof. intros. induction H.
- constructor. auto.
- rewrite rename_subst.
  constructor; apply rename_SN; auto.
Qed.

Lemma whe_SN {L n} (t t' u: Term L n):
  head_β_expansion t t' -> SN (t' $ u) -> SN (t $ u).
Proof. Admitted. (* FIXME: adapt Altenkirch *)

#[refine]
Instance saturated_Product `(𝔈_Set L 𝔈 𝔄) `(𝔈_Set L 𝔈 𝔅)
  (X: 𝔄) (Y: Λ_set X -> 𝔅)
  {Xs: Saturated_Λ_Set (Λ_set_inst X)}
  {Ys: forall α, Saturated_Λ_Set (Λ_set_inst (Y α))}:
  Saturated_Λ_Set (Product X Y) := {
    center := exist _ (fun _ => center)
      product_has_center
}.
Proof.
- intros n t [f H1] H2. simpl in H2.
  apply adjust_SN with (m := 1).
  apply head_SN with (u := var fzero).
  apply realizers_SN with (x := f center).
  apply H2 with (m := 1).
  apply center_realized; constructor. intros.
  inversion H3.
- simpl. intros. apply center_realized.
  + constructor. apply rename_atomic. auto.
  + apply atomic_app_SN.
    * apply rename_atomic. auto.
    * apply rename_SN. auto.
    * apply realizers_SN with (x := α). auto.
- simpl. intros. apply realizers_expansion_closed
  with (t' := rename adjust t' $ u).
  + constructor. apply rename_whe. auto.
  + apply H2. auto.
Qed.

Definition Product_equiv `(𝔈_Set L 𝔈 𝔄) `(𝔈_Set L 𝔈 𝔅):
  𝔈 -> relation { X: 𝔄 & Λ_set X -> 𝔅 } :=
fun i xy xy' => match xy, xy' with
| existT _ X Y, existT _ X' Y' =>
    X ⟪ i ⟫ X'
    /\ (forall α α', α ⟨ i ⟩ α' -> Y α ⟪ i ⟫ Y' α')
end.

Definition Product_carrier_equiv
  `(𝔈_Set L 𝔈 𝔄) `(𝔈_Set L 𝔈 𝔅): 𝔈 ->
  relation { X: 𝔄 & { Y: Λ_set X -> 𝔅 & Π' X Y } } :=
fun i xyp xyp' => match xyp, xyp' with
| existT _ _ (existT _ _ (exist _ f _)),
    existT _ _ (existT _ _ (exist _ g _)) =>
      forall α α', α ⟨ i ⟩ α' -> f α ⟨ i ⟩ g α'
end.

Infix "⟪ i ⟫ₚ" := (Product_equiv i) (at level 50).
Infix "⟨ i ⟩ₚ" := (Product_carrier_equiv i)
  (at level 50).
