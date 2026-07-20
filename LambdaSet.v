Require Import Stdlib.Program.Equality.
Require Import Setoid.
Require Import Syntax.
Require Import StronglyNormalizing.
Require Import Atomic.
Require Import Reduction.

Generalizable Variables L X₀.

Class Λ_Set L X₀ :=
{ models: forall n, Term L n -> X₀ -> Prop }.

Infix "⊨" := (models _) (at level 60).

Definition Saturated {L}
  (𝓒: forall n, Term L n -> Prop) :=
  (forall n t, 𝓒 n t -> SN t)
  /\ (forall n t, SN t -> Atomic t -> 𝓒 n t)
  /\ (forall n t t', WHE t t' -> 𝓒 n t' -> 𝓒 n t).

Class Saturated_Λ_Set L X₀ `{Λ_Set L X₀} :=
{ realizers_SN {n} (t: Term L n) x: t ⊨ x -> SN t
; center: X₀
; center_realized {n} (t: Term L n):
    Atomic t -> SN t -> t ⊨ center
; realizers_expansion_closed {n} (t t': Term L n) x:
    WHE t t' -> t' ⊨ x -> t ⊨ x
}.

Remark realizers_are_saturated `(Saturated_Λ_Set L X₀):
  Saturated (fun _ t => exists x, t ⊨ x).
Proof. split;[|split].
- intros n t [x H'].
  apply realizers_SN with (x := x).
  auto.
- intros. exists center. apply center_realized; auto.
- intros n t t' H1 [x H2]. exists x.
  apply realizers_expansion_closed with (t' := t');
  auto.
Qed.

Generalizable Variable Y₀.

Definition Λ_morphism L X₀ Y₀ `{Λ_Set L X₀} `{Λ_Set L Y₀} :=
  { p: X₀ -> Y₀ | forall n (t: Term L n) x,
      t ⊨ x -> t ⊨ p x }.

Record Λ_iso L X₀ Y₀ `{Λ_Set L X₀} `{Λ_Set L Y₀} :=
  { forward: X₀ -> Y₀
  ; backward: Y₀ -> X₀
  ; fb_i x: backward (forward x) = x
  ; bf_i y: forward (backward y) = y
  ; respects_model {n} (t: Term L n) x:
      t ⊨ x <-> t ⊨ forward x
  }.

Coercion forward : Λ_iso >-> Funclass.

Definition inverse `{X: Λ_Set L X₀} `{Y: Λ_Set L Y₀}:
  @Λ_iso _ _ _ X Y -> @Λ_iso _ _ _ Y X.
Proof.
intros [f b fbi bfi rm].
apply Build_Λ_iso with (forward := b) (backward := f);
auto. intros. rewrite rm, bfi. reflexivity.
Defined.

Generalizable Variables 𝔈 𝔄 A.

Class 𝔈_Set L 𝔈 𝔄 A :=
  { Λ_set: 𝔄 -> A -> Prop
  ; Λ_set_inst α: Λ_Set L (sigT (Λ_set α))
  ; set_equiv: 𝔈 -> relation 𝔄
  ; set_equiv_inst i: Equivalence (set_equiv i)
  ; carriers_equiv: 𝔈 -> relation A
  ; carriers_equiv_inst i:
    Equivalence (carriers_equiv i)
  ; carriers_prop i {X X'} (x: sigT (Λ_set X))
      (x': sigT (Λ_set X')):
      set_equiv i X X' ->
      (forall n (t: Term L n), Atomic t ->
        t ⊨ x <-> t ⊨ x') ->
      carriers_equiv i (projT1 x) (projT1 x')
   }.

Instance Λ_Set_from_𝔈_Set `(𝔈_Set L 𝔈 𝔄) (α: 𝔄):
  Λ_Set L (sigT (Λ_set α)) := Λ_set_inst α.

Infix "⟪ i ⟫" := (set_equiv i) (at level 50).

Notation "x ⟨ i ⟩ y" :=
  (carriers_equiv i (projT1 x) (projT1 y))
  (at level 50).

Generalizable Variable 𝔅 B.

Definition Π' `{𝔈_Set L 𝔈 𝔄} `{𝔈_Set L 𝔈 𝔅}
  (X: 𝔄) (Y: sigT (Λ_set X) -> 𝔅): Type :=
    { f: forall α, sigT (Λ_set (Y α))
    | forall α α' i, α ⟨ i ⟩ α' -> f α ⟨ i ⟩ f α'
    }.

Instance Product `{𝔈_Set L 𝔈 𝔄} `{𝔈_Set L 𝔈 𝔅}
  (X: 𝔄) (Y: sigT (Λ_set X) -> 𝔅): Λ_Set L (Π' X Y) :=
{ models := fun n t f =>
    forall α m (u: Term L (m + n)),
    u ⊨ α -> rename adjust t $ u ⊨ proj1_sig f α
}.

Definition RespectfulMapping
  `{𝔈_Set L 𝔈 𝔄} `{𝔈_Set L 𝔈 𝔅}
  {X: 𝔄} (Y: sigT (Λ_set X) -> 𝔅) :=
  forall α α' i, α ⟨ i ⟩ α' -> Y α ⟪ i ⟫ Y α'.

Record Family `{𝔈_Set L 𝔈 𝔄} (X: 𝔄) 𝔅 `{𝔈_Set L 𝔈 𝔅} :=
  { mapping: sigT (Λ_set X) -> 𝔅
  ; mapping_respects: RespectfulMapping mapping
  }.

Coercion mapping: Family >-> Funclass.

Definition center_at `{𝔈_Set L 𝔈 𝔄} (X: 𝔄)
  `{@Saturated_Λ_Set _ _ (Λ_set_inst X)}:
  sigT (Λ_set X) := center.

Lemma center_prop `{Saturated_Λ_Set L X₀} {n}
  (t: Term L n): Atomic t -> SN t <-> t ⊨ center.
Proof. split; intro.
- apply center_realized; auto.
- apply realizers_SN with (x := center). auto.
Qed.

Lemma centers_are_equivalent `{𝔈_Set L 𝔈 𝔄} (X Y: 𝔄) i
  `{@Saturated_Λ_Set _ _ (Λ_set_inst X)}
  `{@Saturated_Λ_Set _ _ (Λ_set_inst Y)}:
  X ⟪ i ⟫ Y -> center_at X ⟨ i ⟩ center_at Y.
Proof.
intros. apply carriers_prop. auto. unfold center_at.
intros. repeat (rewrite <- (center_prop _ H3)).
reflexivity.
Qed.

#[refine]
Instance saturated_Product `(𝔈_Set L 𝔈 𝔄) `(𝔈_Set L 𝔈 𝔅)
  (X: 𝔄) (Y: Family X 𝔅)
  `{Xs: @Saturated_Λ_Set _ _ (Λ_set_inst X)}
  `{Ys: forall α,
      Saturated_Λ_Set L (sigT (Λ_set (Y α)))}:
  Saturated_Λ_Set L (Π' X Y) := {
    center := exist _ (fun _ => center) _
}.
Proof.
- intros n t [f H1] H2. simpl in H2.
  apply adjust_SN with (m := 1).
  apply head_SN with (u := var fzero).
  apply realizers_SN with (x := f center).
  apply H2 with (m := 1).
  apply center_realized; constructor. intros.
  inversion H3.
- intros.
  apply centers_are_equivalent, mapping_respects. auto.
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

Definition Product_equiv `{𝔈_Set L 𝔈 𝔄} `{𝔈_Set L 𝔈 𝔅}:
  𝔈 -> relation { X: 𝔄 & sigT (Λ_set X) -> 𝔅 } :=
fun i xy xy' => match xy, xy' with
| existT _ X Y, existT _ X' Y' =>
    X ⟪ i ⟫ X'
    /\ (forall α α', α ⟨ i ⟩ α' -> Y α ⟪ i ⟫ Y' α')
end.

Definition Product_carrier_equiv
  `{𝔈_Set L 𝔈 𝔄} `{𝔈_Set L 𝔈 𝔅}: 𝔈 ->
  relation { X: 𝔄
           & { Y: sigT (Λ_set X) -> 𝔅 & Π' X Y } } :=
fun i xyp xyp' => match xyp, xyp' with
| existT _ _ (existT _ _ (exist _ f _)),
    existT _ _ (existT _ _ (exist _ g _)) =>
      forall α α', α ⟨ i ⟩ α' -> f α ⟨ i ⟩ g α'
end.

Infix "⟪ i ⟫ₚ" := (Product_equiv i) (at level 50).
Notation "f ⟨ i ⟩ₚ g" :=
  (Product_carrier_equiv i
    (existT _ _ (existT _ _ f))
    (existT _ _ (existT _ _ g)))
  (at level 50).
