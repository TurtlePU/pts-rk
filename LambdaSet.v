Require Import Stdlib.Program.Equality.
Require Import Setoid.
Require Import Syntax.
Require Import StronglyNormalizing.
Require Import Atomic.
Require Import Reduction.

Class Λ_Set X₀ L :=
{ models: forall n, Term L n -> X₀ -> Prop }.

Infix "⊨" := (models _) (at level 60).

Definition Saturated {L}
  (𝓒: forall n, Term L n -> Prop) :=
  (forall n t, 𝓒 n t -> SN t)
  /\ (forall n t, SN t -> Atomic t -> 𝓒 n t)
  /\ (forall n t t', WHE t t' -> 𝓒 n t' -> 𝓒 n t).

Class Saturated_Λ_Set X₀ L `{Λ_Set X₀ L} :=
{ realizers_SN {n} (t: Term L n) x: t ⊨ x -> SN t
; center: X₀
; center_realized {n} (t: Term L n):
    Atomic t -> SN t -> t ⊨ center
; realizers_expansion_closed {n} (t t': Term L n) x:
    WHE t t' -> t' ⊨ x -> t ⊨ x
}.

Generalizable Variables X₀ L.

Remark realizers_are_saturated `(Saturated_Λ_Set):
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

Definition Λ_morphism X₀ Y₀
    `{Λ_Set X₀ L} `{Λ_Set Y₀ L} :=
  { p: X₀ -> Y₀ | forall n (t: Term L n) x,
      t ⊨ x -> t ⊨ p x }.

Record Λ_iso X₀ Y₀ `{Λ_Set X₀ L} `{Λ_Set Y₀ L} :=
  { forward: X₀ -> Y₀
  ; backward: Y₀ -> X₀
  ; fb_i x: backward (forward x) = x
  ; bf_i y: forward (backward y) = y
  ; respects_model {n} (t: Term L n) x:
      t ⊨ x <-> t ⊨ forward x
  }.

Coercion forward : Λ_iso >-> Funclass.

Generalizable Variable Y₀.

Definition inverse `{X: Λ_Set X₀ L} `{Y: Λ_Set Y₀ L}:
  @Λ_iso _ _ _ X Y -> @Λ_iso _ _ _ Y X.
Proof.
intros [f b fbi bfi rm].
apply Build_Λ_iso with (forward := b) (backward := f);
auto. intros. rewrite rm, bfi. reflexivity.
Defined.

Class 𝔈_Set 𝔄 A L 𝔈 :=
{ Λ_set: 𝔄 -> A -> Prop
; Λ_set_inst α: Λ_Set (sig (Λ_set α)) L
; set_equiv: 𝔈 -> relation 𝔄
; set_equiv_inst i: Equivalence (set_equiv i)
; carriers_equiv: 𝔈 -> relation A
; carriers_equiv_inst i:
    Equivalence (carriers_equiv i)
; carriers_prop i {X X'} (x: sig (Λ_set X))
    (x': sig (Λ_set X')):
      set_equiv i X X' ->
      (forall n (t: Term L n), Atomic t ->
        t ⊨ x <-> t ⊨ x') ->
      carriers_equiv i (proj1_sig x) (proj1_sig x')
}.

Notation "▵ α" := (sig (Λ_set α)) (at level 50).

Generalizable Variables 𝔄 A 𝔈.

Instance Λ_Set_from_𝔈_Set `(𝔈_Set) (α: 𝔄):
  Λ_Set (▵ α) L := Λ_set_inst α.

Notation "α ⊏ X" := (Λ_set X α) (at level 50).

Infix "⟪ i ⟫" := (set_equiv i) (at level 50).

Notation "x ⟨ i ⟩ y" :=
  (carriers_equiv i (proj1_sig x) (proj1_sig y))
  (at level 50).

Notation "x ⟨ i | X ⟩ y" :=
  (@carriers_equiv X _ _ _ _ i (proj1_sig x)
    (proj1_sig y))
  (at level 50).

Generalizable Variable 𝔅 B.

Definition Π' `{𝔈_Set 𝔄 A L 𝔈} `{𝔈_Set 𝔅 B L 𝔈}
  (X: 𝔄) (Y: ▵ X -> 𝔅): Type :=
    { f: forall α, ▵ (Y α)
    | forall α α' i, α ⟨ i ⟩ α' -> f α ⟨ i ⟩ f α'
    }.

Instance Product `{𝔈_Set 𝔄 A L 𝔈} `{𝔈_Set 𝔅 B L 𝔈}
  (X: 𝔄) (Y: ▵ X -> 𝔅): Λ_Set (Π' X Y) L :=
{ models := fun n t f =>
    forall α m (u: Term L (m + n)),
    u ⊨ α -> rename adjust t $ u ⊨ proj1_sig f α
}.

Definition RespectfulMapping `{𝔈_Set 𝔄 A L 𝔈}
  `{𝔈_Set 𝔅 B L 𝔈} {X: 𝔄} (Y: ▵ X -> 𝔅) :=
  forall α α' i, α ⟨ i ⟩ α' -> Y α ⟪ i ⟫ Y α'.

Record Family `{𝔈_Set 𝔄 A L 𝔈} (X: 𝔄) 𝔅 `{𝔈_Set 𝔅 B L 𝔈}
  := { mapping: ▵ X -> 𝔅
     ; mapping_respects: RespectfulMapping mapping
     }.

Coercion mapping: Family >-> Funclass.

Definition center_at `{𝔈_Set} (X: 𝔄)
  `{@Saturated_Λ_Set _ _ (Λ_set_inst X)}: ▵ X := center.

Lemma center_prop `{Saturated_Λ_Set} {n} (t: Term L n):
  Atomic t -> SN t <-> t ⊨ center.
Proof. split; intro.
- apply center_realized; auto.
- apply realizers_SN with (x := center). auto.
Qed.

Lemma centers_are_equivalent `{𝔈_Set} (X Y: 𝔄) i
  `{@Saturated_Λ_Set _ _ (Λ_set_inst X)}
  `{@Saturated_Λ_Set _ _ (Λ_set_inst Y)}:
  X ⟪ i ⟫ Y -> center_at X ⟨ i ⟩ center_at Y.
Proof.
intros. apply carriers_prop. auto. unfold center_at.
intros. repeat (rewrite <- (center_prop _ H3)).
reflexivity.
Qed.

#[refine]
Instance saturated_Product `(𝔈_Set 𝔄 A L 𝔈)
  `(𝔈_Set 𝔅 B L 𝔈) (X: 𝔄) (Y: Family X 𝔅)
  `{Xs: @Saturated_Λ_Set _ _ (Λ_set_inst X)}
  `{Ys: forall α, Saturated_Λ_Set (▵ (Y α)) L}:
  Saturated_Λ_Set (Π' X Y) L := {
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

Notation "⦃ x , y ⦄" := (existT _ x y) (at level 40).

Definition Product_equiv `{𝔈_Set 𝔄 A L 𝔈}
  `{𝔈_Set 𝔅 B L 𝔈}: 𝔈 ->
    relation { X: 𝔄 & ▵ X -> 𝔅 } :=
fun i '⦃ X, Y ⦄ '⦃ X', Y' ⦄ =>
    X ⟪ i ⟫ X'
    /\ (forall α α', α ⟨ i ⟩ α' -> Y α ⟪ i ⟫ Y' α').

Definition Product_carrier_equiv `{𝔈_Set 𝔄 A L 𝔈}
  `{𝔈_Set 𝔅 B L 𝔈}: 𝔈 ->
    relation { X: 𝔄 & { Y: ▵ X -> 𝔅 & Π' X Y } } :=
fun i '⦃_, ⦃_, exist _ f _ ⦄ ⦄
  '⦃_, ⦃_, exist _ g _ ⦄ ⦄ =>
    forall α α', α ⟨ i ⟩ α' -> f α ⟨ i ⟩ g α'.

Infix "⟪ i ⟫ₚ" := (Product_equiv i) (at level 50).
Notation "f ⟨ i ⟩ₚ g" :=
  (Product_carrier_equiv i
    (existT _ _ (existT _ _ f))
    (existT _ _ (existT _ _ g)))
  (at level 50).
