From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk.NormalizationComplexity Require Import Rank Bounds.
From Interpretation_of_R Require Import DirectREval.
From PTSrk.Combinatory Require Import FiniteNormalForms HilbertFiniteModels.
Import ListNotations RankEstimate.

(** A fixed finite constructor carrier with one explicit overflow value.
    The carrier contains POSITIONS, not proofs of list membership.  Duplicate
    source entries therefore require neither proof irrelevance nor quotienting.
    Guards are syntactic bounds alone; typing is not part of admission. *)
Module GuardedFiniteCarriers.
Module FNF := FiniteNormalForms.FiniteNormalForms.

Definition Carrier {X : Type} (xs : list X) : Type :=
  option (Fin (length xs)).

Fixpoint lookup {X : Type} (xs : list X) : Fin (length xs) -> X :=
  match xs as ys return Fin (length ys) -> X with
  | [] => fun i => match i with end
  | x :: ys => fin_match x (lookup ys)
  end.

Definition decode {X : Type} (xs : list X) (a : Carrier xs) : option X :=
  option_map (lookup xs) a.

Fixpoint encode {X : Type} (eq_dec : forall x y : X, {x = y} + {x <> y})
  (xs : list X) (x : X) : Carrier xs :=
  match xs as ys return Carrier ys with
  | [] => None
  | y :: ys => if eq_dec x y then Some fzero
               else option_map fsucc (encode eq_dec ys x)
  end.

Definition elements {X : Type} (xs : list X) : list (Carrier xs) :=
  None :: map Some (FNF.variables (length xs)).

Definition fin_eq_dec {n} (i j : Fin n) : {i = j} + {i <> j}.
Proof.
  destruct (RkEval.fin_eqb i j) eqn:E.
  - left; apply RkEval.fin_eqb_sound, E.
  - right; intro H; subst j; rewrite HilbertFiniteModels.fin_eqb_refl in E; discriminate.
Defined.

Definition carrier_eq_dec X (xs : list X) (a b : Carrier xs) : {a = b} + {a <> b}.
Proof. decide equality; apply fin_eq_dec. Defined.

Theorem elements_complete X (xs : list X) a : In a (elements xs).
Proof.
  unfold elements; destruct a as [i|].
  - right; apply in_map, FNF.variables_complete.
  - left; reflexivity.
Qed.

Theorem elements_length X (xs : list X) :
  length (elements xs) = S (length xs).
Proof. unfold elements; cbn [length]; rewrite length_map, FNF.variables_length; reflexivity. Qed.

Lemma lookup_member X (xs : list X) i : In (lookup xs i) xs.
Proof.
  induction xs as [|x xs IH]; [dependent elimination i |].
  dependent elimination i; cbn [lookup fin_match]; [left; reflexivity | right; apply IH].
Qed.

Theorem decode_member X (xs : list X) a x :
  decode xs a = Some x -> In x xs.
Proof.
  destruct a; cbn [decode]; [| discriminate].
  intro E; injection E as <-; apply lookup_member.
Qed.

Theorem decode_overflow X (xs : list X) a :
  decode xs a = None <-> a = None.
Proof. destruct a; cbn [decode option_map]; split; congruence. Qed.

Theorem decode_encode X eq_dec (xs : list X) x :
  In x xs -> decode xs (encode eq_dec xs x) = Some x.
Proof.
  induction xs as [|y xs IH]; [contradiction |].
  intro H; cbn [encode]; destruct (eq_dec x y) as [->|NE].
  - reflexivity.
  - assert (HX : In x xs) by (destruct H as [E|H]; [congruence|exact H]).
    specialize (IH HX); unfold decode in *.
    destruct (encode eq_dec xs x) as [i|]; cbn in *; [exact IH|discriminate].
Qed.

Theorem decode_encode_exact X eq_dec (xs : list X) x :
  decode xs (encode eq_dec xs x) = Some x <-> In x xs.
Proof. split; [apply decode_member | apply decode_encode]. Qed.

Theorem encode_overflow X eq_dec (xs : list X) x :
  encode eq_dec xs x = None <-> ~ In x xs.
Proof.
  split.
  - intros E H; pose proof (decode_encode X eq_dec xs x H) as HD.
    rewrite E in HD; discriminate.
  - induction xs as [|y xs IH]; [reflexivity|].
    intro H; cbn [encode]; destruct (eq_dec x y) as [E|NE].
    + exfalso; apply H; left; symmetry; exact E.
    + rewrite IH; [reflexivity|intro HX; apply H; right; exact HX].
Qed.

Theorem decode_encode_value X eq_dec (xs : list X) x y :
  decode xs (encode eq_dec xs x) = Some y <-> In x xs /\ y = x.
Proof.
  destruct (in_dec eq_dec x xs) as [HX|HX].
  - rewrite decode_encode by exact HX; split; [intro E; injection E; auto|intros [_ ->]; reflexivity].
  - rewrite (proj2 (encode_overflow X eq_dec xs x) HX); cbn [decode].
    split; [discriminate|intros [H _]; contradiction].
Qed.

Theorem encode_injective X eq_dec (xs : list X) x y :
  In x xs -> In y xs -> encode eq_dec xs x = encode eq_dec xs y -> x = y.
Proof.
  intros HX HY E; pose proof (f_equal (decode xs) E) as H.
  rewrite !decode_encode in H by assumption; injection H; auto.
Qed.

(** Operations may change the carrier's source type or its bounds.  In
    particular a native binder consumes an (n+1)-scoped body and an n-scoped
    annotation.  Every operation is total, even outside its explicit guard. *)
Definition lift1 {X Y : Type} eq_dec (xs : list X) (ys : list Y)
  (f : X -> Y) (a : Carrier xs) : Carrier ys :=
  match decode xs a with Some x => encode eq_dec ys (f x) | None => None end.

Definition lift2 {X Y Z : Type} eq_dec (xs : list X) (ys : list Y) (zs : list Z)
  (f : X -> Y -> Z) (a : Carrier xs) (b : Carrier ys) : Carrier zs :=
  match decode xs a, decode ys b with
  | Some x, Some y => encode eq_dec zs (f x y)
  | _, _ => None
  end.

Definition lift3 {W X Y Z : Type} eq_dec (ws : list W) (xs : list X)
  (ys : list Y) (zs : list Z) (f : W -> X -> Y -> Z)
  (a : Carrier ws) (b : Carrier xs) (c : Carrier ys) : Carrier zs :=
  match decode ws a, decode xs b, decode ys c with
  | Some w, Some x, Some y => encode eq_dec zs (f w x y)
  | _, _, _ => None
  end.

Theorem lift1_exact X Y eq_dec (xs : list X) (ys : list Y) f a y :
  decode ys (lift1 eq_dec xs ys f a) = Some y <->
  exists x, decode xs a = Some x /\ In (f x) ys /\ y = f x.
Proof.
  unfold lift1; destruct (decode xs a) as [x|] eqn:E.
  - rewrite decode_encode_value; split.
    + intros [H ->]; exists x; auto.
    + intros [x' [H [HF ->]]]; injection H as <-; auto.
  - cbn [decode option_map]; split; [discriminate|intros [x [H _]]; discriminate].
Qed.

Theorem lift2_exact X Y Z eq_dec (xs : list X) (ys : list Y) (zs : list Z)
  f a b z :
  decode zs (lift2 eq_dec xs ys zs f a b) = Some z <->
  exists x y, decode xs a = Some x /\ decode ys b = Some y /\
    In (f x y) zs /\ z = f x y.
Proof.
  unfold lift2; destruct (decode xs a) as [x|] eqn:EX;
    destruct (decode ys b) as [y|] eqn:EY; cbn [decode].
  - rewrite decode_encode_value; split.
    + intros [H ->]; exists x,y; auto.
    + intros [x' [y' [HX [HY [HF ->]]]]]; injection HX as <-; injection HY as <-; auto.
  - split; [discriminate|intros [x' [y' [_ [H _]]]]; discriminate].
  - split; [discriminate|intros [x' [y' [H _]]]; discriminate].
  - split; [discriminate|intros [x' [y' [H _]]]; discriminate].
Qed.

Theorem lift3_exact W X Y Z eq_dec (ws : list W) (xs : list X) (ys : list Y)
  (zs : list Z) f a b c z :
  decode zs (lift3 eq_dec ws xs ys zs f a b c) = Some z <->
  exists w x y, decode ws a = Some w /\ decode xs b = Some x /\
    decode ys c = Some y /\ In (f w x y) zs /\ z = f w x y.
Proof.
  unfold lift3; destruct (decode ws a) as [w|] eqn:EW;
    destruct (decode xs b) as [x|] eqn:EX;
    destruct (decode ys c) as [y|] eqn:EY; cbn [decode].
  { rewrite decode_encode_value; split.
    + intros [H ->]; exists w,x,y; repeat split; auto.
    + intros [w' [x' [y' [HW [HX [HY [HF ->]]]]]]];
        injection HW as <-; injection HX as <-; injection HY as <-; auto. }
  all: split; [discriminate|intros [w' [x' [y' [HW [HX [HY _]]]]]]; discriminate].
Qed.

Theorem lift1_encoded X Y eqX eqY (xs : list X) (ys : list Y) f x :
  In x xs -> In (f x) ys ->
  decode ys (lift1 eqY xs ys f (encode eqX xs x)) = Some (f x).
Proof. intros HX HF; apply lift1_exact; exists x; repeat split; auto using decode_encode. Qed.

Theorem lift2_encoded X Y Z eqX eqY eqZ (xs : list X) (ys : list Y)
  (zs : list Z) f x y : In x xs -> In y ys -> In (f x y) zs ->
  decode zs (lift2 eqZ xs ys zs f (encode eqX xs x) (encode eqY ys y)) = Some (f x y).
Proof. intros HX HY HF; apply lift2_exact; exists x,y; repeat split; auto using decode_encode. Qed.

Theorem lift1_overflow X Y eq_dec (xs : list X) (ys : list Y) f :
  lift1 eq_dec xs ys f None = None.
Proof. reflexivity. Qed.

Theorem lift2_overflow X Y Z eq_dec (xs : list X) (ys : list Y) (zs : list Z) f a b :
  a = None \/ b = None -> lift2 eq_dec xs ys zs f a b = None.
Proof.
  intros [-> | ->]; [reflexivity|unfold lift2; destruct (decode xs a); reflexivity].
Qed.

(** Literal native size/depth guards, including all lambda annotations and
    the exact finite universe-label alphabet. *)
Definition native_terms (size depth scope : nat) (alphabet : list nat) :
  list (Term nat scope) :=
  filter (fun t => Nat.leb (nodes t) size) (FNF.terms depth scope alphabet).

Definition NativeGuard {scope} size depth alphabet (t : Term nat scope) : Prop :=
  nodes t <= size /\ FNF.depth t <= depth /\ FNF.Uses alphabet t.

Theorem native_terms_exact size depth scope alphabet t :
  In t (native_terms size depth scope alphabet) <-> NativeGuard size depth alphabet t.
Proof.
  unfold native_terms, NativeGuard; rewrite filter_In, Nat.leb_le, FNF.terms_iff.
  tauto.
Qed.

Theorem native_terms_bound size depth scope alphabet :
  length (native_terms size depth scope alphabet) <=
    tower 2 (3 * depth + scope + length alphabet + 4).
Proof.
  unfold native_terms; eapply Nat.le_trans; [apply filter_length_le|apply FNF.terms_length_bound].
Qed.

Definition NativeCarrier size depth scope alphabet :=
  Carrier (native_terms size depth scope alphabet).

Definition native_encode size depth scope alphabet (t : Term nat scope) :
  NativeCarrier size depth scope alphabet :=
  encode HilbertFiniteModels.term_eq_dec (native_terms size depth scope alphabet) t.

Definition native_decode size depth scope alphabet :
  NativeCarrier size depth scope alphabet -> option (Term nat scope) :=
  decode (native_terms size depth scope alphabet).

Definition native_values size depth scope alphabet :
  list (NativeCarrier size depth scope alphabet) :=
  elements (native_terms size depth scope alphabet).

Theorem native_values_complete size depth scope alphabet a :
  In a (native_values size depth scope alphabet).
Proof. apply elements_complete. Qed.

Theorem native_decode_guard size depth scope alphabet a t :
  native_decode size depth scope alphabet a = Some t -> NativeGuard size depth alphabet t.
Proof. intro H; apply native_terms_exact; eapply decode_member; exact H. Qed.

Theorem native_encoding_exact size depth scope alphabet (t : Term nat scope) :
  decode (native_terms size depth scope alphabet) (native_encode size depth scope alphabet t) =
    Some t <-> NativeGuard size depth alphabet t.
Proof. unfold native_encode; rewrite decode_encode_exact; apply native_terms_exact. Qed.

Theorem native_coverage scope (t : Term nat scope) :
  decode (native_terms (nodes t) (FNF.depth t) scope (FNF.labels t))
    (native_encode (nodes t) (FNF.depth t) scope (FNF.labels t) t) = Some t.
Proof. apply native_encoding_exact; repeat split; auto using FNF.uses_self. Qed.

Theorem native_carrier_size size depth scope alphabet :
  length (elements (native_terms size depth scope alphabet)) <=
    S (tower 2 (3 * depth + scope + length alphabet + 4)).
Proof. rewrite elements_length; pose proof (native_terms_bound size depth scope alphabet); lia. Qed.

(** Fixed-budget total original constructors.  The equations below retain
    the output guard explicitly: a small input pair need not have a small
    application, binder or substituted result. *)
Definition native_app size depth scope alphabet
  (a b : NativeCarrier size depth scope alphabet) : NativeCarrier size depth scope alphabet :=
  lift2 HilbertFiniteModels.term_eq_dec
    (native_terms size depth scope alphabet) (native_terms size depth scope alphabet)
    (native_terms size depth scope alphabet) (@app nat scope) a b.

Definition native_pi size depth scope alphabet
  (a : NativeCarrier size depth scope alphabet)
  (b : NativeCarrier size depth (S scope) alphabet) : NativeCarrier size depth scope alphabet :=
  lift2 HilbertFiniteModels.term_eq_dec
    (native_terms size depth scope alphabet) (native_terms size depth (S scope) alphabet)
    (native_terms size depth scope alphabet) (@Π nat scope) a b.

Definition native_lam size depth scope alphabet
  (a : NativeCarrier size depth scope alphabet)
  (b : NativeCarrier size depth (S scope) alphabet) : NativeCarrier size depth scope alphabet :=
  lift2 HilbertFiniteModels.term_eq_dec
    (native_terms size depth scope alphabet) (native_terms size depth (S scope) alphabet)
    (native_terms size depth scope alphabet) (@lam nat scope) a b.

Definition native_subst size depth scope alphabet
  (b : NativeCarrier size depth (S scope) alphabet)
  (a : NativeCarrier size depth scope alphabet) : NativeCarrier size depth scope alphabet :=
  lift2 HilbertFiniteModels.term_eq_dec
    (native_terms size depth (S scope) alphabet) (native_terms size depth scope alphabet)
    (native_terms size depth scope alphabet) (@subst nat scope) b a.

Theorem native_app_exact size depth scope alphabet a b t :
  native_decode size depth scope alphabet (native_app size depth scope alphabet a b) = Some t <->
  exists f x, native_decode size depth scope alphabet a = Some f /\
    native_decode size depth scope alphabet b = Some x /\
    NativeGuard size depth alphabet (app f x) /\ t = app f x.
Proof.
  unfold native_app, native_decode; rewrite lift2_exact.
  setoid_rewrite native_terms_exact; reflexivity.
Qed.

Theorem native_pi_exact size depth scope alphabet a b t :
  native_decode size depth scope alphabet (native_pi size depth scope alphabet a b) = Some t <->
  exists A B, native_decode size depth scope alphabet a = Some A /\
    native_decode size depth (S scope) alphabet b = Some B /\
    NativeGuard size depth alphabet (Π A B) /\ t = Π A B.
Proof.
  unfold native_pi, native_decode; rewrite lift2_exact.
  setoid_rewrite native_terms_exact; reflexivity.
Qed.

Theorem native_lam_exact size depth scope alphabet a b t :
  native_decode size depth scope alphabet (native_lam size depth scope alphabet a b) = Some t <->
  exists A b', native_decode size depth scope alphabet a = Some A /\
    native_decode size depth (S scope) alphabet b = Some b' /\
    NativeGuard size depth alphabet (lam A b') /\ t = lam A b'.
Proof.
  unfold native_lam, native_decode; rewrite lift2_exact.
  setoid_rewrite native_terms_exact; reflexivity.
Qed.

Theorem native_subst_exact size depth scope alphabet b a t :
  native_decode size depth scope alphabet (native_subst size depth scope alphabet b a) = Some t <->
  exists b' x, native_decode size depth (S scope) alphabet b = Some b' /\
    native_decode size depth scope alphabet a = Some x /\
    NativeGuard size depth alphabet (subst b' x) /\ t = subst b' x.
Proof.
  unfold native_subst, native_decode; rewrite lift2_exact.
  setoid_rewrite native_terms_exact; reflexivity.
Qed.

End GuardedFiniteCarriers.

Print Assumptions GuardedFiniteCarriers.elements_complete.
Print Assumptions GuardedFiniteCarriers.carrier_eq_dec.
Print Assumptions GuardedFiniteCarriers.elements_length.
Print Assumptions GuardedFiniteCarriers.decode_member.
Print Assumptions GuardedFiniteCarriers.decode_overflow.
Print Assumptions GuardedFiniteCarriers.decode_encode.
Print Assumptions GuardedFiniteCarriers.decode_encode_exact.
Print Assumptions GuardedFiniteCarriers.encode_overflow.
Print Assumptions GuardedFiniteCarriers.decode_encode_value.
Print Assumptions GuardedFiniteCarriers.encode_injective.
Print Assumptions GuardedFiniteCarriers.lift1_exact.
Print Assumptions GuardedFiniteCarriers.lift2_exact.
Print Assumptions GuardedFiniteCarriers.lift3_exact.
Print Assumptions GuardedFiniteCarriers.lift1_encoded.
Print Assumptions GuardedFiniteCarriers.lift2_encoded.
Print Assumptions GuardedFiniteCarriers.lift1_overflow.
Print Assumptions GuardedFiniteCarriers.lift2_overflow.
Print Assumptions GuardedFiniteCarriers.native_terms_exact.
Print Assumptions GuardedFiniteCarriers.native_terms_bound.
Print Assumptions GuardedFiniteCarriers.native_encoding_exact.
Print Assumptions GuardedFiniteCarriers.native_values_complete.
Print Assumptions GuardedFiniteCarriers.native_decode_guard.
Print Assumptions GuardedFiniteCarriers.native_coverage.
Print Assumptions GuardedFiniteCarriers.native_carrier_size.
Print Assumptions GuardedFiniteCarriers.native_app_exact.
Print Assumptions GuardedFiniteCarriers.native_pi_exact.
Print Assumptions GuardedFiniteCarriers.native_lam_exact.
Print Assumptions GuardedFiniteCarriers.native_subst_exact.
