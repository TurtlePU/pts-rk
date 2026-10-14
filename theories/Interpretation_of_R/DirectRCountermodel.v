(** The explicit source countermodel in the harmonized note, for both the
    relational and functional presentations. This is NOT a PTS set model.
    Source non-derivability additionally needs soundness of a source proof system. *)
From Stdlib Require Import Arith.PeanoNat Lia.

Module SourceCountermodel.
Definition point := option nat.
Definition zero : point := Some 0.
Definition successor (x : point) : point := option_map S x.
Definition addition (x y : point) : point :=
  match x, y with Some m, Some n => Some (m+n) | _, _ => zero end.
Definition multiplication (x y : point) : point :=
  match x, y with Some m, Some n => Some (m*n) | _, _ => zero end.
Definition order (x y : point) : Prop :=
  match x, y with
  | Some m, Some n => m <= n
  | Some _, None => True
  | None, _ => False
  end.
Definition add_graph x y z := addition x y = z.
Definition mul_graph x y z := multiplication x y = z.
Fixpoint numeral n : point :=
  match n with 0 => zero | S k => successor (numeral k) end.
Lemma numeral_value n : numeral n = Some n.
Proof. induction n; cbn [numeral zero]; [reflexivity | rewrite IHn; reflexivity]. Qed.

Theorem ground_add m n : addition (numeral m) (numeral n) = numeral (m+n).
Proof. rewrite !numeral_value. reflexivity. Qed.
Theorem ground_mul m n : multiplication (numeral m) (numeral n) = numeral (m*n).
Proof. rewrite !numeral_value. reflexivity. Qed.
Theorem ground_add_graph m n x :
  add_graph (numeral m) (numeral n) x <-> numeral (m+n) = x.
Proof. unfold add_graph. rewrite ground_add. reflexivity. Qed.
Theorem ground_mul_graph m n x :
  mul_graph (numeral m) (numeral n) x <-> numeral (m*n) = x.
Proof. unfold mul_graph. rewrite ground_mul. reflexivity. Qed.
Theorem distinct m n : m <> n -> numeral m <> numeral n.
Proof. rewrite !numeral_value. congruence. Qed.
Theorem bounded n x :
  order x (numeral n) <-> exists i, i <= n /\ x = numeral i.
Proof.
  rewrite numeral_value. destruct x as [m|]; cbn [order].
  - split.
    + intro H. exists m. split; [exact H | symmetry; apply numeral_value].
    + intros [i [H E]]. rewrite numeral_value in E. injection E as E. lia.
  - split; [contradiction |].
    intros [i [_ E]]. rewrite numeral_value in E. discriminate.
Qed.
Theorem comparable n x : order x (numeral n) \/ order (numeral n) x.
Proof. rewrite numeral_value. destruct x; cbn [order]; [lia | right; exact I]. Qed.
Theorem failure_of_order_reflexivity : ~ (forall x, order x x).
Proof. intro H. exact (H None). Qed.

End SourceCountermodel.
