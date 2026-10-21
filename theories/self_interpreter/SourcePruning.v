From Stdlib Require Import Arith.PeanoNat Lia Logic.Eqdep_dec.
From PTSrk Require Import -(notations) Syntax Context Typing Ranks.
From PTSrk.SelfInterpreter Require Import FullSource FullConversion.
Import Context.

(** Remove conversions whose source and target types are literally equal.
    The source judgment is retained, including every source annotation.
    Arbitrary beta-equivalent types are deliberately not identified. *)
Module SourcePruning.
Module FS := FullSource.FullSource.
Module FC := FullConversion.FullConversion.

Fixpoint prune {n G t T} (d : FS.derivation n G t T) : FS.derivation n G t T.
Proof.
  destruct d.
  - exact (FS.d_sort G r).
  - exact (FS.d_pi a b (prune _ _ _ _ d1) (prune _ _ _ _ d2)).
  - exact (FS.d_var G i).
  - exact (FS.d_lam a (prune _ _ _ _ d1) (prune _ _ _ _ d2)).
  - exact (FS.d_app (prune _ _ _ _ d1) (prune _ _ _ _ d2)).
  - destruct (FC.term_eq_dec A B) as [E|NE].
    + subst B; exact (prune _ _ _ _ d1).
    + exact (FS.d_conv b (prune _ _ _ _ d1) (prune _ _ _ _ d2) c).
Defined.

Theorem prune_original n G t T (d : FS.derivation n G t T) :
  @typ nat RankSorts n G t T.
Proof. exact (FS.derivation_sound n G t T (prune d)). Qed.

Theorem prune_reflexive n G t T b (d : FS.derivation n G t T)
    (f : FS.derivation n G T (𝓤 b)) (c : FS.conversion n T T) :
  prune (FS.d_conv b d f c) = prune d.
Proof.
  cbn [prune]; destruct (FC.term_eq_dec T T) as [E|NE]; [|contradiction].
  assert (E=eq_refl) by (apply UIP_dec; apply FC.term_eq_dec).
  subst E; reflexivity.
Qed.

Theorem prune_idempotent n G t T (d : FS.derivation n G t T) :
  prune (prune d) = prune d.
Proof.
  induction d; cbn [prune]; try (rewrite ?IHd1, ?IHd2; reflexivity).
  destruct (FC.term_eq_dec A B) as [E|NE].
  - destruct E; exact IHd1.
  - cbn [prune]; destruct (FC.term_eq_dec A B) as [E|NE']; [contradiction|].
    rewrite IHd1, IHd2; reflexivity.
Qed.

Fixpoint derivation_nodes {n G t T} (d : FS.derivation n G t T) : nat :=
  match d with
  | FS.d_sort _ _ | FS.d_var _ _ => 1
  | FS.d_pi _ _ p q | FS.d_lam _ p q | FS.d_app p q | FS.d_conv _ p q _ =>
      S (derivation_nodes p + derivation_nodes q)
  end.

(** Number of allocated equality layers in the existing structural quoter;
    its connection with the actual output plan is proved separately. *)
Fixpoint repair_count {n G t T} (d : FS.derivation n G t T) : nat :=
  match d with
  | FS.d_sort _ _ | FS.d_var _ _ => 0
  | FS.d_pi _ _ p q | FS.d_app p q | FS.d_conv _ p q _ =>
      2 + repair_count p + repair_count q
  | FS.d_lam _ p q => 1 + repair_count p + repair_count q
  end.

Theorem prune_nodes n G t T (d : FS.derivation n G t T) :
  derivation_nodes (prune d) <= derivation_nodes d.
Proof.
  induction d; cbn [prune derivation_nodes]; try lia.
  destruct (FC.term_eq_dec A B) as [E|NE]; [destruct E|];
    cbn [eq_rect derivation_nodes]; lia.
Qed.
Theorem prune_repairs n G t T (d : FS.derivation n G t T) :
  repair_count (prune d) <= repair_count d.
Proof.
  induction d; cbn [prune repair_count]; try lia.
  destruct (FC.term_eq_dec A B) as [E|NE]; [destruct E|];
    cbn [eq_rect repair_count]; lia.
Qed.
Theorem repair_count_bound n G t T (d : FS.derivation n G t T) :
  repair_count d < derivation_nodes d.
Proof. induction d; cbn [repair_count derivation_nodes]; lia. Qed.

Fixpoint pad h {n G t T} b (d : FS.derivation n G t T)
    (f : FS.derivation n G T (𝓤 b)) : FS.derivation n G t T :=
  match h with
  | 0 => d
  | S h' => FS.d_conv b (pad h' b d f) f (FS.c_refl T)
  end.
Theorem prune_padding h n G t T b (d : FS.derivation n G t T) f :
  prune (pad h b d f) = prune d.
Proof. induction h; [reflexivity|cbn [pad]; rewrite prune_reflexive; exact IHh]. Qed.
Theorem padding_cost h n G t T b (d : FS.derivation n G t T) f :
  repair_count (pad h b d f) = repair_count d + h * (2 + repair_count f).
Proof. induction h; cbn [pad repair_count]; lia. Qed.

Print Assumptions prune_original.
Print Assumptions prune_reflexive.
Print Assumptions prune_idempotent.
Print Assumptions prune_nodes.
Print Assumptions prune_repairs.
Print Assumptions repair_count_bound.
Print Assumptions prune_padding.
Print Assumptions padding_cost.
End SourcePruning.
