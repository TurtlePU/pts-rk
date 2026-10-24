(** Independent structural resources: binary trees, paths and growth.
    No source typing, acceptance or normalization occurs in this interface. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk.SelfConsistency Require Import StructuralCodes.
Import ListNotations.

Module ResourcePaths.
Inductive direction := Left | Right.
Definition path := list direction.
Fixpoint path_code (p : path) : code :=
  match p with
  | [] => Atom NZero
  | Left :: p => Pair (Atom PEven) (path_code p)
  | Right :: p => Pair (Atom POdd) (path_code p)
  end.
Fixpoint lookup (p : path) (tree : code) : option code :=
  match p, tree with
  | [], _ => Some tree
  | Left :: p, Pair a _ => lookup p a
  | Right :: p, Pair _ b => lookup p b
  | _ :: _, Atom _ => None
  end.

(** This is chronological prefix for append-only LEFT-spine buffers.
    It is not the two-sided subresource relation used for joining. *)
Inductive prefix : code -> code -> Prop :=
| prefix_refl a : prefix a a
| prefix_append a b entry : prefix a b -> prefix a (Pair b entry).
Inductive extends : code -> code -> Prop :=
| extends_refl a : extends a a
| extends_left a b entry : extends a b -> extends a (Pair b entry)
| extends_right a b entry : extends a b -> extends a (Pair entry b).

Theorem path_code_injective p q : path_code p = path_code q -> p = q.
Proof.
  revert q; induction p as [|[] p IH]; intros [|[] q] H;
    cbn in H; try discriminate; try reflexivity;
    f_equal; apply IH; injection H; auto.
Qed.
Theorem path_code_size p : code_size (path_code p) = 1 + 2 * length p.
Proof. induction p as [|[] p IH]; cbn in *; lia. Qed.
Theorem lookup_app p q tree :
  lookup (p ++ q) tree = match lookup p tree with Some u => lookup q u | None => None end.
Proof.
  revert tree; induction p as [|[] p IH]; intro tree; [reflexivity | |];
    destruct tree; cbn; auto.
Qed.
Theorem lookup_functional p tree u v :
  lookup p tree = Some u -> lookup p tree = Some v -> u = v.
Proof. congruence. Qed.
Lemma code_size_positive tree : 0 < code_size tree.
Proof. destruct tree; cbn; lia. Qed.
Theorem lookup_size_bound p tree v : lookup p tree = Some v ->
  code_size v + 2 * length p <= code_size tree.
Proof.
  revert tree v; induction p as [|[] p IH]; intros tree v H.
  - cbn in H; inversion H; subst; cbn; lia.
  - destruct tree as [t|a b]; [discriminate |]. cbn in H.
    specialize (IH a v H); pose proof (code_size_positive b); cbn; lia.
  - destruct tree as [t|a b]; [discriminate |]. cbn in H.
    specialize (IH b v H); pose proof (code_size_positive a); cbn; lia.
Qed.
Theorem prefix_transitive a b c : prefix a b -> prefix b c -> prefix a c.
Proof. intros H K; induction K; eauto using prefix_append. Qed.
Theorem serialized_lookup_bound p tree v : lookup p tree = Some v ->
  code_size v + code_size (path_code p) <= S (code_size tree).
Proof. intro H; pose proof (lookup_size_bound p tree v H); rewrite path_code_size; lia. Qed.
Theorem extension_transitive a b c : extends a b -> extends b c -> extends a c.
Proof. intros H K; induction K; eauto using extends_left, extends_right. Qed.
Theorem prefix_extension a b : prefix a b -> extends a b.
Proof. intro H; induction H; constructor; assumption. Qed.
Theorem extension_size a b : extends a b -> code_size a <= code_size b.
Proof. intro H; induction H; cbn; lia. Qed.
Theorem lookup_extension p tree v : lookup p tree = Some v -> extends v tree.
Proof.
  revert tree v; induction p as [|[] p IH]; intros tree v H.
  - cbn in H; inversion H; constructor.
  - destruct tree; [discriminate |]; apply extends_left, (IH _ _ H).
  - destruct tree; [discriminate |]; apply extends_right, (IH _ _ H).
Qed.
Theorem extension_has_path a b : extends a b -> exists p, lookup p b = Some a.
Proof.
  intro H; induction H as [a|a b e H [p Hp]|a b e H [p Hp]].
  - exists []; reflexivity.
  - exists (Left :: p); exact Hp.
  - exists (Right :: p); exact Hp.
Qed.
Theorem join_inclusions a b : extends a (Pair a b) /\ extends b (Pair a b).
Proof. split; [apply extends_left |apply extends_right]; constructor. Qed.
End ResourcePaths.
