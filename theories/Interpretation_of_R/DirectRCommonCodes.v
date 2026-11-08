(** Shared annotated term builders and negative logic, independent of either carrier. *)
From Stdlib Require Import Arith.PeanoNat Lia Lists.List Bool.Bool.
From PTSrk Require Import -(notations) Syntax.
Import ListNotations.
Module CommonCodes.
(** A hygienic named assembler.  Its OUTPUT is the repository's own
    intrinsically scoped [Term nat n], not a parallel PTS syntax. *)
Inductive named : Type :=
| NSort : nat -> named
| NVar : nat -> named
| NPi : nat -> named -> named -> named
| NArrow : named -> named -> named
| NLam : nat -> named -> named -> named
| NApp : named -> named -> named
| NClosed : Term nat 0 -> named.

Fixpoint max_ident (t : named) : nat :=
  match t with
  | NSort _ => 0
  | NClosed _ => 0
  | NVar i => i
  | NPi i a b | NLam i a b => Nat.max i (Nat.max (max_ident a) (max_ident b))
  | NApp f a | NArrow f a => Nat.max (max_ident f) (max_ident a)
  end.

(** Adapted from clayrat/pts-dependent-types, PTS/Named.v at
    7e6282d357c6f42217a9584f6c7493c594ae1aed: an arrow binds no source name.
    Its codomain is assembled in the current environment and then shifted.
    This is builder syntax only, not a new constructor of PTSrk.Syntax.Term.
    See docs/PORTING-DirectR.md. *)
Definition nArrow (a b : named) : named := NArrow a b.
Definition napps (f : named) (args : list named) : named :=
  fold_left NApp args f.
Definition npis (fields : list (nat * named)) (body : named) : named :=
  fold_right (fun field b => NPi (fst field) (snd field) b) body fields.
Definition nlams (fields : list (nat * named)) (body : named) : named :=
  fold_right (fun field b => NLam (fst field) (snd field) b) body fields.

Fixpoint lookup (env : list nat) (x : nat) : option (Fin (List.length env)) :=
  match env as es return option (Fin (List.length es)) with
  | [] => None
  | y :: es =>
      if Nat.eqb x y then Some fzero
      else match lookup es x with
           | Some i => Some (fsucc i)
           | None => None
           end
  end.

Fixpoint assemble (t : named) (env : list nat)
  : option (Term nat (List.length env)) :=
  match t with
  | NSort r => Some (𝓤 r)
  | NClosed c => Some (rename (fun i : Fin 0 => match i with end) c)
  | NVar x =>
      match lookup env x with Some i => Some (var i) | None => None end
  | NPi x a b =>
      match assemble a env, assemble b (x :: env) with
      | Some a', Some b' => Some (Π a' b')
      | _, _ => None
      end
  | NArrow a b =>
      match assemble a env, assemble b env with
      | Some a', Some b' => Some (Π a' (shift b'))
      | _, _ => None
      end
  | NLam x a b =>
      match assemble a env, assemble b (x :: env) with
      | Some a', Some b' => Some (lam a' b')
      | _, _ => None
      end
  | NApp f a =>
      match assemble f env, assemble a env with
      | Some f', Some a' => Some (app f' a')
      | _, _ => None
      end
  end.

(** The successful arrow case is exactly the original nondependent Π.
    These new scripts, like the rest of the file, require a Rocq build. *)
Lemma assemble_nArrow (env : list nat) (a b : named)
    (A B : Term nat (List.length env)) :
  assemble a env = Some A -> assemble b env = Some B ->
  assemble (nArrow a b) env = Some (Π A (shift B)).
Proof.
  intros Ha Hb. unfold nArrow. cbn [assemble]. rewrite Ha, Hb. reflexivity.
Qed.

Example arrow_preserves_outer_reference :
  assemble (nArrow (NSort 0) (NVar 7)) [7] =
  Some (Π (𝓤 0) (var (fsucc fzero))).
Proof. reflexivity. Qed.

Example arrow_does_not_capture_or_invent_a_name :
  assemble (nArrow (NSort 0) (NVar 7)) [] = None.
Proof. reflexivity. Qed.

Definition closedb (t : named) : bool :=
  match assemble t [] with Some _ => true | None => false end.
Definition closed_term := Term nat 0.

(** Failure is not silently replaced by a default term: an actual proof
    that assembly succeeded is required.  This certifies SCOPE, not typing. *)
Definition close (t : named) (ok : closedb t = true) : closed_term.
Proof.
  unfold closedb in ok.
  destruct (assemble t []) as [u |].
  - exact u.
  - discriminate ok.
Defined.


Definition nBottom : named :=
  (NPi 0 (NSort 0) (NVar 0)).

Definition nTop : named :=
  (NPi 1 (NSort 0) (NSort 0)).

Definition nTopProof : named :=
  (NLam 0 (NSort 0) (NVar 0)).


Definition Bottom : closed_term := close nBottom eq_refl.
Definition Top : closed_term := close nTop eq_refl.
Definition top_proof : closed_term := close nTopProof eq_refl.

Definition empty_renaming {n : nat} (i : Fin 0) : Fin n := match i with end.
Definition lift_closed {n : nat} (t : closed_term) : Term nat n :=
  rename (@empty_renaming n) t.
Definition Arrow {n : nat} (a b : Term nat n) : Term nat n := Π a (shift b).
Definition V0 {n : nat} : Term nat (S n) := var fzero.


Definition Neg {n : nat} (a : Term nat n) : Term nat n := Arrow a (lift_closed Bottom).
Definition Conj {n : nat} (a b : Term nat n) : Term nat n :=
  Neg (Arrow a (Arrow b (lift_closed Bottom))).
Definition FlatOr {n : nat} (xs : list (Term nat n)) : Term nat n :=
  fold_right (fun a rest => Arrow (Neg a) rest) (lift_closed Bottom) xs.


(** The finite-selector syntax used by Lemma 3.  [selector] is intrinsically
    scoped for every arity.  This construction does not claim its PTS typing. *)
Fixpoint constant_lambdas (q : nat) {n : nat} (t : Term nat n) : Term nat n :=
  match q with
  | 0 => t
  | S k => lam (𝓤 1) (constant_lambdas k (shift t))
  end.
Fixpoint selector {q : nat} (i : Fin q) (n : nat) : Term nat n :=
  match i with
  | @fzero k => lam (𝓤 1) (constant_lambdas k (var fzero))
  | @fsucc k j => lam (𝓤 1) (selector j (S n))
  end.
Fixpoint selector_type (q n : nat) : Term nat n :=
  match q with
  | 0 => 𝓤 1
  | S k => Arrow (𝓤 1) (selector_type k n)
  end.
Example first_of_two_selectors :
  @selector 2 (@fzero 1) 0 = lam (𝓤 1) (lam (𝓤 1) (var (fsucc fzero))).
Proof. reflexivity. Qed.
Example second_of_two_selectors :
  @selector 2 (@fsucc 1 (@fzero 0)) 0 = lam (𝓤 1) (lam (𝓤 1) (var fzero)).
Proof. reflexivity. Qed.

Fixpoint nSelectorType (q : nat) : named :=
  match q with 0 => NSort 1 | S k => nArrow (NSort 1) (nSelectorType k) end.
Definition selector_binders (q : nat) : list (nat * named) :=
  map (fun i => (i, NSort 1)) (seq 0 q).
Definition nSelector (q i : nat) : named :=
  nlams (selector_binders q) (NVar i).
Definition nUnaryTable (q : nat) (h : nat -> nat) : named :=
  NLam q (nSelectorType q)
    (nlams (selector_binders q)
      (napps (NVar q) (map (fun i => NVar (h i)) (seq 0 q)))).
Definition nBinaryTable (q : nat) (h : nat -> nat -> nat) : named :=
  NLam q (nSelectorType q) (NLam (S q) (nSelectorType q)
    (nlams (selector_binders q)
      (napps (NVar q)
        (map (fun i => napps (NVar (S q))
                         (map (fun j => NVar (h i j)) (seq 0 q)))
             (seq 0 q))))).
Definition nRelationTable (q : nat) (truth : nat -> nat -> bool) : named :=
  NLam q (nSelectorType q) (NLam (S q) (nSelectorType q)
    (napps (NVar q)
      (map (fun i => napps (NVar (S q))
                       (map (fun j => if truth i j then nBottom else nTop)
                            (seq 0 q)))
           (seq 0 q)))).
Definition nDelta (q : nat) : named :=
  NLam q (nSelectorType q)
    (NPi (S q) (nArrow (nSelectorType q) (NSort 3))
      (fold_right nArrow
        (NApp (NVar (S q)) (NVar q))
        (map (fun i => NApp (NVar (S q)) (nSelector q i)) (seq 0 q)))).


Definition nJ2 : named :=
  (NPi 2 nTop nTop).

Definition nJ3 : named :=
  (NPi 3 nJ2 nJ2).

Definition nJ4 : named :=
  (NPi 4 nJ3 nJ3).

Definition nJ5 : named :=
  (NPi 5 nJ4 nJ4).

Definition nJ6 : named :=
  (NPi 6 nJ5 nJ5).

Definition nJ7 : named :=
  (NPi 7 nJ6 nJ6).

Definition nJ8 : named :=
  (NPi 8 nJ7 nJ7).

Definition nJ9 : named :=
  (NPi 9 nJ8 nJ8).

Definition nj9 : named :=
  (NLam 50 nJ8 (NVar 50)).

End CommonCodes.
