(** Direct R interpretation -- restructured draft, 2026-10-13.
    Compiler-unchecked. No new PTS axioms or answer-type nontriviality claims.
    See docs/DirectR.md and docs/DirectR-obligations.md. *)

From Stdlib Require Import Arith.PeanoNat Lia Lists.List Bool.Bool.
(* The upstream lambda notation [T] t conflicts with list literals. *)
From PTSrk Require Import -(notations) Syntax.
Import ListNotations.

Module Codes.

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

(** The numeric names below are local binder names, erased by [assemble].
    Observation parameters: 0=X, 1=z, 2=s, 3=a, 4=m, 5=delta, 6=R0, 7=C0.
    Observation certificates have names 100--122.  Each object binder in
    a law is immediately followed by its delta guard. *)
Definition nBottom : named :=
  (NPi 0 (NSort 0) (NVar 0)).

Definition nTop : named :=
  (NPi 1 (NSort 0) (NSort 0)).

Definition nTopProof : named :=
  (NLam 0 (NSort 0) (NVar 0)).

Definition nDomain : named :=
  (NPi 0 (NSort 1) (NPi 5 (NVar 0) (NPi 4 (NPi 1 (NVar 0) (NVar 0)) (NPi 3 (NPi 2 (NVar 0) (NPi 1
  (NVar 0) (NVar 0))) (NPi 1 (NPi 2 (NVar 0) (NPi 1 (NVar 0) (NVar 0))) (NVar 0)))))).

Definition nZero : named :=
  (NLam 0 (NSort 1) (NLam 1 (NVar 0) (NLam 2 (NPi 1 (NVar 0) (NVar 0)) (NLam 3 (NPi 2 (NVar 0) (NPi
  1 (NVar 0) (NVar 0))) (NLam 4 (NPi 2 (NVar 0) (NPi 1 (NVar 0) (NVar 0))) (NVar 1)))))).

Definition nSucc : named :=
  (NLam 20 nDomain (NLam 0 (NSort 1) (NLam 1 (NVar 0) (NLam 2 (NPi 1 (NVar 0) (NVar 0)) (NLam 3 (NPi
  2 (NVar 0) (NPi 1 (NVar 0) (NVar 0))) (NLam 4 (NPi 2 (NVar 0) (NPi 1 (NVar 0) (NVar 0))) (napps
  (NVar 2) [(napps (NVar 20) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)])]))))))).

Definition nAdd : named :=
  (NLam 20 nDomain (NLam 21 nDomain (NLam 0 (NSort 1) (NLam 1 (NVar 0) (NLam 2 (NPi 1 (NVar 0) (NVar
  0)) (NLam 3 (NPi 2 (NVar 0) (NPi 1 (NVar 0) (NVar 0))) (NLam 4 (NPi 2 (NVar 0) (NPi 1 (NVar 0)
  (NVar 0))) (napps (NVar 3) [(napps (NVar 20) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]);
  (napps (NVar 21) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)])])))))))).

Definition nMul : named :=
  (NLam 20 nDomain (NLam 21 nDomain (NLam 0 (NSort 1) (NLam 1 (NVar 0) (NLam 2 (NPi 1 (NVar 0) (NVar
  0)) (NLam 3 (NPi 2 (NVar 0) (NPi 1 (NVar 0) (NVar 0))) (NLam 4 (NPi 2 (NVar 0) (NPi 1 (NVar 0)
  (NVar 0))) (napps (NVar 4) [(napps (NVar 20) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]);
  (napps (NVar 21) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)])])))))))).

Definition nGood : named :=
  (NLam 20 nDomain (NPi 40 (NPi 1 nDomain (NSort 10)) (NPi 42 (napps (NVar 40) [nZero]) (NPi 43 (NPi
  30 nDomain (NPi 41 (napps (NVar 40) [(NVar 30)]) (napps (NVar 40) [(napps nSucc [(NVar 30)])])))
  (NPi 44 (NPi 30 nDomain (NPi 31 nDomain (NPi 42 (napps (NVar 40) [(NVar 30)]) (NPi 41 (napps (NVar
  40) [(NVar 31)]) (napps (NVar 40) [(napps nAdd [(NVar 30); (NVar 31)])]))))) (NPi 45 (NPi 30
  nDomain (NPi 31 nDomain (NPi 42 (napps (NVar 40) [(NVar 30)]) (NPi 41 (napps (NVar 40) [(NVar
  31)]) (napps (NVar 40) [(napps nMul [(NVar 30); (NVar 31)])]))))) (napps (NVar 40) [(NVar
  20)]))))))).

Definition nGoodZero : named :=
  (NLam 40 (NPi 1 nDomain (NSort 10)) (NLam 42 (napps (NVar 40) [nZero]) (NLam 43 (NPi 30 nDomain
  (NPi 41 (napps (NVar 40) [(NVar 30)]) (napps (NVar 40) [(napps nSucc [(NVar 30)])]))) (NLam 44
  (NPi 30 nDomain (NPi 31 nDomain (NPi 42 (napps (NVar 40) [(NVar 30)]) (NPi 41 (napps (NVar 40)
  [(NVar 31)]) (napps (NVar 40) [(napps nAdd [(NVar 30); (NVar 31)])]))))) (NLam 45 (NPi 30 nDomain
  (NPi 31 nDomain (NPi 42 (napps (NVar 40) [(NVar 30)]) (NPi 41 (napps (NVar 40) [(NVar 31)]) (napps
  (NVar 40) [(napps nMul [(NVar 30); (NVar 31)])]))))) (NVar 42)))))).

Definition nGoodSucc : named :=
  (NLam 20 nDomain (NLam 22 (napps nGood [(NVar 20)]) (NLam 40 (NPi 1 nDomain (NSort 10)) (NLam 42
  (napps (NVar 40) [nZero]) (NLam 43 (NPi 30 nDomain (NPi 41 (napps (NVar 40) [(NVar 30)]) (napps
  (NVar 40) [(napps nSucc [(NVar 30)])]))) (NLam 44 (NPi 30 nDomain (NPi 31 nDomain (NPi 42 (napps
  (NVar 40) [(NVar 30)]) (NPi 41 (napps (NVar 40) [(NVar 31)]) (napps (NVar 40) [(napps nAdd [(NVar
  30); (NVar 31)])]))))) (NLam 45 (NPi 30 nDomain (NPi 31 nDomain (NPi 42 (napps (NVar 40) [(NVar
  30)]) (NPi 41 (napps (NVar 40) [(NVar 31)]) (napps (NVar 40) [(napps nMul [(NVar 30); (NVar
  31)])]))))) (napps (NVar 43) [(NVar 20); (napps (NVar 22) [(NVar 40); (NVar 42); (NVar 43); (NVar
  44); (NVar 45)])])))))))).

Definition nGoodAdd : named :=
  (NLam 20 nDomain (NLam 21 nDomain (NLam 22 (napps nGood [(NVar 20)]) (NLam 23 (napps nGood [(NVar
  21)]) (NLam 40 (NPi 1 nDomain (NSort 10)) (NLam 42 (napps (NVar 40) [nZero]) (NLam 43 (NPi 30
  nDomain (NPi 41 (napps (NVar 40) [(NVar 30)]) (napps (NVar 40) [(napps nSucc [(NVar 30)])])))
  (NLam 44 (NPi 30 nDomain (NPi 31 nDomain (NPi 42 (napps (NVar 40) [(NVar 30)]) (NPi 41 (napps
  (NVar 40) [(NVar 31)]) (napps (NVar 40) [(napps nAdd [(NVar 30); (NVar 31)])]))))) (NLam 45 (NPi
  30 nDomain (NPi 31 nDomain (NPi 42 (napps (NVar 40) [(NVar 30)]) (NPi 41 (napps (NVar 40) [(NVar
  31)]) (napps (NVar 40) [(napps nMul [(NVar 30); (NVar 31)])]))))) (napps (NVar 44) [(NVar 20);
  (NVar 21); (napps (NVar 22) [(NVar 40); (NVar 42); (NVar 43); (NVar 44); (NVar 45)]); (napps (NVar
  23) [(NVar 40); (NVar 42); (NVar 43); (NVar 44); (NVar 45)])])))))))))).

Definition nGoodMul : named :=
  (NLam 20 nDomain (NLam 21 nDomain (NLam 22 (napps nGood [(NVar 20)]) (NLam 23 (napps nGood [(NVar
  21)]) (NLam 40 (NPi 1 nDomain (NSort 10)) (NLam 42 (napps (NVar 40) [nZero]) (NLam 43 (NPi 30
  nDomain (NPi 41 (napps (NVar 40) [(NVar 30)]) (napps (NVar 40) [(napps nSucc [(NVar 30)])])))
  (NLam 44 (NPi 30 nDomain (NPi 31 nDomain (NPi 42 (napps (NVar 40) [(NVar 30)]) (NPi 41 (napps
  (NVar 40) [(NVar 31)]) (napps (NVar 40) [(napps nAdd [(NVar 30); (NVar 31)])]))))) (NLam 45 (NPi
  30 nDomain (NPi 31 nDomain (NPi 42 (napps (NVar 40) [(NVar 30)]) (NPi 41 (napps (NVar 40) [(NVar
  31)]) (napps (NVar 40) [(napps nMul [(NVar 30); (NVar 31)])]))))) (napps (NVar 45) [(NVar 20);
  (NVar 21); (napps (NVar 22) [(NVar 40); (NVar 42); (NVar 43); (NVar 44); (NVar 45)]); (napps (NVar
  23) [(NVar 40); (NVar 42); (NVar 43); (NVar 44); (NVar 45)])])))))))))).

(* The 8 data parameters followed by 23 individually guarded laws. *)
Definition observation_fields : list (nat * named) :=
  [
    (0, (NSort 1));
    (1, (NVar 0));
    (2, (NPi 1 (NVar 0) (NVar 0)));
    (3, (NPi 2 (NVar 0) (NPi 1 (NVar 0) (NVar 0))));
    (4, (NPi 2 (NVar 0) (NPi 1 (NVar 0) (NVar 0))));
    (5, (NPi 1 (NVar 0) (NSort 4)));
    (6, (NPi 2 (NVar 0) (NPi 1 (NVar 0) (NSort 1))));
    (7, (NPi 2 (NVar 0) (NPi 1 (NVar 0) (NSort 1))));
    (* dom_zero *)
    (100, (napps (NVar 5) [(NVar 1)]));
    (* dom_succ *)
    (101, (NPi 30 (NVar 0) (NPi 1030 (napps (NVar 5) [(NVar 30)]) (napps (NVar 5) [(napps (NVar 2) [(NVar 30)])]))));
    (* dom_add *)
    (102, (NPi 30 (NVar 0) (NPi 1030 (napps (NVar 5) [(NVar 30)]) (NPi 31 (NVar 0) (NPi 1031 (napps (NVar 5) [(NVar 31)]) (napps (NVar 5) [(napps (NVar 3) [(NVar 30); (NVar 31)])]))))));
    (* dom_mul *)
    (103, (NPi 30 (NVar 0) (NPi 1030 (napps (NVar 5) [(NVar 30)]) (NPi 31 (NVar 0) (NPi 1031 (napps (NVar 5) [(NVar 31)]) (napps (NVar 5) [(napps (NVar 4) [(NVar 30); (NVar 31)])]))))));
    (* eq_refl *)
    (104, (NPi 30 (NVar 0) (NPi 1030 (napps (NVar 5) [(NVar 30)]) (NPi 1 (napps (NVar 6) [(NVar 30); (NVar 30)]) nBottom))));
    (* eq_sym *)
    (105, (NPi 30 (NVar 0) (NPi 1030 (napps (NVar 5) [(NVar 30)]) (NPi 31 (NVar 0) (NPi 1031 (napps (NVar 5) [(NVar 31)]) (NPi 32 (NPi 1 (napps (NVar 6) [(NVar 30); (NVar 31)]) nBottom) (NPi 1 (napps (NVar 6) [(NVar 31); (NVar 30)]) nBottom)))))));
    (* eq_trans *)
    (106, (NPi 30 (NVar 0) (NPi 1030 (napps (NVar 5) [(NVar 30)]) (NPi 31 (NVar 0) (NPi 1031 (napps (NVar 5) [(NVar 31)]) (NPi 32 (NVar 0) (NPi 1032 (napps (NVar 5) [(NVar 32)]) (NPi 34 (NPi 1 (napps (NVar 6) [(NVar 30); (NVar 31)]) nBottom) (NPi 33 (NPi 1 (napps (NVar 6) [(NVar 31); (NVar 32)]) nBottom) (NPi 1 (napps (NVar 6) [(NVar 30); (NVar 32)]) nBottom))))))))));
    (* succ_congr *)
    (107, (NPi 30 (NVar 0) (NPi 1030 (napps (NVar 5) [(NVar 30)]) (NPi 31 (NVar 0) (NPi 1031 (napps (NVar 5) [(NVar 31)]) (NPi 32 (NPi 1 (napps (NVar 6) [(NVar 30); (NVar 31)]) nBottom) (NPi 1 (napps (NVar 6) [(napps (NVar 2) [(NVar 30)]); (napps (NVar 2) [(NVar 31)])]) nBottom)))))));
    (* add_congr *)
    (108, (NPi 30 (NVar 0) (NPi 1030 (napps (NVar 5) [(NVar 30)]) (NPi 33 (NVar 0) (NPi 1033 (napps (NVar 5) [(NVar 33)]) (NPi 31 (NVar 0) (NPi 1031 (napps (NVar 5) [(NVar 31)]) (NPi 34 (NVar 0) (NPi 1034 (napps (NVar 5) [(NVar 34)]) (NPi 36 (NPi 1 (napps (NVar 6) [(NVar 30); (NVar 33)]) nBottom) (NPi 35 (NPi 1 (napps (NVar 6) [(NVar 31); (NVar 34)]) nBottom) (NPi 1 (napps (NVar 6) [(napps (NVar 3) [(NVar 30); (NVar 31)]); (napps (NVar 3) [(NVar 33); (NVar 34)])]) nBottom))))))))))));
    (* mul_congr *)
    (109, (NPi 30 (NVar 0) (NPi 1030 (napps (NVar 5) [(NVar 30)]) (NPi 33 (NVar 0) (NPi 1033 (napps (NVar 5) [(NVar 33)]) (NPi 31 (NVar 0) (NPi 1031 (napps (NVar 5) [(NVar 31)]) (NPi 34 (NVar 0) (NPi 1034 (napps (NVar 5) [(NVar 34)]) (NPi 36 (NPi 1 (napps (NVar 6) [(NVar 30); (NVar 33)]) nBottom) (NPi 35 (NPi 1 (napps (NVar 6) [(NVar 31); (NVar 34)]) nBottom) (NPi 1 (napps (NVar 6) [(napps (NVar 4) [(NVar 30); (NVar 31)]); (napps (NVar 4) [(NVar 33); (NVar 34)])]) nBottom))))))))))));
    (* order_congr *)
    (110, (NPi 30 (NVar 0) (NPi 1030 (napps (NVar 5) [(NVar 30)]) (NPi 33 (NVar 0) (NPi 1033 (napps (NVar 5) [(NVar 33)]) (NPi 31 (NVar 0) (NPi 1031 (napps (NVar 5) [(NVar 31)]) (NPi 34 (NVar 0) (NPi 1034 (napps (NVar 5) [(NVar 34)]) (NPi 37 (NPi 1 (napps (NVar 6) [(NVar 30); (NVar 33)]) nBottom) (NPi 36 (NPi 1 (napps (NVar 6) [(NVar 31); (NVar 34)]) nBottom) (NPi 35 (NPi 1 (napps (NVar 7) [(NVar 30); (NVar 31)]) nBottom) (NPi 1 (napps (NVar 7) [(NVar 33); (NVar 34)]) nBottom)))))))))))));
    (* order_refl *)
    (111, (NPi 30 (NVar 0) (NPi 1030 (napps (NVar 5) [(NVar 30)]) (NPi 1 (napps (NVar 7) [(NVar 30); (NVar 30)]) nBottom))));
    (* order_trans *)
    (112, (NPi 30 (NVar 0) (NPi 1030 (napps (NVar 5) [(NVar 30)]) (NPi 31 (NVar 0) (NPi 1031 (napps (NVar 5) [(NVar 31)]) (NPi 32 (NVar 0) (NPi 1032 (napps (NVar 5) [(NVar 32)]) (NPi 34 (NPi 1 (napps (NVar 7) [(NVar 30); (NVar 31)]) nBottom) (NPi 33 (NPi 1 (napps (NVar 7) [(NVar 31); (NVar 32)]) nBottom) (NPi 1 (napps (NVar 7) [(NVar 30); (NVar 32)]) nBottom))))))))));
    (* add_zero *)
    (113, (NPi 30 (NVar 0) (NPi 1030 (napps (NVar 5) [(NVar 30)]) (NPi 1 (napps (NVar 6) [(napps (NVar 3) [(NVar 1); (NVar 30)]); (NVar 30)]) nBottom))));
    (* add_succ *)
    (114, (NPi 30 (NVar 0) (NPi 1030 (napps (NVar 5) [(NVar 30)]) (NPi 31 (NVar 0) (NPi 1031 (napps (NVar 5) [(NVar 31)]) (NPi 1 (napps (NVar 6) [(napps (NVar 3) [(napps (NVar 2) [(NVar 30)]); (NVar 31)]); (napps (NVar 2) [(napps (NVar 3) [(NVar 30); (NVar 31)])])]) nBottom))))));
    (* mul_zero *)
    (115, (NPi 30 (NVar 0) (NPi 1030 (napps (NVar 5) [(NVar 30)]) (NPi 1 (napps (NVar 6) [(napps (NVar 4) [(NVar 1); (NVar 30)]); (NVar 1)]) nBottom))));
    (* mul_succ *)
    (116, (NPi 30 (NVar 0) (NPi 1030 (napps (NVar 5) [(NVar 30)]) (NPi 31 (NVar 0) (NPi 1031 (napps (NVar 5) [(NVar 31)]) (NPi 1 (napps (NVar 6) [(napps (NVar 4) [(napps (NVar 2) [(NVar 30)]); (NVar 31)]); (napps (NVar 3) [(NVar 31); (napps (NVar 4) [(NVar 30); (NVar 31)])])]) nBottom))))));
    (* mul_zero_right *)
    (117, (NPi 30 (NVar 0) (NPi 1030 (napps (NVar 5) [(NVar 30)]) (NPi 1 (napps (NVar 6) [(napps (NVar 4) [(NVar 30); (NVar 1)]); (NVar 1)]) nBottom))));
    (* le_succ *)
    (118, (NPi 30 (NVar 0) (NPi 1030 (napps (NVar 5) [(NVar 30)]) (NPi 1 (napps (NVar 7) [(NVar 30); (napps (NVar 2) [(NVar 30)])]) nBottom))));
    (* le_add_left *)
    (119, (NPi 30 (NVar 0) (NPi 1030 (napps (NVar 5) [(NVar 30)]) (NPi 31 (NVar 0) (NPi 1031 (napps (NVar 5) [(NVar 31)]) (NPi 1 (napps (NVar 7) [(NVar 30); (napps (NVar 3) [(NVar 30); (NVar 31)])]) nBottom))))));
    (* le_add_right *)
    (120, (NPi 30 (NVar 0) (NPi 1030 (napps (NVar 5) [(NVar 30)]) (NPi 31 (NVar 0) (NPi 1031 (napps (NVar 5) [(NVar 31)]) (NPi 1 (napps (NVar 7) [(NVar 31); (napps (NVar 3) [(NVar 30); (NVar 31)])]) nBottom))))));
    (* le_mul_left *)
    (121, (NPi 30 (NVar 0) (NPi 1030 (napps (NVar 5) [(NVar 30)]) (NPi 31 (NVar 0) (NPi 1031 (napps (NVar 5) [(NVar 31)]) (NPi 32 (NPi 1 (napps (NVar 7) [(napps (NVar 2) [(NVar 1)]); (NVar 31)]) nBottom) (NPi 1 (napps (NVar 7) [(NVar 30); (napps (NVar 4) [(NVar 30); (NVar 31)])]) nBottom)))))));
    (* le_mul_right *)
    (122, (NPi 30 (NVar 0) (NPi 1030 (napps (NVar 5) [(NVar 30)]) (NPi 31 (NVar 0) (NPi 1031 (napps (NVar 5) [(NVar 31)]) (NPi 32 (NPi 1 (napps (NVar 7) [(napps (NVar 2) [(NVar 1)]); (NVar 30)]) nBottom) (NPi 1 (napps (NVar 7) [(NVar 31); (napps (NVar 4) [(NVar 30); (NVar 31)])]) nBottom)))))))
  ].

Definition nAllObs (body : named) : named := npis observation_fields body.
Definition nAbstractObs (body : named) : named := nlams observation_fields body.

Definition nEquality : named :=
  (NLam 20 nDomain (NLam 21 nDomain (nAllObs (NPi 1 (napps (NVar 6) [(napps (NVar 20) [(NVar 0);
  (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 21) [(NVar 0); (NVar 1); (NVar 2); (NVar
  3); (NVar 4)])]) nBottom)))).

Definition nOrder : named :=
  (NLam 20 nDomain (NLam 21 nDomain (nAllObs (NPi 1 (napps (NVar 7) [(napps (NVar 20) [(NVar 0);
  (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 21) [(NVar 0); (NVar 1); (NVar 2); (NVar
  3); (NVar 4)])]) nBottom)))).

Definition nAdmittedObservations : named :=
  (NLam 20 nDomain (nAllObs (napps (NVar 5) [(napps (NVar 20) [(NVar 0); (NVar 1); (NVar 2); (NVar
  3); (NVar 4)])]))).

Definition nGZero : named :=
  (nAbstractObs (NVar 100)).

Definition nGSucc : named :=
  (NLam 20 nDomain (NLam 22 (napps nAdmittedObservations [(NVar 20)]) (nAbstractObs (napps (NVar
  101) [(napps (NVar 20) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 22)
  [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar
  101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar
  109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar
  117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)])])))).

Definition nGAdd : named :=
  (NLam 20 nDomain (NLam 21 nDomain (NLam 22 (napps nAdmittedObservations [(NVar 20)]) (NLam 23
  (napps nAdmittedObservations [(NVar 21)]) (nAbstractObs (napps (NVar 102) [(napps (NVar 20) [(NVar
  0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 22) [(NVar 0); (NVar 1); (NVar 2);
  (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar 103);
  (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar 111);
  (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar 119);
  (NVar 120); (NVar 121); (NVar 122)]); (napps (NVar 21) [(NVar 0); (NVar 1); (NVar 2); (NVar 3);
  (NVar 4)]); (napps (NVar 23) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar
  6); (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106);
  (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114);
  (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar
  122)])])))))).

Definition nGMul : named :=
  (NLam 20 nDomain (NLam 21 nDomain (NLam 22 (napps nAdmittedObservations [(NVar 20)]) (NLam 23
  (napps nAdmittedObservations [(NVar 21)]) (nAbstractObs (napps (NVar 103) [(napps (NVar 20) [(NVar
  0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 22) [(NVar 0); (NVar 1); (NVar 2);
  (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar 103);
  (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar 111);
  (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar 119);
  (NVar 120); (NVar 121); (NVar 122)]); (napps (NVar 21) [(NVar 0); (NVar 1); (NVar 2); (NVar 3);
  (NVar 4)]); (napps (NVar 23) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar
  6); (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106);
  (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114);
  (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar
  122)])])))))).

Definition nEqRefl : named :=
  (NLam 20 nDomain (NLam 22 (napps nAdmittedObservations [(NVar 20)]) (nAbstractObs (napps (NVar
  104) [(napps (NVar 20) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 22)
  [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar
  101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar
  109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar
  117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)])])))).

Definition nOrderRefl : named :=
  (NLam 20 nDomain (NLam 22 (napps nAdmittedObservations [(NVar 20)]) (nAbstractObs (napps (NVar
  111) [(napps (NVar 20) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 22)
  [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar
  101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar
  109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar
  117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)])])))).

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

Definition nGoodToG : named :=
  (NLam 20 nDomain (NLam 22 (napps nGood [(NVar 20)]) (napps (NVar 22) [(NLam 30 nDomain (NPi 1035
  nJ9 (napps nAdmittedObservations [(NVar 30)]))); (NLam 50 nJ9 nGZero); (NLam 30 nDomain (NLam 51
  (napps (NLam 30 nDomain (NPi 1035 nJ9 (napps nAdmittedObservations [(NVar 30)]))) [(NVar 30)])
  (NLam 50 nJ9 (napps nGSucc [(NVar 30); (napps (NVar 51) [nj9])])))); (NLam 30 nDomain (NLam 31
  nDomain (NLam 51 (napps (NLam 30 nDomain (NPi 1035 nJ9 (napps nAdmittedObservations [(NVar 30)])))
  [(NVar 30)]) (NLam 52 (napps (NLam 30 nDomain (NPi 1035 nJ9 (napps nAdmittedObservations [(NVar
  30)]))) [(NVar 31)]) (NLam 50 nJ9 (napps nGAdd [(NVar 30); (NVar 31); (napps (NVar 51) [nj9]);
  (napps (NVar 52) [nj9])])))))); (NLam 30 nDomain (NLam 31 nDomain (NLam 51 (napps (NLam 30 nDomain
  (NPi 1035 nJ9 (napps nAdmittedObservations [(NVar 30)]))) [(NVar 30)]) (NLam 52 (napps (NLam 30
  nDomain (NPi 1035 nJ9 (napps nAdmittedObservations [(NVar 30)]))) [(NVar 31)]) (NLam 50 nJ9 (napps
  nGMul [(NVar 30); (NVar 31); (napps (NVar 51) [nj9]); (napps (NVar 52) [nj9])])))))); nj9]))).

(** All of these are terms in [PTSrk.Syntax.Term nat 0].
    The [eq_refl] arguments prove only that the assembler found no free names. *)
Definition Bottom : closed_term := close nBottom eq_refl.
Definition Top : closed_term := close nTop eq_refl.
Definition top_proof : closed_term := close nTopProof eq_refl.
Definition Domain : closed_term := close nDomain eq_refl.
Definition zero : closed_term := close nZero eq_refl.
Definition successor : closed_term := close nSucc eq_refl.
Definition addition : closed_term := close nAdd eq_refl.
Definition multiplication : closed_term := close nMul eq_refl.
Definition Good : closed_term := close nGood eq_refl.
Definition Equality : closed_term := close nEquality eq_refl.
Definition Order : closed_term := close nOrder eq_refl.
Definition G : closed_term := close nAdmittedObservations eq_refl.

Definition good_zero_proof : closed_term := close nGoodZero eq_refl.
Definition good_succ_proof : closed_term := close nGoodSucc eq_refl.
Definition good_add_proof : closed_term := close nGoodAdd eq_refl.
Definition good_mul_proof : closed_term := close nGoodMul eq_refl.
Definition g_zero_proof : closed_term := close nGZero eq_refl.
Definition g_succ_proof : closed_term := close nGSucc eq_refl.
Definition g_add_proof : closed_term := close nGAdd eq_refl.
Definition g_mul_proof : closed_term := close nGMul eq_refl.
Definition equality_refl_proof : closed_term := close nEqRefl eq_refl.
Definition order_refl_proof : closed_term := close nOrderRefl eq_refl.
Definition good_to_g_proof : closed_term := close nGoodToG eq_refl.

Definition empty_renaming {n : nat} (i : Fin 0) : Fin n := match i with end.
Definition lift_closed {n : nat} (t : closed_term) : Term nat n :=
  rename (@empty_renaming n) t.
Definition Arrow {n : nat} (a b : Term nat n) : Term nat n := Π a (shift b).
Definition V0 {n : nat} : Term nat (S n) := var fzero.

Definition GoodAt {n : nat} (d : Term nat n) : Term nat n := app (lift_closed Good) d.
Definition GAt {n : nat} (d : Term nat n) : Term nat n := app (lift_closed G) d.
Definition EqAt {n : nat} (d e : Term nat n) : Term nat n :=
  app (app (lift_closed Equality) d) e.
Definition LeAt {n : nat} (d e : Term nat n) : Term nat n :=
  app (app (lift_closed Order) d) e.
Definition Neg {n : nat} (a : Term nat n) : Term nat n := Arrow a (lift_closed Bottom).
Definition Conj {n : nat} (a b : Term nat n) : Term nat n :=
  Neg (Arrow a (Arrow b (lift_closed Bottom))).
Definition FlatOr {n : nat} (xs : list (Term nat n)) : Term nat n :=
  fold_right (fun a rest => Arrow (Neg a) rest) (lift_closed Bottom) xs.

Fixpoint numeral (n : nat) : closed_term :=
  match n with 0 => zero | S k => app successor (numeral k) end.

Definition CaseAt {k : nat} (n : nat) (d : Term nat k) : Term nat k :=
  FlatOr
    (map (fun i => EqAt d (lift_closed (numeral i))) (seq 0 (S n)) ++
     [LeAt (lift_closed (numeral (S n))) d]).

Definition InvariantAt {k : nat} (n : nat) (d : Term nat k) : Term nat k :=
  Π (𝓤 8)
    (Arrow (Arrow (shift (GAt d)) (Arrow (shift (CaseAt n d)) V0)) V0).

(** Closed types for exactly the five axiom schemes in the note.
    Kernel and Generated below contain typing proofs and instance witnesses. *)
Definition R1 (m n : nat) : closed_term :=
  EqAt (app (app addition (numeral m)) (numeral n)) (numeral (m + n)).
Definition R2 (m n : nat) : closed_term :=
  EqAt (app (app multiplication (numeral m)) (numeral n)) (numeral (m * n)).
Definition R3 (m n : nat) : closed_term := Neg (EqAt (numeral m) (numeral n)).
Definition R4 (n : nat) : closed_term :=
  Π Domain
    (Arrow (GoodAt V0)
      (Arrow (LeAt V0 (lift_closed (numeral n)))
        (FlatOr (map (fun i => EqAt V0 (lift_closed (numeral i))) (seq 0 (S n)))))).
Definition R5 (n : nat) : closed_term :=
  Π Domain
    (Arrow (GoodAt V0)
      (FlatOr [LeAt V0 (lift_closed (numeral n));
               LeAt (lift_closed (numeral n)) V0])).

(** Types of the concrete witnesses.  The corresponding repository-typing
    statements and proof scripts occur in Kernel below. *)
Definition good_zero_type : closed_term := GoodAt zero.
Definition good_succ_type : closed_term :=
  Π Domain (Arrow (GoodAt V0) (GoodAt (app (lift_closed successor) V0))).
Definition good_binary_type (op : closed_term) : closed_term :=
  Π Domain (Π (lift_closed Domain)
    (Arrow (GoodAt (var (fsucc fzero)))
      (Arrow (GoodAt V0)
        (GoodAt (app (app (lift_closed op) (var (fsucc fzero))) V0))))).
Definition g_zero_type : closed_term := GAt zero.
Definition g_succ_type : closed_term :=
  Π Domain (Arrow (GAt V0) (GAt (app (lift_closed successor) V0))).
Definition g_binary_type (op : closed_term) : closed_term :=
  Π Domain (Π (lift_closed Domain)
    (Arrow (GAt (var (fsucc fzero)))
      (Arrow (GAt V0)
        (GAt (app (app (lift_closed op) (var (fsucc fzero))) V0))))).
Definition equality_refl_type : closed_term :=
  Π Domain (Arrow (GAt V0) (EqAt V0 V0)).
Definition order_refl_type : closed_term :=
  Π Domain (Arrow (GAt V0) (LeAt V0 V0)).
Definition good_to_g_type : closed_term :=
  Π Domain (Arrow (GoodAt V0) (GAt V0)).

Inductive axiom_instance : Type :=
| ax_add : nat -> nat -> axiom_instance
| ax_mul : nat -> nat -> axiom_instance
| ax_distinct : forall m n : nat, m <> n -> axiom_instance
| ax_bounded : nat -> axiom_instance
| ax_comparison : nat -> axiom_instance.

Definition axiom_type (a : axiom_instance) : closed_term :=
  match a with
  | ax_add m n => R1 m n
  | ax_mul m n => R2 m n
  | ax_distinct m n _ => R3 m n
  | ax_bounded n => R4 n
  | ax_comparison n => R5 n
  end.

(** Sanity checks of scope at the Rocq term level.  These are not typing tests. *)
Example no_unbound_named_variable : assemble (NVar 0) [] = None.
Proof. reflexivity. Qed.
Example shadowing_is_lexical :
  assemble (NLam 0 (NSort 0) (NLam 0 (NSort 0) (NVar 0))) [] =
  Some (lam (𝓤 0) (lam (𝓤 0) (var fzero))).
Proof. reflexivity. Qed.
Example domain_assembly_succeeds : closedb nDomain = true.
Proof. reflexivity. Qed.
Example equality_assembly_succeeds : closedb nEquality = true.
Proof. reflexivity. Qed.
Example good_to_g_assembly_succeeds : closedb nGoodToG = true.
Proof. reflexivity. Qed.


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

(** Ordered as X,z,s,a,m,delta,R0,C0. This is only the data sublist;
    Generated.observation_arguments also constructs the 23 law witnesses. *)
Definition nCappedObservationData (K : nat) : list named :=
  let c := S K in
  let q := S c in
  [nSelectorType q;
   nSelector q 0;
   nUnaryTable q (fun i => Nat.min (S i) c);
   nBinaryTable q (fun i j => Nat.min (i + j) c);
   nBinaryTable q (fun i j => Nat.min (i * j) c);
   nDelta q;
   nRelationTable q Nat.eqb;
   nRelationTable q Nat.leb].

Example two_state_observation_data_are_closed :
  forallb closedb (nCappedObservationData 0) = true.
Proof. reflexivity. Qed.
Example five_state_observation_data_are_closed :
  forallb closedb (nCappedObservationData 3) = true.
Proof. reflexivity. Qed.

(** Additional closed observation-law combinators. *)
Definition nLaw_eq_refl : named :=
  (NLam 200 nDomain (NLam 201 (napps nAdmittedObservations [(NVar 200)]) (nAbstractObs (napps (NVar
  104) [(napps (NVar 200) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 201)
  [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar
  101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar
  109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar
  117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)])])))).
Definition nLaw_eq_reflType : named :=
  (NPi 200 nDomain (NPi 201 (napps nAdmittedObservations [(NVar 200)]) (napps nEquality [(NVar 200);
  (NVar 200)]))).
Definition Law_eq_refl : closed_term := close nLaw_eq_refl eq_refl.
Definition Law_eq_reflType : closed_term := close nLaw_eq_reflType eq_refl.

Definition nLaw_eq_sym : named :=
  (NLam 200 nDomain (NLam 201 (napps nAdmittedObservations [(NVar 200)]) (NLam 202 nDomain (NLam 203
  (napps nAdmittedObservations [(NVar 202)]) (NLam 300 (napps nEquality [(NVar 200); (NVar 202)])
  (nAbstractObs (napps (NVar 105) [(napps (NVar 200) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar
  4)]); (napps (NVar 201) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6);
  (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106);
  (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114);
  (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)]);
  (napps (NVar 202) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 203) [(NVar
  0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101);
  (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109);
  (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117);
  (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)]); (napps (NVar 300) [(NVar 0); (NVar
  1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar
  102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109); (NVar
  110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117); (NVar
  118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)])]))))))).
Definition nLaw_eq_symType : named :=
  (NPi 200 nDomain (NPi 201 (napps nAdmittedObservations [(NVar 200)]) (NPi 202 nDomain (NPi 203
  (napps nAdmittedObservations [(NVar 202)]) (NPi 300 (napps nEquality [(NVar 200); (NVar 202)])
  (napps nEquality [(NVar 202); (NVar 200)])))))).
Definition Law_eq_sym : closed_term := close nLaw_eq_sym eq_refl.
Definition Law_eq_symType : closed_term := close nLaw_eq_symType eq_refl.

Definition nLaw_eq_trans : named :=
  (NLam 200 nDomain (NLam 201 (napps nAdmittedObservations [(NVar 200)]) (NLam 202 nDomain (NLam 203
  (napps nAdmittedObservations [(NVar 202)]) (NLam 204 nDomain (NLam 205 (napps
  nAdmittedObservations [(NVar 204)]) (NLam 300 (napps nEquality [(NVar 200); (NVar 202)]) (NLam 301
  (napps nEquality [(NVar 202); (NVar 204)]) (nAbstractObs (napps (NVar 106) [(napps (NVar 200)
  [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 201) [(NVar 0); (NVar 1); (NVar
  2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar
  103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar
  111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar
  119); (NVar 120); (NVar 121); (NVar 122)]); (napps (NVar 202) [(NVar 0); (NVar 1); (NVar 2); (NVar
  3); (NVar 4)]); (napps (NVar 203) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5);
  (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar
  106); (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar
  114); (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar
  122)]); (napps (NVar 204) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 205)
  [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar
  101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar
  109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar
  117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)]); (napps (NVar 300) [(NVar 0);
  (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101);
  (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109);
  (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117);
  (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)]); (napps (NVar 301) [(NVar 0); (NVar
  1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar
  102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109); (NVar
  110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117); (NVar
  118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)])])))))))))).
Definition nLaw_eq_transType : named :=
  (NPi 200 nDomain (NPi 201 (napps nAdmittedObservations [(NVar 200)]) (NPi 202 nDomain (NPi 203
  (napps nAdmittedObservations [(NVar 202)]) (NPi 204 nDomain (NPi 205 (napps nAdmittedObservations
  [(NVar 204)]) (NPi 300 (napps nEquality [(NVar 200); (NVar 202)]) (NPi 301 (napps nEquality [(NVar
  202); (NVar 204)]) (napps nEquality [(NVar 200); (NVar 204)]))))))))).
Definition Law_eq_trans : closed_term := close nLaw_eq_trans eq_refl.
Definition Law_eq_transType : closed_term := close nLaw_eq_transType eq_refl.

Definition nLaw_succ_congr : named :=
  (NLam 200 nDomain (NLam 201 (napps nAdmittedObservations [(NVar 200)]) (NLam 202 nDomain (NLam 203
  (napps nAdmittedObservations [(NVar 202)]) (NLam 300 (napps nEquality [(NVar 200); (NVar 202)])
  (nAbstractObs (napps (NVar 107) [(napps (NVar 200) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar
  4)]); (napps (NVar 201) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6);
  (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106);
  (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114);
  (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)]);
  (napps (NVar 202) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 203) [(NVar
  0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101);
  (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109);
  (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117);
  (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)]); (napps (NVar 300) [(NVar 0); (NVar
  1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar
  102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109); (NVar
  110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117); (NVar
  118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)])]))))))).
Definition nLaw_succ_congrType : named :=
  (NPi 200 nDomain (NPi 201 (napps nAdmittedObservations [(NVar 200)]) (NPi 202 nDomain (NPi 203
  (napps nAdmittedObservations [(NVar 202)]) (NPi 300 (napps nEquality [(NVar 200); (NVar 202)])
  (napps nEquality [(napps nSucc [(NVar 200)]); (napps nSucc [(NVar 202)])])))))).
Definition Law_succ_congr : closed_term := close nLaw_succ_congr eq_refl.
Definition Law_succ_congrType : closed_term := close nLaw_succ_congrType eq_refl.

Definition nLaw_add_congr : named :=
  (NLam 200 nDomain (NLam 201 (napps nAdmittedObservations [(NVar 200)]) (NLam 202 nDomain (NLam 203
  (napps nAdmittedObservations [(NVar 202)]) (NLam 204 nDomain (NLam 205 (napps
  nAdmittedObservations [(NVar 204)]) (NLam 206 nDomain (NLam 207 (napps nAdmittedObservations
  [(NVar 206)]) (NLam 300 (napps nEquality [(NVar 200); (NVar 202)]) (NLam 301 (napps nEquality
  [(NVar 204); (NVar 206)]) (nAbstractObs (napps (NVar 108) [(napps (NVar 200) [(NVar 0); (NVar 1);
  (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 201) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar
  4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar 103); (NVar 104);
  (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar 111); (NVar 112);
  (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar 119); (NVar 120);
  (NVar 121); (NVar 122)]); (napps (NVar 202) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]);
  (napps (NVar 203) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7);
  (NVar 100); (NVar 101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107);
  (NVar 108); (NVar 109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115);
  (NVar 116); (NVar 117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)]); (napps (NVar
  204) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 205) [(NVar 0); (NVar 1);
  (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar 102);
  (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109); (NVar 110);
  (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117); (NVar 118);
  (NVar 119); (NVar 120); (NVar 121); (NVar 122)]); (napps (NVar 206) [(NVar 0); (NVar 1); (NVar 2);
  (NVar 3); (NVar 4)]); (napps (NVar 207) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar
  5); (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar 103); (NVar 104); (NVar 105);
  (NVar 106); (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar 111); (NVar 112); (NVar 113);
  (NVar 114); (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar 119); (NVar 120); (NVar 121);
  (NVar 122)]); (napps (NVar 300) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar
  6); (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106);
  (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114);
  (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)]);
  (napps (NVar 301) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7);
  (NVar 100); (NVar 101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107);
  (NVar 108); (NVar 109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115);
  (NVar 116); (NVar 117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)])])))))))))))).
Definition nLaw_add_congrType : named :=
  (NPi 200 nDomain (NPi 201 (napps nAdmittedObservations [(NVar 200)]) (NPi 202 nDomain (NPi 203
  (napps nAdmittedObservations [(NVar 202)]) (NPi 204 nDomain (NPi 205 (napps nAdmittedObservations
  [(NVar 204)]) (NPi 206 nDomain (NPi 207 (napps nAdmittedObservations [(NVar 206)]) (NPi 300 (napps
  nEquality [(NVar 200); (NVar 202)]) (NPi 301 (napps nEquality [(NVar 204); (NVar 206)]) (napps
  nEquality [(napps nAdd [(NVar 200); (NVar 204)]); (napps nAdd [(NVar 202); (NVar
  206)])]))))))))))).
Definition Law_add_congr : closed_term := close nLaw_add_congr eq_refl.
Definition Law_add_congrType : closed_term := close nLaw_add_congrType eq_refl.

Definition nLaw_mul_congr : named :=
  (NLam 200 nDomain (NLam 201 (napps nAdmittedObservations [(NVar 200)]) (NLam 202 nDomain (NLam 203
  (napps nAdmittedObservations [(NVar 202)]) (NLam 204 nDomain (NLam 205 (napps
  nAdmittedObservations [(NVar 204)]) (NLam 206 nDomain (NLam 207 (napps nAdmittedObservations
  [(NVar 206)]) (NLam 300 (napps nEquality [(NVar 200); (NVar 202)]) (NLam 301 (napps nEquality
  [(NVar 204); (NVar 206)]) (nAbstractObs (napps (NVar 109) [(napps (NVar 200) [(NVar 0); (NVar 1);
  (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 201) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar
  4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar 103); (NVar 104);
  (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar 111); (NVar 112);
  (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar 119); (NVar 120);
  (NVar 121); (NVar 122)]); (napps (NVar 202) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]);
  (napps (NVar 203) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7);
  (NVar 100); (NVar 101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107);
  (NVar 108); (NVar 109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115);
  (NVar 116); (NVar 117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)]); (napps (NVar
  204) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 205) [(NVar 0); (NVar 1);
  (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar 102);
  (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109); (NVar 110);
  (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117); (NVar 118);
  (NVar 119); (NVar 120); (NVar 121); (NVar 122)]); (napps (NVar 206) [(NVar 0); (NVar 1); (NVar 2);
  (NVar 3); (NVar 4)]); (napps (NVar 207) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar
  5); (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar 103); (NVar 104); (NVar 105);
  (NVar 106); (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar 111); (NVar 112); (NVar 113);
  (NVar 114); (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar 119); (NVar 120); (NVar 121);
  (NVar 122)]); (napps (NVar 300) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar
  6); (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106);
  (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114);
  (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)]);
  (napps (NVar 301) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7);
  (NVar 100); (NVar 101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107);
  (NVar 108); (NVar 109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115);
  (NVar 116); (NVar 117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)])])))))))))))).
Definition nLaw_mul_congrType : named :=
  (NPi 200 nDomain (NPi 201 (napps nAdmittedObservations [(NVar 200)]) (NPi 202 nDomain (NPi 203
  (napps nAdmittedObservations [(NVar 202)]) (NPi 204 nDomain (NPi 205 (napps nAdmittedObservations
  [(NVar 204)]) (NPi 206 nDomain (NPi 207 (napps nAdmittedObservations [(NVar 206)]) (NPi 300 (napps
  nEquality [(NVar 200); (NVar 202)]) (NPi 301 (napps nEquality [(NVar 204); (NVar 206)]) (napps
  nEquality [(napps nMul [(NVar 200); (NVar 204)]); (napps nMul [(NVar 202); (NVar
  206)])]))))))))))).
Definition Law_mul_congr : closed_term := close nLaw_mul_congr eq_refl.
Definition Law_mul_congrType : closed_term := close nLaw_mul_congrType eq_refl.

Definition nLaw_order_congr : named :=
  (NLam 200 nDomain (NLam 201 (napps nAdmittedObservations [(NVar 200)]) (NLam 202 nDomain (NLam 203
  (napps nAdmittedObservations [(NVar 202)]) (NLam 204 nDomain (NLam 205 (napps
  nAdmittedObservations [(NVar 204)]) (NLam 206 nDomain (NLam 207 (napps nAdmittedObservations
  [(NVar 206)]) (NLam 300 (napps nEquality [(NVar 200); (NVar 202)]) (NLam 301 (napps nEquality
  [(NVar 204); (NVar 206)]) (NLam 302 (napps nOrder [(NVar 200); (NVar 204)]) (nAbstractObs (napps
  (NVar 110) [(napps (NVar 200) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar
  201) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100);
  (NVar 101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108);
  (NVar 109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116);
  (NVar 117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)]); (napps (NVar 202) [(NVar
  0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 203) [(NVar 0); (NVar 1); (NVar 2);
  (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar 103);
  (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar 111);
  (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar 119);
  (NVar 120); (NVar 121); (NVar 122)]); (napps (NVar 204) [(NVar 0); (NVar 1); (NVar 2); (NVar 3);
  (NVar 4)]); (napps (NVar 205) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar
  6); (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106);
  (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114);
  (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)]);
  (napps (NVar 206) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 207) [(NVar
  0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101);
  (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109);
  (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117);
  (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)]); (napps (NVar 300) [(NVar 0); (NVar
  1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar
  102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109); (NVar
  110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117); (NVar
  118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)]); (napps (NVar 301) [(NVar 0); (NVar 1);
  (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar 102);
  (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109); (NVar 110);
  (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117); (NVar 118);
  (NVar 119); (NVar 120); (NVar 121); (NVar 122)]); (napps (NVar 302) [(NVar 0); (NVar 1); (NVar 2);
  (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar 103);
  (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar 111);
  (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar 119);
  (NVar 120); (NVar 121); (NVar 122)])]))))))))))))).
Definition nLaw_order_congrType : named :=
  (NPi 200 nDomain (NPi 201 (napps nAdmittedObservations [(NVar 200)]) (NPi 202 nDomain (NPi 203
  (napps nAdmittedObservations [(NVar 202)]) (NPi 204 nDomain (NPi 205 (napps nAdmittedObservations
  [(NVar 204)]) (NPi 206 nDomain (NPi 207 (napps nAdmittedObservations [(NVar 206)]) (NPi 300 (napps
  nEquality [(NVar 200); (NVar 202)]) (NPi 301 (napps nEquality [(NVar 204); (NVar 206)]) (NPi 302
  (napps nOrder [(NVar 200); (NVar 204)]) (napps nOrder [(NVar 202); (NVar 206)])))))))))))).
Definition Law_order_congr : closed_term := close nLaw_order_congr eq_refl.
Definition Law_order_congrType : closed_term := close nLaw_order_congrType eq_refl.

Definition nLaw_order_refl : named :=
  (NLam 200 nDomain (NLam 201 (napps nAdmittedObservations [(NVar 200)]) (nAbstractObs (napps (NVar
  111) [(napps (NVar 200) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 201)
  [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar
  101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar
  109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar
  117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)])])))).
Definition nLaw_order_reflType : named :=
  (NPi 200 nDomain (NPi 201 (napps nAdmittedObservations [(NVar 200)]) (napps nOrder [(NVar 200);
  (NVar 200)]))).
Definition Law_order_refl : closed_term := close nLaw_order_refl eq_refl.
Definition Law_order_reflType : closed_term := close nLaw_order_reflType eq_refl.

Definition nLaw_order_trans : named :=
  (NLam 200 nDomain (NLam 201 (napps nAdmittedObservations [(NVar 200)]) (NLam 202 nDomain (NLam 203
  (napps nAdmittedObservations [(NVar 202)]) (NLam 204 nDomain (NLam 205 (napps
  nAdmittedObservations [(NVar 204)]) (NLam 300 (napps nOrder [(NVar 200); (NVar 202)]) (NLam 301
  (napps nOrder [(NVar 202); (NVar 204)]) (nAbstractObs (napps (NVar 112) [(napps (NVar 200) [(NVar
  0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 201) [(NVar 0); (NVar 1); (NVar 2);
  (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar 103);
  (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar 111);
  (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar 119);
  (NVar 120); (NVar 121); (NVar 122)]); (napps (NVar 202) [(NVar 0); (NVar 1); (NVar 2); (NVar 3);
  (NVar 4)]); (napps (NVar 203) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar
  6); (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106);
  (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114);
  (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)]);
  (napps (NVar 204) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 205) [(NVar
  0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101);
  (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109);
  (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117);
  (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)]); (napps (NVar 300) [(NVar 0); (NVar
  1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar
  102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109); (NVar
  110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117); (NVar
  118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)]); (napps (NVar 301) [(NVar 0); (NVar 1);
  (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar 102);
  (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109); (NVar 110);
  (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117); (NVar 118);
  (NVar 119); (NVar 120); (NVar 121); (NVar 122)])])))))))))).
Definition nLaw_order_transType : named :=
  (NPi 200 nDomain (NPi 201 (napps nAdmittedObservations [(NVar 200)]) (NPi 202 nDomain (NPi 203
  (napps nAdmittedObservations [(NVar 202)]) (NPi 204 nDomain (NPi 205 (napps nAdmittedObservations
  [(NVar 204)]) (NPi 300 (napps nOrder [(NVar 200); (NVar 202)]) (NPi 301 (napps nOrder [(NVar 202);
  (NVar 204)]) (napps nOrder [(NVar 200); (NVar 204)]))))))))).
Definition Law_order_trans : closed_term := close nLaw_order_trans eq_refl.
Definition Law_order_transType : closed_term := close nLaw_order_transType eq_refl.

Definition nLaw_add_zero : named :=
  (NLam 200 nDomain (NLam 201 (napps nAdmittedObservations [(NVar 200)]) (nAbstractObs (napps (NVar
  113) [(napps (NVar 200) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 201)
  [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar
  101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar
  109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar
  117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)])])))).
Definition nLaw_add_zeroType : named :=
  (NPi 200 nDomain (NPi 201 (napps nAdmittedObservations [(NVar 200)]) (napps nEquality [(napps nAdd
  [nZero; (NVar 200)]); (NVar 200)]))).
Definition Law_add_zero : closed_term := close nLaw_add_zero eq_refl.
Definition Law_add_zeroType : closed_term := close nLaw_add_zeroType eq_refl.

Definition nLaw_add_succ : named :=
  (NLam 200 nDomain (NLam 201 (napps nAdmittedObservations [(NVar 200)]) (NLam 202 nDomain (NLam 203
  (napps nAdmittedObservations [(NVar 202)]) (nAbstractObs (napps (NVar 114) [(napps (NVar 200)
  [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 201) [(NVar 0); (NVar 1); (NVar
  2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar
  103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar
  111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar
  119); (NVar 120); (NVar 121); (NVar 122)]); (napps (NVar 202) [(NVar 0); (NVar 1); (NVar 2); (NVar
  3); (NVar 4)]); (napps (NVar 203) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5);
  (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar
  106); (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar
  114); (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar
  122)])])))))).
Definition nLaw_add_succType : named :=
  (NPi 200 nDomain (NPi 201 (napps nAdmittedObservations [(NVar 200)]) (NPi 202 nDomain (NPi 203
  (napps nAdmittedObservations [(NVar 202)]) (napps nEquality [(napps nAdd [(napps nSucc [(NVar
  200)]); (NVar 202)]); (napps nSucc [(napps nAdd [(NVar 200); (NVar 202)])])]))))).
Definition Law_add_succ : closed_term := close nLaw_add_succ eq_refl.
Definition Law_add_succType : closed_term := close nLaw_add_succType eq_refl.

Definition nLaw_mul_zero : named :=
  (NLam 200 nDomain (NLam 201 (napps nAdmittedObservations [(NVar 200)]) (nAbstractObs (napps (NVar
  115) [(napps (NVar 200) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 201)
  [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar
  101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar
  109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar
  117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)])])))).
Definition nLaw_mul_zeroType : named :=
  (NPi 200 nDomain (NPi 201 (napps nAdmittedObservations [(NVar 200)]) (napps nEquality [(napps nMul
  [nZero; (NVar 200)]); nZero]))).
Definition Law_mul_zero : closed_term := close nLaw_mul_zero eq_refl.
Definition Law_mul_zeroType : closed_term := close nLaw_mul_zeroType eq_refl.

Definition nLaw_mul_succ : named :=
  (NLam 200 nDomain (NLam 201 (napps nAdmittedObservations [(NVar 200)]) (NLam 202 nDomain (NLam 203
  (napps nAdmittedObservations [(NVar 202)]) (nAbstractObs (napps (NVar 116) [(napps (NVar 200)
  [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 201) [(NVar 0); (NVar 1); (NVar
  2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar
  103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar
  111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar
  119); (NVar 120); (NVar 121); (NVar 122)]); (napps (NVar 202) [(NVar 0); (NVar 1); (NVar 2); (NVar
  3); (NVar 4)]); (napps (NVar 203) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5);
  (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar
  106); (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar
  114); (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar
  122)])])))))).
Definition nLaw_mul_succType : named :=
  (NPi 200 nDomain (NPi 201 (napps nAdmittedObservations [(NVar 200)]) (NPi 202 nDomain (NPi 203
  (napps nAdmittedObservations [(NVar 202)]) (napps nEquality [(napps nMul [(napps nSucc [(NVar
  200)]); (NVar 202)]); (napps nAdd [(NVar 202); (napps nMul [(NVar 200); (NVar 202)])])]))))).
Definition Law_mul_succ : closed_term := close nLaw_mul_succ eq_refl.
Definition Law_mul_succType : closed_term := close nLaw_mul_succType eq_refl.

Definition nLaw_mul_zero_right : named :=
  (NLam 200 nDomain (NLam 201 (napps nAdmittedObservations [(NVar 200)]) (nAbstractObs (napps (NVar
  117) [(napps (NVar 200) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 201)
  [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar
  101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar
  109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar
  117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)])])))).
Definition nLaw_mul_zero_rightType : named :=
  (NPi 200 nDomain (NPi 201 (napps nAdmittedObservations [(NVar 200)]) (napps nEquality [(napps nMul
  [(NVar 200); nZero]); nZero]))).
Definition Law_mul_zero_right : closed_term := close nLaw_mul_zero_right eq_refl.
Definition Law_mul_zero_rightType : closed_term := close nLaw_mul_zero_rightType eq_refl.

Definition nLaw_le_succ : named :=
  (NLam 200 nDomain (NLam 201 (napps nAdmittedObservations [(NVar 200)]) (nAbstractObs (napps (NVar
  118) [(napps (NVar 200) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 201)
  [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar
  101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar
  109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar
  117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)])])))).
Definition nLaw_le_succType : named :=
  (NPi 200 nDomain (NPi 201 (napps nAdmittedObservations [(NVar 200)]) (napps nOrder [(NVar 200);
  (napps nSucc [(NVar 200)])]))).
Definition Law_le_succ : closed_term := close nLaw_le_succ eq_refl.
Definition Law_le_succType : closed_term := close nLaw_le_succType eq_refl.

Definition nLaw_le_add_left : named :=
  (NLam 200 nDomain (NLam 201 (napps nAdmittedObservations [(NVar 200)]) (NLam 202 nDomain (NLam 203
  (napps nAdmittedObservations [(NVar 202)]) (nAbstractObs (napps (NVar 119) [(napps (NVar 200)
  [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 201) [(NVar 0); (NVar 1); (NVar
  2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar
  103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar
  111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar
  119); (NVar 120); (NVar 121); (NVar 122)]); (napps (NVar 202) [(NVar 0); (NVar 1); (NVar 2); (NVar
  3); (NVar 4)]); (napps (NVar 203) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5);
  (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar
  106); (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar
  114); (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar
  122)])])))))).
Definition nLaw_le_add_leftType : named :=
  (NPi 200 nDomain (NPi 201 (napps nAdmittedObservations [(NVar 200)]) (NPi 202 nDomain (NPi 203
  (napps nAdmittedObservations [(NVar 202)]) (napps nOrder [(NVar 200); (napps nAdd [(NVar 200);
  (NVar 202)])]))))).
Definition Law_le_add_left : closed_term := close nLaw_le_add_left eq_refl.
Definition Law_le_add_leftType : closed_term := close nLaw_le_add_leftType eq_refl.

Definition nLaw_le_add_right : named :=
  (NLam 200 nDomain (NLam 201 (napps nAdmittedObservations [(NVar 200)]) (NLam 202 nDomain (NLam 203
  (napps nAdmittedObservations [(NVar 202)]) (nAbstractObs (napps (NVar 120) [(napps (NVar 200)
  [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 201) [(NVar 0); (NVar 1); (NVar
  2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar
  103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar
  111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar
  119); (NVar 120); (NVar 121); (NVar 122)]); (napps (NVar 202) [(NVar 0); (NVar 1); (NVar 2); (NVar
  3); (NVar 4)]); (napps (NVar 203) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5);
  (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar
  106); (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar
  114); (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar
  122)])])))))).
Definition nLaw_le_add_rightType : named :=
  (NPi 200 nDomain (NPi 201 (napps nAdmittedObservations [(NVar 200)]) (NPi 202 nDomain (NPi 203
  (napps nAdmittedObservations [(NVar 202)]) (napps nOrder [(NVar 202); (napps nAdd [(NVar 200);
  (NVar 202)])]))))).
Definition Law_le_add_right : closed_term := close nLaw_le_add_right eq_refl.
Definition Law_le_add_rightType : closed_term := close nLaw_le_add_rightType eq_refl.

Definition nLaw_le_mul_left : named :=
  (NLam 200 nDomain (NLam 201 (napps nAdmittedObservations [(NVar 200)]) (NLam 202 nDomain (NLam 203
  (napps nAdmittedObservations [(NVar 202)]) (NLam 300 (napps nOrder [(napps nSucc [nZero]); (NVar
  202)]) (nAbstractObs (napps (NVar 121) [(napps (NVar 200) [(NVar 0); (NVar 1); (NVar 2); (NVar 3);
  (NVar 4)]); (napps (NVar 201) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar
  6); (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106);
  (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114);
  (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)]);
  (napps (NVar 202) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 203) [(NVar
  0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101);
  (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109);
  (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117);
  (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)]); (napps (NVar 300) [(NVar 0); (NVar
  1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar
  102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109); (NVar
  110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117); (NVar
  118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)])]))))))).
Definition nLaw_le_mul_leftType : named :=
  (NPi 200 nDomain (NPi 201 (napps nAdmittedObservations [(NVar 200)]) (NPi 202 nDomain (NPi 203
  (napps nAdmittedObservations [(NVar 202)]) (NPi 300 (napps nOrder [(napps nSucc [nZero]); (NVar
  202)]) (napps nOrder [(NVar 200); (napps nMul [(NVar 200); (NVar 202)])])))))).
Definition Law_le_mul_left : closed_term := close nLaw_le_mul_left eq_refl.
Definition Law_le_mul_leftType : closed_term := close nLaw_le_mul_leftType eq_refl.

Definition nLaw_le_mul_right : named :=
  (NLam 200 nDomain (NLam 201 (napps nAdmittedObservations [(NVar 200)]) (NLam 202 nDomain (NLam 203
  (napps nAdmittedObservations [(NVar 202)]) (NLam 300 (napps nOrder [(napps nSucc [nZero]); (NVar
  200)]) (nAbstractObs (napps (NVar 122) [(napps (NVar 200) [(NVar 0); (NVar 1); (NVar 2); (NVar 3);
  (NVar 4)]); (napps (NVar 201) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar
  6); (NVar 7); (NVar 100); (NVar 101); (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106);
  (NVar 107); (NVar 108); (NVar 109); (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114);
  (NVar 115); (NVar 116); (NVar 117); (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)]);
  (napps (NVar 202) [(NVar 0); (NVar 1); (NVar 2); (NVar 3); (NVar 4)]); (napps (NVar 203) [(NVar
  0); (NVar 1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101);
  (NVar 102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109);
  (NVar 110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117);
  (NVar 118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)]); (napps (NVar 300) [(NVar 0); (NVar
  1); (NVar 2); (NVar 3); (NVar 4); (NVar 5); (NVar 6); (NVar 7); (NVar 100); (NVar 101); (NVar
  102); (NVar 103); (NVar 104); (NVar 105); (NVar 106); (NVar 107); (NVar 108); (NVar 109); (NVar
  110); (NVar 111); (NVar 112); (NVar 113); (NVar 114); (NVar 115); (NVar 116); (NVar 117); (NVar
  118); (NVar 119); (NVar 120); (NVar 121); (NVar 122)])]))))))).
Definition nLaw_le_mul_rightType : named :=
  (NPi 200 nDomain (NPi 201 (napps nAdmittedObservations [(NVar 200)]) (NPi 202 nDomain (NPi 203
  (napps nAdmittedObservations [(NVar 202)]) (NPi 300 (napps nOrder [(napps nSucc [nZero]); (NVar
  200)]) (napps nOrder [(NVar 202); (napps nMul [(NVar 200); (NVar 202)])])))))).
Definition Law_le_mul_right : closed_term := close nLaw_le_mul_right eq_refl.
Definition Law_le_mul_rightType : closed_term := close nLaw_le_mul_rightType eq_refl.

End Codes.
