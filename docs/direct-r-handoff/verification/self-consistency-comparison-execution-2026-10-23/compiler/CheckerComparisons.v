(** A comparison-preserving compilation of the ORIGINAL native checkers.
    No whole-checker answer is tabulated: every syntactic comparison retains
    both complete raw operands.  Parsing, endpoint extraction, substitution
    and context lookup are still performed by this EXTERNAL compiler.
    The Boolean expression evaluator and its comparison leaves are separate
    components for subsequent original-PTS realization. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context.
From PTSrk.SelfConsistency Require Import NativeProofCodes StructuralCodes
  CertificateSerialization InternalCarrier.

Module CheckerComparisons.
Module NC := NativeProofCodes.NativeProofCodes.
Module IC := InternalCarrier.InternalCarrier.

Definition tag_eqb (x y : tag) := Nat.eqb (IC.tag_number x) (IC.tag_number y).
Lemma tag_eqb_correct x y : tag_eqb x y = true <-> x = y.
Proof.
  unfold tag_eqb; rewrite Nat.eqb_eq; split.
  - intro H; rewrite <- (IC.tag_number_roundtrip x),
      <- (IC.tag_number_roundtrip y), H; reflexivity.
  - intros <-; reflexivity.
Qed.

Fixpoint code_eqb (x y : code) : bool :=
  match x, y with
  | Atom a, Atom b => tag_eqb a b
  | Pair a b, Pair c d => code_eqb a c && code_eqb b d
  | _, _ => false
  end.
Theorem code_eqb_correct x y : code_eqb x y = true <-> x = y.
Proof.
  revert y; induction x as [a|a IHa b IHb]; intros [c|c d]; cbn [code_eqb].
  - rewrite tag_eqb_correct; split; intro H; [now subst | now injection H].
  - split; discriminate.
  - split; discriminate.
  - rewrite andb_true_iff, IHa, IHb; split.
    + intros [-> ->]; reflexivity.
    + intro H; injection H; auto.
Qed.
Theorem code_eqb_false x y : code_eqb x y = false <-> x <> y.
Proof.
  rewrite <- Bool.not_true_iff_false, code_eqb_correct; reflexivity.
Qed.
Theorem code_eqb_reflexive x : code_eqb x x = true.
Proof. apply code_eqb_correct; reflexivity. Qed.
Theorem code_eqb_encoded_terms {n} (t u : Term nat n) :
  code_eqb (encode_term t) (encode_term u) = NC.term_eqb t u.
Proof.
  apply Bool.eq_true_iff_eq; rewrite code_eqb_correct, NC.term_eqb_correct.
  split; [apply encode_term_injective | intros ->; reflexivity].
Qed.

Inductive Expr : Type :=
| Truth : bool -> Expr
| Compare : code -> code -> Expr
| Both : Expr -> Expr -> Expr.

Fixpoint eval (e : Expr) : bool :=
  match e with
  | Truth b => b
  | Compare x y => code_eqb x y
  | Both a b => eval a && eval b
  end.

Definition matches_expression {n} (p : NC.Certificate n) (t A : Term nat n) :=
  Both (Compare (encode_term (NC.subject p)) (encode_term t))
    (Compare (encode_term (NC.type p)) (encode_term A)).
Theorem eval_matches_expression {n} (p : NC.Certificate n) t A :
  eval (matches_expression p t A) = NC.matchesb p t A.
Proof. unfold matches_expression, NC.matchesb; cbn [eval].
  rewrite !code_eqb_encoded_terms; reflexivity. Qed.

Fixpoint equality_expression {n} (p : NC.EqualityCode n) : Expr :=
  match p with
  | NC.Refl _ | NC.Reduce _ => Truth true
  | NC.Symmetry p => equality_expression p
  | NC.Transitivity p q => Both (Both (equality_expression p) (equality_expression q))
      (Compare (encode_term (NC.equality_target p)) (encode_term (NC.equality_source q)))
  end.
Theorem eval_equality_expression {n} (p : NC.EqualityCode n) :
  eval (equality_expression p) = NC.equality_check p.
Proof.
  induction p; cbn [equality_expression eval NC.equality_check];
    rewrite ?IHp, ?IHp1, ?IHp2, ?code_eqb_encoded_terms; reflexivity.
Qed.

Fixpoint check_expression {n} (G : Ctx nat n) (p : NC.Certificate n) : Expr :=
  match p in NC.Certificate k return Ctx nat k -> Expr with
  | NC.SortRule _ => fun _ => Truth true
  | NC.VariableRule i A => fun G =>
      Compare (encode_term (G !! i)) (encode_term A)
  | NC.ProductRule A B a b p q => fun G =>
      Both (Both (Both (check_expression G p) (check_expression (G & A) q))
        (matches_expression p A (𝓤 a))) (matches_expression q B (𝓤 b))
  | NC.AbstractionRule A t B r p q => fun G =>
      Both (Both (Both (check_expression G p) (check_expression (G & A) q))
        (matches_expression p A (𝓤 r))) (matches_expression q t B)
  | NC.ApplicationRule f u A B p q => fun G =>
      Both (Both (Both (check_expression G p) (check_expression G q))
        (matches_expression p f (Π A B))) (matches_expression q u A)
  | NC.ConversionRule t A B r p q e => fun G =>
      Both (Both (Both (Both (Both (Both (check_expression G p) (check_expression G q))
        (matches_expression p t A)) (matches_expression q B (𝓤 r)))
        (equality_expression e))
        (Compare (encode_term (NC.equality_source e)) (encode_term A)))
        (Compare (encode_term (NC.equality_target e)) (encode_term B))
  end G.
Theorem eval_check_expression {n} (G : Ctx nat n) (p : NC.Certificate n) :
  eval (check_expression G p) = NC.check G p.
Proof.
  revert G; induction p; intro G; cbn [check_expression eval NC.check];
    rewrite ?IHp1, ?IHp2, ?eval_matches_expression, ?eval_equality_expression,
      ?code_eqb_encoded_terms; reflexivity.
Qed.

Fixpoint context_expression {n} (c : NC.ContextCode n) : Expr :=
  match c with
  | NC.EmptyContext => Truth true
  | @NC.ExtendContext k c r p =>
      Both (Both (context_expression c) (check_expression (NC.context c) p))
        (Compare (encode_term (NC.type p)) (encode_term (@𝓤 nat k r)))
  end.
Theorem eval_context_expression {n} (c : NC.ContextCode n) :
  eval (context_expression c) = NC.context_check c.
Proof.
  induction c; cbn [context_expression eval NC.context_check];
    rewrite ?IHc, ?eval_check_expression, ?code_eqb_encoded_terms; reflexivity.
Qed.

Definition raw_check_expression q :=
  match decode_input q with
  | Some (existT _ n (c,p)) =>
      Both (context_expression c) (check_expression (NC.context c) p)
  | None => Truth false
  end.
Definition raw_bottom_expression q :=
  match decode_certificate q 0 with
  | Some p => Both (check_expression ε p)
      (Compare (encode_term (NC.type p)) (encode_term NC.Bottom))
  | None => Truth false
  end.

Theorem eval_raw_check_expression q : eval (raw_check_expression q) = raw_check q.
Proof.
  unfold raw_check_expression, raw_check.
  destruct (decode_input q) as [[n [c p]]|]; cbn [eval]; [|reflexivity].
  rewrite eval_context_expression, eval_check_expression; reflexivity.
Qed.
Theorem eval_raw_bottom_expression q :
  eval (raw_bottom_expression q) = raw_bottom_check q.
Proof.
  unfold raw_bottom_expression, raw_bottom_check.
  destruct (decode_certificate q 0) as [p|]; cbn [eval]; [|reflexivity].
  rewrite eval_check_expression, code_eqb_encoded_terms; reflexivity.
Qed.

Theorem malformed_input_expression q : decode_input q = None ->
  raw_check_expression q = Truth false.
Proof. intro H; unfold raw_check_expression; rewrite H; reflexivity. Qed.
Theorem malformed_bottom_expression q : decode_certificate q 0 = None ->
  raw_bottom_expression q = Truth false.
Proof. intro H; unfold raw_bottom_expression; rewrite H; reflexivity. Qed.

(** These count expression constructors, treating a comparison as one node.
    They do not measure operand size or bound compilation/evaluation time. *)
Fixpoint comparison_count e :=
  match e with Truth _ => 0 | Compare _ _ => 1 |
    Both a b => comparison_count a + comparison_count b end.
Fixpoint expression_size e :=
  match e with Truth _ | Compare _ _ => 1 |
    Both a b => S (expression_size a + expression_size b) end.
Theorem comparison_count_bound e : comparison_count e < expression_size e + 1.
Proof. induction e; cbn; lia. Qed.

(** Output-neutral examples: the general checker has both outcomes.  The
    rejected application is scoped but ill-typed; rejection is not merely
    the parser's malformed-input default. *)
Definition bad_application : NC.Certificate 0 :=
  NC.ApplicationRule (𝓤 0) (𝓤 0) (𝓤 0) (𝓤 0)
    (NC.SortRule 0) (NC.SortRule 0).
Example accepted_input : eval (raw_check_expression
  (encode_input NC.EmptyContext (NC.SortRule 0))) = true.
Proof. reflexivity. Qed.
Example rejected_scoped_input : eval (raw_check_expression
  (encode_input NC.EmptyContext bad_application)) = false.
Proof. reflexivity. Qed.
Example malformed_input : eval (raw_check_expression (Atom NZero)) = false.
Proof. reflexivity. Qed.
Example rejected_bottom_input : eval (raw_bottom_expression
  (encode_certificate (NC.SortRule 0 : NC.Certificate 0))) = false.
Proof. reflexivity. Qed.

End CheckerComparisons.
