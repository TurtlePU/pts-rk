From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import Syntax Context Typing Ranks Reduction AbstractRewriting.

(** Closed original terms for four numerical families.  The implicit ambient
    scope permits their direct use in open contexts; none has a free variable.
    All type and family parameters below are ordinary PTS arguments. *)
Module Core.

Local Abbreviation v0 := (var fzero).
Local Abbreviation v1 := (var (fsucc fzero)).
Local Abbreviation v2 := (var (fsucc (fsucc fzero))).
Local Abbreviation v3 := (var (fsucc (fsucc (fsucc fzero)))).
Local Abbreviation v4 := (var (fsucc (fsucc (fsucc (fsucc fzero))))).

Definition identity {n} (a : nat) : Term nat n :=
  lam (𝓤 a) (lam v0 v0).
Definition identity_type {n} (a : nat) : Term nat n :=
  Π (𝓤 a) (Π v0 v1).

(** The ordinary K has an independent second type parameter. *)
Definition constant_simple {n} (a b : nat) : Term nat n :=
  lam (𝓤 a) (lam (𝓤 b) (lam v1 (lam v1 v1))).
Definition constant_simple_type {n} (a b : nat) : Term nat n :=
  Π (𝓤 a) (Π (𝓤 b) (Π v1 (Π v1 v3))).

(** K A B x y = x, where B : Pi x:A. U_b. *)
Definition constant {n} (a b : nat) : Term nat n :=
  lam (𝓤 a) (lam (Π v0 (𝓤 b)) (lam v1 (lam (v1 $ v0) v1))).
Definition constant_type {n} (a b : nat) : Term nat n :=
  Π (𝓤 a) (Π (Π v0 (𝓤 b)) (Π v1 (Π (v1 $ v0) v3))).

(** S A B C f g x = f x (g x), with dependent B and C. *)
Definition substitution {n} (a b c : nat) : Term nat n :=
  lam (𝓤 a)
    (lam (Π v0 (𝓤 b))
      (lam (Π v1 (Π (v1 $ v0) (𝓤 c)))
        (lam (Π v2 (Π (v2 $ v0) (v2 $ v1 $ v0)))
          (lam (Π v3 (v3 $ v0))
            (lam v4 (v2 $ v0 $ (v1 $ v0))))))).
Definition substitution_type {n} (a b c : nat) : Term nat n :=
  Π (𝓤 a)
    (Π (Π v0 (𝓤 b))
      (Π (Π v1 (Π (v1 $ v0) (𝓤 c)))
        (Π (Π v2 (Π (v2 $ v0) (v2 $ v1 $ v0)))
          (Π (Π v3 (v3 $ v0))
            (Π v4 (v3 $ v0 $ (v1 $ v0))))))).

(** P A B = Pi x:A. B x. *)
Definition product {n} (a b : nat) : Term nat n :=
  lam (𝓤 a) (lam (Π v0 (𝓤 b)) (Π v1 (v1 $ v0))).
Definition product_type {n} (a b : nat) : Term nat n :=
  Π (𝓤 a) (Π (Π v0 (𝓤 b)) (𝓤 (Nat.max (S a) b))).

(** This local proof-producing tactic only composes the ORIGINAL typ
    constructors.  It neither defines a checker judgment nor changes the
    statement of any typing theorem. *)
Local Ltac infer_original G t :=
  lazymatch t with
  | 𝓤 ?a => constr:(@typ_𝓤 nat RankSorts _ G a 0 eq_refl)
  | var ?i => constr:(@typ_var nat RankSorts _ G i)
  | Π ?A ?B =>
      let pA := infer_original G A in
      let pB := infer_original (G & A) B in
      let TA := type of pA in let TA := eval cbn - [Nat.max] in TA in
      let TB := type of pB in let TB := eval cbn - [Nat.max] in TB in
      lazymatch TA with
      | @typ _ _ _ _ _ (𝓤 ?a) =>
          lazymatch TB with
          | @typ _ _ _ _ _ (𝓤 ?b) =>
              constr:(@typ_Π nat RankSorts _ G A B a b
                (Nat.max (S a) b) pA pB eq_refl)
          end
      end
  | lam ?A ?b =>
      let pA := infer_original G A in
      let pb := infer_original (G & A) b in
      let TA := type of pA in let TA := eval cbn - [Nat.max] in TA in
      lazymatch TA with
      | @typ _ _ _ _ _ (𝓤 ?a) =>
          constr:(@typ_λ nat RankSorts _ G A b _ a pA pb)
      end
  | app ?f ?x =>
      let pf := infer_original G f in
      let px := infer_original G x in
      let Tf := type of pf in let Tf := eval cbn - [Nat.max] in Tf in
      lazymatch Tf with
      | @typ _ _ _ _ _ (Π ?A ?B) =>
          constr:(@typ_app nat RankSorts _ G f B x A pf px)
      end
  end.

Local Ltac original_typing :=
  lazymatch goal with
  | |- @typ _ _ _ ?G ?t _ =>
      let t := eval cbv beta delta [identity identity_type constant constant_type
        constant_simple constant_simple_type
        substitution substitution_type product product_type] in t in
      let p := infer_original G t in exact p
  end.

Theorem identity_typed {n} (G : Ctx nat n) a :
  @typ nat RankSorts n G (identity a) (identity_type a).
Proof. original_typing. Qed.

Theorem constant_typed {n} (G : Ctx nat n) a b :
  @typ nat RankSorts n G (constant a b) (constant_type a b).
Proof. original_typing. Qed.

Theorem constant_simple_typed {n} (G : Ctx nat n) a b :
  @typ nat RankSorts n G (constant_simple a b) (constant_simple_type a b).
Proof. original_typing. Qed.

Theorem substitution_typed {n} (G : Ctx nat n) a b c :
  @typ nat RankSorts n G (substitution a b c) (substitution_type a b c).
Proof. original_typing. Qed.

Theorem product_typed {n} (G : Ctx nat n) a b :
  @typ nat RankSorts n G (product a b) (product_type a b).
Proof. original_typing. Qed.

(** Exact sorts of the declared types, without cumulativity. *)
Local Ltac original_sort :=
  lazymatch goal with
  | |- @typ _ _ _ ?G ?t (𝓤 ?r) =>
      let t := eval cbv beta delta [identity_type constant_type
        constant_simple_type substitution_type product_type] in t in
      let p := infer_original G t in
      let T := type of p in
      lazymatch T with
      | @typ _ _ _ _ _ (𝓤 ?s) =>
          replace r with s by lia; exact p
      end
  end.

Theorem identity_type_sorted {n} (G : Ctx nat n) a :
  @typ nat RankSorts n G (identity_type a) (𝓤 (S a)).
Proof. original_sort. Qed.

Theorem constant_simple_type_sorted {n} (G : Ctx nat n) a b :
  @typ nat RankSorts n G (constant_simple_type a b)
    (𝓤 (Nat.max (S a) (S b))).
Proof. original_sort. Qed.

Theorem constant_type_sorted {n} (G : Ctx nat n) a b :
  @typ nat RankSorts n G (constant_type a b)
    (𝓤 (Nat.max (S (S a)) (S b))).
Proof. original_sort. Qed.

Theorem substitution_type_sorted {n} (G : Ctx nat n) a b c :
  @typ nat RankSorts n G (substitution_type a b c)
    (𝓤 (Nat.max (S (S a)) (Nat.max (S (S b)) (S c)))).
Proof. original_sort. Qed.

Theorem product_type_sorted {n} (G : Ctx nat n) a b :
  @typ nat RankSorts n G (product_type a b) (𝓤 (S (S a))).
Proof. original_sort. Qed.

(** Literal beta computation, with no eta conversion and no typing premises. *)
Local Ltac head_beta :=
  first [apply step_beta | apply step_app_left; head_beta].
Local Ltac compute_head :=
  eapply rtc_step; [head_beta | cbn; unfold shift, subst; cbn;
    autorewrite with syntax].

Theorem identity_beta {n} a (A x : Term nat n) :
  identity a $ A $ x ↠ᵝ x.
Proof. unfold identity. do 2 compute_head. reflexivity. Qed.

Theorem constant_simple_beta {n} a b (A B x y : Term nat n) :
  constant_simple a b $ A $ B $ x $ y ↠ᵝ x.
Proof. unfold constant_simple. do 4 compute_head. reflexivity. Qed.

Theorem constant_beta {n} a b (A B x y : Term nat n) :
  constant a b $ A $ B $ x $ y ↠ᵝ x.
Proof. unfold constant. do 4 compute_head. reflexivity. Qed.

Theorem substitution_beta {n} a b c (A B C f g x : Term nat n) :
  substitution a b c $ A $ B $ C $ f $ g $ x ↠ᵝ f $ x $ (g $ x).
Proof. unfold substitution. do 6 compute_head. reflexivity. Qed.

Theorem product_beta {n} a b (A B : Term nat n) :
  product a b $ A $ B ↠ᵝ Π A (shift B $ v0).
Proof. unfold product. do 2 compute_head. reflexivity. Qed.

Print Assumptions identity_typed.
Print Assumptions constant_typed.
Print Assumptions constant_simple_typed.
Print Assumptions substitution_typed.
Print Assumptions product_typed.
Print Assumptions identity_type_sorted.
Print Assumptions constant_simple_type_sorted.
Print Assumptions constant_type_sorted.
Print Assumptions substitution_type_sorted.
Print Assumptions product_type_sorted.
Print Assumptions identity_beta.
Print Assumptions constant_simple_beta.
Print Assumptions constant_beta.
Print Assumptions substitution_beta.
Print Assumptions product_beta.

End Core.
