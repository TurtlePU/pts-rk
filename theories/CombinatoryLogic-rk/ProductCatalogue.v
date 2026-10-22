From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import Syntax Context Typing Ranks Reduction Congruence
  AbstractRewriting.
From PTSrk.Combinatory Require Import Core Presentation.

(** The eleven product schemes displayed after Definition 7.3 in
    Bunder--Dekkers, LMCS 4(1:1), 2008, specialized to RankSorts.  All scheme
    parameters are NUMBERS; the original typing judgment is never an
    admission condition.  This is the product subcatalogue, not the full
    65-shape Hilbert catalogue and not a completeness theorem. *)
Module ProductCatalogue.

Local Abbreviation v0 := (var fzero).
Local Abbreviation v1 := (var (fsucc fzero)).

Inductive Scheme : Type :=
| P1 (a b : nat)
| P2 (a b c : nat)
| P3 (a b c : nat)
| P4 (a c : nat)
| P5 (a c : nat)
| P6 (a b : nat)
| P7 (a b c : nat)
| P8 (a b c : nat)
| P9 (a b c : nat)
| P10 (a b c : nat)
| P11 (a b c : nat).

Definition subject {n} (s : Scheme) : Term nat n :=
  match s with
  | P1 a b => Core.product a b
  | P2 a b c => Π (𝓤 a) (Π (Π v0 (𝓤 b)) (𝓤 c))
  | P3 a b c => lam (𝓤 a) (Π (Π v0 (𝓤 b)) (𝓤 c))
  | P4 a c => lam (𝓤 a) (𝓤 c)
  | P5 a c => Π (𝓤 a) (𝓤 c)
  | P6 a b => lam (𝓤 a) (lam (Π v0 (𝓤 b)) (lam v1 (v1 $ v0)))
  | P7 a b c => Π (𝓤 a) (Π (Π v0 (𝓤 b)) (Π v1 (𝓤 c)))
  | P8 a b c => lam (𝓤 a) (lam (Π v0 (𝓤 b)) (𝓤 c))
  | P9 a b c => lam (𝓤 a) (Π (Π v0 (𝓤 b)) (Π v1 (𝓤 c)))
  | P10 a b c => lam (𝓤 a) (lam (Π v0 (𝓤 b)) (Π v1 (𝓤 c)))
  | P11 a b c => lam (𝓤 a) (lam (Π v0 (𝓤 b)) (lam v1 (𝓤 c)))
  end.

Definition declared_type {n} (s : Scheme) : Term nat n :=
  match s with
  | P1 a b => Core.product_type a b
  | P2 a _ _ => 𝓤 (S (S a))
  | P3 a _ _ => Π (𝓤 a) (𝓤 (S (S a)))
  | P4 a _ => Π (𝓤 a) (𝓤 0)
  | P5 _ _ => 𝓤 1
  | P6 a b => Π (𝓤 a) (Π (Π v0 (𝓤 b)) (Π v1 (𝓤 b)))
  | P7 a _ _ => 𝓤 (S (S a))
  | P8 a b _ => Π (𝓤 a) (Π (Π v0 (𝓤 b)) (𝓤 0))
  | P9 a _ _ => Π (𝓤 a) (𝓤 (S (S a)))
  | P10 a b _ => Π (𝓤 a) (Π (Π v0 (𝓤 b)) (𝓤 (S a)))
  | P11 a b _ => Π (𝓤 a) (Π (Π v0 (𝓤 b)) (Π v1 (𝓤 0)))
  end.

Definition type_rank (s : Scheme) : nat :=
  match s with
  | P1 a _ | P6 a _ | P8 a _ _ | P10 a _ _ | P11 a _ _ => S (S a)
  | P2 _ _ _ | P5 _ _ | P7 _ _ _ => 0
  | P3 _ _ _ | P4 _ _ | P9 _ _ _ => 1
  end.

(** A proof-producing tactic composing only original typing constructors. *)
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
      let t := eval cbv beta delta [subject Core.product] in t in
      let p := infer_original G t in
      first [exact p |
        let H := fresh "Htyping" in pose proof p as H;
        cbn - [Nat.max] in H;
        repeat first [rewrite Nat.max_0_r in H | rewrite Nat.max_id in H |
          rewrite Nat.max_l in H by lia | rewrite Nat.max_r in H by lia];
        exact H]
  end.

Theorem scheme_typed {n} (G : Ctx nat n) s :
  @typ nat RankSorts n G (subject s) (declared_type s).
Proof.
  destruct s; cbn [subject declared_type]; original_typing.
Qed.

Theorem scheme_type_sorted {n} (G : Ctx nat n) s :
  @typ nat RankSorts n G (declared_type s) (𝓤 (type_rank s)).
Proof.
  destruct s; cbn [declared_type type_rank];
  lazymatch goal with
  | |- @typ _ _ _ ?G ?t (𝓤 ?r) =>
      let t := eval cbv beta delta [Core.product_type] in t in
      let p := infer_original G t in
      let T := type of p in
      lazymatch T with
      | @typ _ _ _ _ _ (𝓤 ?q) => replace r with q by lia; exact p
      end
  end.
Qed.

(** Every declared type is itself a catalogue subject or a universe atom.
    This is a literal syntax theorem, providing the product part of the
    Hilbert catalogue's type-formation closure. *)
Inductive TypeCode : Type :=
| SortCode (a : nat)
| SchemeCode (s : Scheme).

Definition type_code (s : Scheme) : TypeCode :=
  match s with
  | P1 a b => SchemeCode (P2 a b (Nat.max (S a) b))
  | P2 a _ _ => SortCode (S (S a))
  | P3 a _ _ => SchemeCode (P5 a (S (S a)))
  | P4 a _ => SchemeCode (P5 a 0)
  | P5 _ _ => SortCode 1
  | P6 a b => SchemeCode (P7 a b b)
  | P7 a _ _ => SortCode (S (S a))
  | P8 a b _ => SchemeCode (P2 a b 0)
  | P9 a _ _ => SchemeCode (P5 a (S (S a)))
  | P10 a b _ => SchemeCode (P2 a b (S a))
  | P11 a b _ => SchemeCode (P7 a b 0)
  end.

Definition expand_type_code {n} (c : TypeCode) : Term nat n :=
  match c with SortCode a => 𝓤 a | SchemeCode s => subject s end.

Theorem type_code_exact {n} s :
  @expand_type_code n (type_code s) = declared_type s.
Proof. destruct s; reflexivity. Qed.

(** Replace the first product below an initial lambda prefix by a lambda.
    This is syntactic PRODUCT EXPOSURE, not an eta-conversion principle. *)
Fixpoint expose_product {n} (t : Term nat n) : option (Term nat n) :=
  match t with
  | Π A B => Some (lam A B)
  | lam A b => option_map (lam A) (expose_product b)
  | _ => None
  end.

Definition exposure (s : Scheme) : option Scheme :=
  match s with
  | P1 a b => Some (P6 a b)
  | P2 a b c => Some (P3 a b c)
  | P3 a b c => Some (P8 a b c)
  | P5 a c => Some (P4 a c)
  | P7 a b c => Some (P9 a b c)
  | P9 a b c => Some (P10 a b c)
  | P10 a b c => Some (P11 a b c)
  | _ => None
  end.

Theorem exposure_exact {n} s :
  expose_product (@subject n s) = option_map subject (exposure s).
Proof. destruct s; reflexivity. Qed.

(** First explicit auxiliary compilations into the original FOUR-FAMILY
    expression grammar.  Both independent HasType derivations and literal
    annotated beta recovery are proved, without adding catalogue atoms. *)
Definition p4_code a c : Presentation.Expression :=
  Presentation.Apply
    (Presentation.Apply
      (Presentation.Apply (Presentation.Constant 0 0) (Presentation.Universe 0))
      (Presentation.Universe a))
    (Presentation.Universe c).

Definition p5_code a c : Presentation.Expression :=
  Presentation.Apply
    (Presentation.Apply (Presentation.Product 0 0) (Presentation.Universe a))
    (p4_code a c).

Local Ltac change_code_type T :=
  lazymatch goal with
  | |- Presentation.HasType ?p _ => change (Presentation.HasType p T)
  end.

Theorem p4_code_typed a c :
  Presentation.HasType (p4_code a c) (declared_type (P4 a c)).
Proof.
  unfold p4_code. cbn [declared_type].
  change_code_type (@subst nat 0 (Π (𝓤 a) (𝓤 0)) (𝓤 c)).
  eapply Presentation.type_apply with (A := 𝓤 0).
  - change_code_type (@subst nat 0 (Π (𝓤 0) (Π v1 (𝓤 0))) (𝓤 a)).
    eapply Presentation.type_apply with (A := 𝓤 0).
    + change_code_type
        (@subst nat 0 (Π (𝓤 0) (Π v1 (Π v1 (var (fsucc (fsucc (fsucc fzero)))))))
          (𝓤 0)).
      eapply Presentation.type_apply with (A := 𝓤 0).
      * apply Presentation.type_constant.
      * apply Presentation.type_universe.
    + apply Presentation.type_universe.
  - apply Presentation.type_universe.
Qed.

Theorem p5_code_typed a c :
  Presentation.HasType (p5_code a c) (declared_type (P5 a c)).
Proof.
  unfold p5_code. cbn [declared_type].
  change_code_type (@subst nat 0 (𝓤 1) (Presentation.expand (p4_code a c))).
  eapply Presentation.type_apply with (A := Π (𝓤 a) (𝓤 0)).
  - change_code_type (@subst nat 0 (Π (Π v0 (𝓤 0)) (𝓤 1)) (𝓤 a)).
    eapply Presentation.type_apply with (A := 𝓤 0).
    + apply Presentation.type_product.
    + apply Presentation.type_universe.
  - apply p4_code_typed.
Qed.

Local Ltac head_beta :=
  first [apply step_beta | apply step_app_left; head_beta].
Local Ltac compute_head :=
  eapply rtc_step; [head_beta | cbn; unfold shift, subst; cbn;
    autorewrite with syntax].

Theorem p4_code_beta a c :
  Presentation.expand (p4_code a c) ↠ᵝ subject (P4 a c).
Proof.
  unfold p4_code. cbn [Presentation.expand subject].
  unfold Core.constant_simple. do 3 compute_head. reflexivity.
Qed.

Theorem p5_code_beta a c :
  Presentation.expand (p5_code a c) ↠ᵝ subject (P5 a c).
Proof.
  unfold p5_code. cbn [Presentation.expand subject].
  transitivity (Core.product 0 0 $ 𝓤 a $ lam (𝓤 a) (𝓤 c) : Term nat 0).
  - apply app_cong_r. apply p4_code_beta.
  - unfold Core.product. do 2 compute_head.
    eapply rtc_step; [apply step_pi_right, step_beta | reflexivity].
Qed.

Print Assumptions scheme_typed.
Print Assumptions scheme_type_sorted.
Print Assumptions type_code_exact.
Print Assumptions exposure_exact.
Print Assumptions p4_code_typed.
Print Assumptions p5_code_typed.
Print Assumptions p4_code_beta.
Print Assumptions p5_code_beta.

End ProductCatalogue.
