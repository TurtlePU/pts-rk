From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import Syntax Context Typing Ranks Reduction
  Congruence AbstractRewriting.
From PTSrk.NormalizationComplexity Require Import Greedy.

(** A contraction/affine numeral fragment. W is duplication; the two affine
    tags denote fixed ORIGINAL annotated terms. The universe index i is a
    numerical family index, not an erased type argument. *)
Module AffineDuplication.

Local Abbreviation v0 := (var fzero).
Local Abbreviation v1 := (var (fsucc fzero)).
Local Abbreviation v2 := (var (fsucc (fsucc fzero))).
Local Abbreviation v3 := (var (fsucc (fsucc (fsucc fzero)))).

Definition endo {n} (i : nat) : Term nat n := Π (𝓤 i) (𝓤 i).
Definition church_type {n} (i : nat) : Term nat n := Π (endo i) (endo i).
Definition fork_type {n} (i : nat) : Term nat n :=
  Π (endo i) (Π (endo i) (endo i)).

Definition duplicate {n} (i : nat) : Term nat n :=
  lam (fork_type i) (lam (endo i) (v1 $ v0 $ v0)).
Definition duplicate_type {n} (i : nat) : Term nat n :=
  Π (fork_type i) (church_type i).

Definition affine_zero {n} (i : nat) : Term nat n :=
  lam (endo i) (lam (𝓤 i) v0).
Definition affine_step {n} (i : nat) : Term nat n :=
  lam (church_type i) (lam (endo i) (lam (endo i)
    (lam (𝓤 i) (v2 $ (v3 $ v1 $ v0))))).
Definition affine_step_type {n} (i : nat) : Term nat n :=
  Π (church_type i) (fork_type i).

(** The tactic builds only the six original typing constructors. *)
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
      | @typ _ _ _ _ _ (𝓤 ?a) => lazymatch TB with
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
      let t := eval cbv beta delta [endo church_type fork_type duplicate
        duplicate_type affine_zero affine_step affine_step_type] in t in
      let p := infer_original G t in exact p
  end.

Theorem duplicate_typed {n} (G : Ctx nat n) i :
  @typ nat RankSorts n G (duplicate i) (duplicate_type i).
Proof. original_typing. Qed.

Theorem affine_zero_typed {n} (G : Ctx nat n) i :
  @typ nat RankSorts n G (affine_zero i) (church_type i).
Proof. original_typing. Qed.

Theorem affine_step_typed {n} (G : Ctx nat n) i :
  @typ nat RankSorts n G (affine_step i) (affine_step_type i).
Proof. original_typing. Qed.

Theorem church_type_sorted {n} (G : Ctx nat n) i :
  @typ nat RankSorts n G (church_type i) (𝓤 2).
Proof. original_typing. Qed.

Theorem duplicate_type_sorted {n} (G : Ctx nat n) i :
  @typ nat RankSorts n G (duplicate_type i) (𝓤 3).
Proof. original_typing. Qed.

Theorem affine_step_type_sorted {n} (G : Ctx nat n) i :
  @typ nat RankSorts n G (affine_step_type i) (𝓤 3).
Proof. original_typing. Qed.

Local Ltac head_beta :=
  first [apply step_beta | apply step_app_left; head_beta].
Local Ltac compute_head :=
  eapply rtc_step; [head_beta | cbn; unfold shift, subst; cbn;
    autorewrite with syntax].

Theorem duplicate_beta {n} i (h f : Term nat n) :
  duplicate i $ h $ f ↠ᵝ h $ f $ f.
Proof. unfold duplicate. do 2 compute_head. reflexivity. Qed.

Theorem affine_zero_beta {n} i (f x : Term nat n) :
  affine_zero i $ f $ x ↠ᵝ x.
Proof. unfold affine_zero. do 2 compute_head. reflexivity. Qed.

Theorem affine_step_beta {n} i (m f g x : Term nat n) :
  affine_step i $ m $ f $ g $ x ↠ᵝ f $ (m $ g $ x).
Proof. unfold affine_step. do 4 compute_head. reflexivity. Qed.

Inductive Code : Type :=
| W | Jzero | Jstep | apply (f x : Code).

Fixpoint expand {n} (i : nat) (p : Code) : Term nat n :=
  match p with
  | W => duplicate i
  | Jzero => affine_zero i
  | Jstep => affine_step i
  | apply f x => expand i f $ expand i x
  end.

Lemma expand_rename i p : forall n m (rho : Fin n -> Fin m),
  rename rho (@expand n i p) = @expand m i p.
Proof.
  induction p; intros n m rho;
    cbn [expand duplicate fork_type church_type endo affine_zero affine_step
      rename weak fin_match]; try reflexivity.
  now rewrite IHp1, IHp2.
Qed.

Lemma expand_replace i p : forall n m (rho : Fin n -> Term nat m),
  replace rho (@expand n i p) = @expand m i p.
Proof.
  induction p; intros n m rho;
    cbn [expand duplicate fork_type church_type endo affine_zero affine_step
      replace transpose shift rename weak fin_match]; try reflexivity.
  now rewrite IHp1, IHp2.
Qed.

Fixpoint duplications (p : Code) : nat :=
  match p with
  | W => 1
  | Jzero | Jstep => 0
  | apply f x => duplications f + duplications x
  end.

Fixpoint atoms (p : Code) : nat :=
  match p with
  | W | Jzero | Jstep => 1
  | apply f x => atoms f + atoms x
  end.

Fixpoint numeral (k : nat) : Code :=
  match k with
  | 0 => Jzero
  | S k => apply W (apply Jstep (numeral k))
  end.

Theorem numeral_duplications k : duplications (numeral k) = k.
Proof. induction k; cbn; congruence. Qed.

Theorem numeral_atoms k : atoms (numeral k) = 2 * k + 1.
Proof. induction k; cbn; lia. Qed.

Theorem numeral_typed k : forall n (G : Ctx nat n) i,
  @typ nat RankSorts n G (expand i (numeral k)) (church_type i).
Proof.
  induction k; intros n G i; cbn [numeral expand].
  - apply affine_zero_typed.
  - change (@typ nat RankSorts n G
      (duplicate i $ (affine_step i $ expand i (numeral k)))
      (subst (church_type i) (affine_step i $ expand i (numeral k)))).
    eapply typ_app with (U := fork_type i).
    + apply duplicate_typed.
    + change (@typ nat RankSorts n G
        (affine_step i $ expand i (numeral k))
        (subst (fork_type i) (expand i (numeral k)))).
      eapply typ_app with (U := church_type i).
      * apply affine_step_typed.
      * apply IHk.
Qed.

Fixpoint iterate {n} (k : nat) (f x : Term nat n) : Term nat n :=
  match k with 0 => x | S k => f $ iterate k f x end.

Theorem numeral_beta k : forall n i (f x : Term nat n),
  expand i (numeral k) $ f $ x ↠ᵝ iterate k f x.
Proof.
  induction k; intros n i f x; cbn [numeral expand iterate].
  - apply affine_zero_beta.
  - transitivity (affine_step i $ expand i (numeral k) $ f $ f $ x).
    + apply app_cong_l. apply duplicate_beta.
    + transitivity (f $ (expand i (numeral k) $ f $ x)).
      * apply affine_step_beta.
      * apply app_cong_r. apply IHk.
Qed.

(** Unapplied representations reduce to the annotated Church term itself;
    saturation is not being used as an eta principle. *)
Definition church_normal {n} i k : Term nat n :=
  lam (endo i) (lam (𝓤 i) (iterate k v1 v0)).

Theorem numeral_expansion k n i :
  @expand n i (numeral k) ↠ᵝ church_normal i k.
Proof.
  destruct k; cbn [numeral expand church_normal iterate].
  - reflexivity.
  - unfold duplicate. compute_head.
    rewrite expand_rename. fold (reduces_to nat n). apply λ_cong_r.
    unfold affine_step. do 3 compute_head.
    rewrite expand_replace.
    fold (reduces_to nat (S n)). apply λ_cong_r.
    apply app_cong_r. apply numeral_beta.
Qed.

Lemma iterate_variables_normal {n} k (f x : Fin n) :
  normalb (iterate k (var f) (var x)) = true.
Proof.
  induction k; cbn [iterate normalb isLambda];
    [reflexivity | now rewrite IHk].
Qed.

Theorem church_normal_is_normal n i k :
  forall u, ~ step nat n (church_normal i k) u.
Proof.
  apply normalb_sound. cbn [church_normal endo normalb].
  apply iterate_variables_normal.
Qed.

Print Assumptions duplicate_typed.
Print Assumptions affine_zero_typed.
Print Assumptions affine_step_typed.
Print Assumptions church_type_sorted.
Print Assumptions duplicate_type_sorted.
Print Assumptions affine_step_type_sorted.
Print Assumptions duplicate_beta.
Print Assumptions affine_zero_beta.
Print Assumptions affine_step_beta.
Print Assumptions numeral_duplications.
Print Assumptions numeral_atoms.
Print Assumptions numeral_typed.
Print Assumptions numeral_beta.
Print Assumptions numeral_expansion.
Print Assumptions church_normal_is_normal.

End AffineDuplication.
