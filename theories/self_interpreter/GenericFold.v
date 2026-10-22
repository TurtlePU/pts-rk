From Stdlib Require Import Lists.List Bool.Bool.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import Algebra DependentProgramDecoder.
Import Context ListNotations.

(** One actual ordinary-argument fold head per finite dependent signature.
    No algebra filling is built into the head: after P and Q, its ordinary
    object-language arguments are exactly the fields of the signature.
    Eta expansion is syntax here, NOT an eta conversion rule. *)
Module GenericFold.
Module A := Algebra.Algebra.
Module DP := DependentProgramDecoder.DependentProgramDecoder.
Module CT := A.CT.
Module UT := A.UT.
Module TR := A.TR.
Module PT := A.PT.
Module BP := DP.BP.

Definition expand {rs} (D : CT.telescope 0 rs) {n} (Q : Term nat n) :=
  CT.close_term (DP.domains D n) (UT.apply_under (DP.domains D n) Q).

Theorem expand_replace rs (D : CT.telescope 0 rs) m n
    (sigma : Fin m -> Term nat n) Q :
  replace sigma (expand D Q) = expand D (replace sigma Q).
Proof.
  unfold expand; rewrite CT.close_term_replace, UT.apply_under_replace,
    DP.domains_replace; reflexivity.
Qed.

Theorem expand_typed rs (D : CT.telescope 0 rs) E n (G : Ctx nat n) P Q :
  CT.formed ε D ->
  @typ nat RankSorts n G Q (DP.term_program_type D E P) ->
  @typ nat RankSorts n G (expand D Q) (DP.term_program_type D E P).
Proof.
  intros HD HQ; unfold expand, DP.term_program_type in *.
  apply CT.close_typing.
  - apply CT.formed_rename with (G := ε); [exact HD | apply DP.empty_typed].
  - apply UT.apply_under_typed; exact HQ.
Qed.

Theorem expand_normal rs (D : CT.telescope 0 rs) n (Q : Term nat n) :
  CT.normal_annotations D = true -> normalb Q = true ->
  isLambda Q = false -> normalb (expand D Q) = true.
Proof.
  intros HD HQ HL; unfold expand; rewrite CT.close_term_normal.
  unfold DP.domains; rewrite UT.annotations_rename, HD.
  cbn [andb]; apply UT.apply_under_normal; assumption.
Qed.

Definition head {rs} (D : CT.telescope 0 rs) C E : Term nat 0 :=
  lam (DP.type_program_type D C)
    (lam (DP.term_program_type D E (var fzero)) (expand D (var fzero))).

Definition head_type {rs} (D : CT.telescope 0 rs) C E : Term nat 0 :=
  Π (DP.type_program_type D C)
    (BP.arr (DP.term_program_type D E (var fzero))
      (DP.term_program_type D E (var fzero))).

Theorem head_typed s rs (D : CT.telescope 0 rs) C E :
  CT.formed ε D -> @typ nat RankSorts _ (CT.context D ε) C (𝓤 0) ->
  @typ nat RankSorts _ (CT.context D ε) E (BP.arr C (𝓤 s)) ->
  @typ nat RankSorts 0 ε (head D C E) (head_type D C E).
Proof.
  intros HD HC HE; unfold head, head_type, BP.arr.
  eapply typ_λ with (ℓ := CT.rank rs 0); [apply DP.type_program_sort; assumption |].
  eapply typ_λ with (ℓ := CT.rank rs s).
  - apply DP.term_program_sort with (C := C); [exact HD | exact HE |].
    rewrite DP.lift_closed_one; constructor.
  - unfold shift at 1; rewrite DP.term_program_rename.
    apply expand_typed; [exact HD |].
    rewrite <- DP.term_program_rename.
    change (typ ((ε & DP.type_program_type D C) & DP.term_program_type D E (var fzero))
      (var fzero) (((ε & DP.type_program_type D C) & DP.term_program_type D E (var fzero)) !! fzero)).
    constructor.
Qed.

Theorem head_type_sort s rs (D : CT.telescope 0 rs) C E :
  CT.formed ε D -> @typ nat RankSorts _ (CT.context D ε) C (𝓤 0) ->
  @typ nat RankSorts _ (CT.context D ε) E (BP.arr C (𝓤 s)) ->
  @typ nat RankSorts 0 ε (head_type D C E)
    (𝓤 (Nat.max (S (CT.rank rs 0))
      (Nat.max (S (CT.rank rs s)) (CT.rank rs s)))).
Proof.
  intros HD HC HE; unfold head_type; eapply typ_Π.
  - apply DP.type_program_sort; assumption.
  - apply BP.arr_sort; apply DP.term_program_sort with (C := C);
      [exact HD | exact HE | rewrite DP.lift_closed_one; constructor |
       exact HD | exact HE | rewrite DP.lift_closed_one; constructor].
  - reflexivity.
Qed.

Theorem head_normal rs (D : CT.telescope 0 rs) C E :
  CT.normal_annotations D = true -> normalb C = true ->
  normalb E = true -> isLambda E = false -> normalb (head D C E) = true.
Proof.
  intros HD HC HE HL; unfold head; cbn [normalb].
  rewrite DP.type_program_normal by assumption.
  rewrite DP.term_program_normal by (try assumption; reflexivity).
  rewrite expand_normal by (try assumption; reflexivity); reflexivity.
Qed.

Definition specialize {rs} (D : CT.telescope 0 rs) C E P Q :=
  app (app (head D C E) P) Q.

Theorem specialize_first rs (D : CT.telescope 0 rs) C E P :
  reduces_to nat 0 (app (head D C E) P)
    (lam (DP.term_program_type D E P) (expand D (var fzero))).
Proof.
  unfold head; eapply rtc_step; [apply step_beta |].
  unfold subst; cbn [replace]; rewrite DP.term_program_replace, expand_replace.
  cbn [replace transpose fin_match]; reflexivity.
Qed.

Theorem specialize_reduces rs (D : CT.telescope 0 rs) C E P Q :
  reduces_to nat 0 (specialize D C E P Q) (expand D Q).
Proof.
  unfold specialize; eapply rtc_trans.
  - apply (@app_cong_l nat (reduces_to nat) _ 0), specialize_first.
  - eapply rtc_step; [apply step_beta |].
    unfold subst; rewrite expand_replace; reflexivity.
Qed.

Theorem specialize_typed s rs (D : CT.telescope 0 rs) C E P Q :
  CT.formed ε D -> @typ nat RankSorts _ (CT.context D ε) C (𝓤 0) ->
  @typ nat RankSorts _ (CT.context D ε) E (BP.arr C (𝓤 s)) ->
  @typ nat RankSorts 0 ε P (DP.type_program_type D C) ->
  @typ nat RankSorts 0 ε Q (DP.term_program_type D E P) ->
  @typ nat RankSorts 0 ε (specialize D C E P Q) (DP.term_program_type D E P).
Proof.
  intros HD HC HE HP HQ; unfold specialize; eapply BP.arr_apply; [|exact HQ].
  pose proof (typ_app _ (head_typed s rs D C E HD HC HE) HP) as H.
  unfold head_type, BP.arr, subst in H; cbn [replace] in H.
  rewrite DP.term_program_replace, replace_lift_shift, DP.term_program_replace in H.
  cbn [replace fin_match] in H; exact H.
Qed.

Theorem fold_expand rs (D : CT.telescope 0 rs) (alg : A.algebra D) Q :
  reduces_to nat 0 (A.fold alg (expand D Q)) (A.fold alg Q).
Proof.
  unfold expand; rewrite DP.domains_zero.
  eapply rtc_trans; [apply A.fold_closure |].
  rewrite <- TR.run_apply_under, DP.closed_replace.
  unfold A.fold, DP.evaluate.
  replace (TR.run D (DP.lifted_fill (A.fields alg)) Q)
    with (TR.run D (A.fields alg) Q); [reflexivity |].
  apply TR.run_ext; intro i; symmetry; apply DP.lift_closed_zero.
Qed.

(** [run] is the literal application head P Q alpha_1 ... alpha_n.
    The record only collects already typed argument terms in Rocq. *)
Definition run {rs} {D : CT.telescope 0 rs} (alg : A.algebra D) C E P Q :=
  A.fold alg (specialize D C E P Q).

Theorem run_computes rs (D : CT.telescope 0 rs) (alg : A.algebra D) C E P Q :
  reduces_to nat 0 (run alg C E P Q) (A.fold alg Q).
Proof.
  unfold run; eapply rtc_trans; [apply TR.run_reduces, specialize_reduces | apply fold_expand].
Qed.

Theorem run_typed s rs (D : CT.telescope 0 rs) (alg : A.algebra D) C E P Q :
  CT.formed ε D -> @typ nat RankSorts _ (CT.context D ε) C (𝓤 0) ->
  @typ nat RankSorts _ (CT.context D ε) E (BP.arr C (𝓤 s)) ->
  @typ nat RankSorts 0 ε P (DP.type_program_type D C) ->
  @typ nat RankSorts 0 ε Q (DP.term_program_type D E P) ->
  @typ nat RankSorts 0 ε (run alg C E P Q) (DP.result_type D (A.fields alg) E P).
Proof. intros; apply A.fold_typed; eapply specialize_typed; eassumption. Qed.

Theorem run_closure rs (D : CT.telescope 0 rs) (alg : A.algebra D) C E P body :
  reduces_to nat 0 (run alg C E P (CT.close_term D body))
    (replace (A.fields alg) body).
Proof. eapply rtc_trans; [apply run_computes | apply A.fold_closure]. Qed.

(** Pure syntactic composition: no source evaluator or semantic correctness
    premise is smuggled into the general-fold contract. *)
Theorem run_composition rs (D : CT.telescope 0 rs) (alg : A.algebra D)
    rs' (D' : CT.telescope 0 rs') (alg' : A.algebra D') C E P C' E' P' Q :
  reduces_to nat 0 (run alg' C' E' P' (run alg C E P Q))
    (A.fold alg' (A.fold alg Q)).
Proof.
  eapply rtc_trans; [apply run_computes |].
  apply TR.run_reduces, run_computes.
Qed.

Print Assumptions expand_replace.
Print Assumptions expand_typed.
Print Assumptions expand_normal.
Print Assumptions head_typed.
Print Assumptions head_type_sort.
Print Assumptions head_normal.
Print Assumptions specialize_first.
Print Assumptions specialize_reduces.
Print Assumptions specialize_typed.
Print Assumptions fold_expand.
Print Assumptions run_computes.
Print Assumptions run_typed.
Print Assumptions run_closure.
Print Assumptions run_composition.
End GenericFold.
