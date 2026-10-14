(** The all-rank neutral-spine invariant needed by hereditary substitution.
    A variable-headed spine cannot increase the rank of its assigned type.
    This is a theorem of the ORIGINAL typing rules, independent of semantic
    conversion, denotation, normal forms or a finite collection of examples.
    It is a component of, not a replacement for, semantic substitution. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing Ranks Inversions Preservation
  Reduction DefEq AbstractRewriting.
From PTSrkModel Require Import SyntaxSubstitution CanonicalTypeWitnesses CanonicalRenaming.

Module NeutralCutRank.

Inductive headed_by {n} (i : Fin n) : Term nat n -> Prop :=
| headed_variable : headed_by i (var i)
| headed_application f u : headed_by i f -> headed_by i (app f u).

Lemma headed_not_lambda {n} (i : Fin n) t :
  headed_by i t -> forall A b, t <> lam A b.
Proof. intro H; destruct H; intros A b E; discriminate. Qed.

Theorem headed_type_rank {n} (i : Fin n) t : headed_by i t ->
  forall (G : Ctx nat n) T r,
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  @typ nat RankSorts n G (G !! i) (𝓤 r) ->
  exists k, k <= r /\ @typ nat RankSorts n G T (𝓤 k).
Proof.
  intro HH; induction HH as [|f u HH IH]; intros G T r HG HT HI.
  - destruct (type_is_correct (var i) T HT HG) as [k TK].
    assert (E : k = r).
    { apply (@equiv_𝓤_inversion nat n k r).
      eapply type_stability; [exact TK | exact HI | exact HG |].
      eapply var_inversion; exact HT. }
    subst k; exists r; split; [lia | exact TK].
  - destruct (app_inversion RankSorts f u T HT) as [A [B [TF [TU ET]]]].
    destruct (IH G (Π A B) r HG TF HI) as [q [Hq TP]].
    destruct (Π_inversion RankSorts A (𝓤 q) B TP)
      as [m [k [l [R [TA [TB EQl]]]]]].
    apply equiv_𝓤_inversion in EQl.
    change (l = Nat.max (S m) k) in R.
    assert (TC : @typ nat RankSorts n G (B ◁ u) (𝓤 k)).
    { change (@typ nat RankSorts n G (B ◁ u) ((𝓤 k) ◁ u)).
      eapply substitution_lemma; eassumption. }
    destruct (type_is_correct (app f u) T HT HG) as [j TJ].
    assert (E : j = k).
    { apply (@equiv_𝓤_inversion nat n j k).
      eapply type_stability; [exact TJ | exact TC | exact HG | exact ET]. }
    subst j; exists k; split; [|exact TJ].
    pose proof (Nat.le_max_r (S m) k); lia.
Qed.

Corollary cut_headed_type_rank {n} (G : Ctx nat n) A t T r :
  @wf nat RankSorts n G -> @typ nat RankSorts n G A (𝓤 r) ->
  headed_by fzero t -> @typ nat RankSorts (S n) (G & A) t T ->
  exists k, k <= r /\ @typ nat RankSorts (S n) (G & A) T (𝓤 k).
Proof.
  intros HG TA HH HT. eapply headed_type_rank; [exact HH | | exact HT |].
  - eapply wf_cons; eassumption.
  - change (@typ nat RankSorts (S n) (G & A) (shift A) (shift (𝓤 r))).
    apply weakening; exact TA.
Qed.

Theorem headed_replace {n} (i : Fin n) t : headed_by i t ->
  forall m (sigma : Fin n -> Term nat m) j,
  headed_by j (sigma i) -> headed_by j (replace sigma t).
Proof. intro HH; induction HH; intros m sigma j HS; cbn [replace]; auto using headed_application. Qed.

Theorem headed_step {n} (i : Fin n) t : headed_by i t ->
  forall u, t →ᵝ u -> headed_by i u.
Proof.
  intro HH; induction HH; intros v R.
  - inversion R.
  - inversion R; subst.
    + apply headed_application, IHHH; assumption.
    + apply headed_application; assumption.
    + exfalso; eapply headed_not_lambda; [exact HH | reflexivity].
Qed.

Theorem headed_reduction {n} (i : Fin n) t u :
  headed_by i t -> t ↠ᵝ u -> headed_by i u.
Proof.
  intros HH R; induction R; [exact HH |].
  apply IHR; eapply headed_step; eassumption.
Qed.

(** The product is the ACTUAL type of the substituted head. Its domain
    rank is strictly below the cut rank, even if the original assigned
    type and its substitution are not normal. *)
Theorem headed_substituted_product_rank {n} (i : Fin n) f : headed_by i f ->
  forall (G : Ctx nat n) T r m (D : Ctx nat m)
    (sigma : Fin n -> Term nat m) A B,
  @wf nat RankSorts n G -> @wf nat RankSorts m D ->
  @typ nat RankSorts n G f T -> @typ nat RankSorts n G (G !! i) (𝓤 r) ->
  typed_substitution G D sigma ->
  @typ nat RankSorts m D (replace sigma f) (Π A B) ->
  exists a b, a < r /\ b <= r /\
    @typ nat RankSorts m D A (𝓤 a) /\
    @typ nat RankSorts (S m) (D & A) B (𝓤 b).
Proof.
  intros HH G T r m D sigma A B HG HD TF HI HS TP.
  destruct (headed_type_rank i f HH G T r HG TF HI) as [q [Hq TQ]].
  assert (TT : @typ nat RankSorts m D (replace sigma T) (𝓤 q)).
  { change (@typ nat RankSorts m D (replace sigma T) (replace sigma (𝓤 q))).
    eapply rank_typing_replace; eassumption. }
  assert (TF' : @typ nat RankSorts m D (replace sigma f) (replace sigma T)) by
    (eapply rank_typing_replace; eassumption).
  assert (ET : replace sigma T =ᵝ Π A B) by
    (eapply uniqueness_of_typing; [exact TF' | exact TP]).
  destruct (type_is_correct (replace sigma f) (Π A B) TP HD) as [p TPi].
  assert (E : q = p).
  { apply (@equiv_𝓤_inversion nat m q p).
    eapply type_stability; eassumption. }
  subst p. destruct (Π_inversion RankSorts A (𝓤 q) B TPi)
    as [a [b [l [R [TA [TB El]]]]]].
  apply equiv_𝓤_inversion in El.
  change (l = Nat.max (S a) b) in R.
  exists a, b; split.
  - pose proof (Nat.le_max_l (S a) b); lia.
  - split; [pose proof (Nat.le_max_r (S a) b); lia | auto].
Qed.

(** A lambda reached from a substituted neutral spine must originate at
    the cut variable, not at an untouched variable further in the context. *)
Theorem single_cut_lambda_head {n} (i : Fin (S n)) f u A b :
  headed_by i f -> f ◁ u ↠ᵝ lam A b -> i = fzero.
Proof.
  intros HH R. dependent elimination i as [fzero | fsucc j]; [reflexivity |].
  exfalso. assert (HH' : headed_by j (f ◁ u)).
  { unfold subst. eapply headed_replace; [exact HH |].
    cbn [fin_match]; apply headed_variable. }
  pose proof (headed_reduction j (f ◁ u) (lam A b) HH' R) as HL.
  eapply headed_not_lambda; [exact HL | reflexivity].
Qed.

Local Lemma product_sort_distinct {n} (A : Term nat n) B j : ~ (Π A B =ᵝ 𝓤 j).
Proof.
  intros E; apply def_equiv_prop in E as [N [RP RU]].
  assert (EN : (𝓤 j : Term nat n) = N).
  { apply normal_reductions_equal; [intros v R; inversion R |exact RU]. }
  subst N. destruct (rtc_Π_repr A (𝓤 j) B RP) as [C [D E]]. discriminate.
Qed.

Theorem normal_function_head {n} (f : Term nat n) : beta_normal f -> not_lambda f ->
  forall (G : Ctx nat n) A B, @typ nat RankSorts n G f (Π A B) ->
  exists i, headed_by i f.
Proof.
  induction f as [n j | n C IHC D IHD | n i | n C IHC t IHt | n f IHf u IHu];
    intros NF LF G A B TF.
  - destruct (𝓤_inversion RankSorts j (Π A B) TF) as [k [_ E]].
    exfalso; eapply product_sort_distinct; exact E.
  - destruct (Π_inversion RankSorts C (Π A B) D TF)
      as [j [k [l [_ [_ [_ E]]]]]].
    exfalso; eapply product_sort_distinct; exact E.
  - exists i; apply headed_variable.
  - exfalso; eapply LF; reflexivity.
  - destruct (app_inversion RankSorts f u (Π A B) TF) as [C [D [TF' [_ _]]]].
    destruct (proj1 (beta_normal_application f u) NF) as [Nf [_ Lf]].
    destruct (IHf Nf Lf G C D TF') as [i Hi].
    exists i; apply headed_application; exact Hi.
Qed.

(** General active-head branch: when substituting u for the newest
    variable exposes a lambda from a normal nonlambda function, the
    lambda's ACTUAL domain rank is smaller than the cut rank. *)
Theorem exposed_lambda_domain_rank {n} (G : Ctx nat n) A f F u C t r :
  @wf nat RankSorts n G -> @typ nat RankSorts n G A (𝓤 r) ->
  @typ nat RankSorts (S n) (G & A) f F ->
  (exists D E, F = Π D E) -> beta_normal f -> not_lambda f ->
  @typ nat RankSorts n G u A -> f ◁ u ↠ᵝ lam C t ->
  exists m k B, m < r /\ k <= r /\
    @typ nat RankSorts n G C (𝓤 m) /\
    @typ nat RankSorts (S n) (G & C) B (𝓤 k) /\
    @typ nat RankSorts (S n) (G & C) t B.
Proof.
  intros HG TA TF [D [E EF]] Nf Lf TU RR; subst F.
  destruct (normal_function_head f Nf Lf (G & A) D E TF) as [i Hi].
  assert (Ei : i = fzero) by (eapply single_cut_lambda_head; eassumption).
  subst i.
  destruct (cut_headed_type_rank G A f (Π D E) r HG TA Hi TF) as [q [Hq TQ]].
  assert (TQ' : @typ nat RankSorts n G ((Π D E) ◁ u) (𝓤 q)).
  { change (@typ nat RankSorts n G ((Π D E) ◁ u) ((𝓤 q) ◁ u)).
    eapply substitution_lemma; eassumption. }
  assert (TL : @typ nat RankSorts n G (lam C t) ((Π D E) ◁ u)).
  { eapply subject_reduction'; [|exact HG|exact RR].
    eapply substitution_lemma; eassumption. }
  destruct (λ_inversion RankSorts C ((Π D E) ◁ u) t TL)
    as [m [B [TC [TT ET]]]].
  assert (HGC : @wf nat RankSorts (S n) (G & C)) by (eapply wf_cons; eassumption).
  destruct (type_is_correct t B TT HGC) as [k TB].
  assert (TP : @typ nat RankSorts n G (Π C B) (𝓤 (Nat.max (S m) k))).
  { eapply typ_Π; [exact TC |exact TB|reflexivity]. }
  assert (Er : q = Nat.max (S m) k).
  { apply (@equiv_𝓤_inversion nat n q (Nat.max (S m) k)).
    eapply type_stability; [exact TQ'|exact TP|exact HG|exact ET]. }
  exists m, k, B; split; [pose proof (Nat.le_max_l (S m) k); lia |].
  split; [pose proof (Nat.le_max_r (S m) k); lia |auto].
Qed.

(** Variables are harmless under binder lifting. Only nonvariable images
    need a source-declaration rank bound. This supports arbitrary cuts and
    simultaneous substitutions, including every lifted binder. *)
Definition bounded_substitution {n m} r (G : Ctx nat n)
  (sigma : Fin n -> Term nat m) :=
  forall i, (forall j, sigma i <> var j) ->
    exists q, q <= r /\ @typ nat RankSorts n G (G !! i) (𝓤 q).

Lemma bounded_substitution_extend {n m} r (G : Ctx nat n)
  (sigma : Fin n -> Term nat m) A :
  bounded_substitution r G sigma -> bounded_substitution r (G & A) (transpose sigma).
Proof.
  intros HB i HV; dependent elimination i as [fzero | fsucc j].
  - exfalso; apply (HV fzero); reflexivity.
  - assert (HN : forall z, sigma j <> var z).
    { intros z E; apply (HV (fsucc z)).
      change (shift (sigma j) = var (fsucc z)); rewrite E; reflexivity. }
    destruct (HB j HN) as [q [Hq Tq]]. exists q; split; [exact Hq |].
    change (@typ nat RankSorts _ (G & A) (shift (G !! j)) (shift (𝓤 q))).
    apply weakening; exact Tq.
Qed.

Theorem bounded_exposed_lambda_domain_rank {n m} (G : Ctx nat n) (D : Ctx nat m)
  sigma f F C t r :
  @wf nat RankSorts n G -> @wf nat RankSorts m D ->
  typed_substitution G D sigma -> bounded_substitution r G sigma ->
  @typ nat RankSorts n G f F -> (exists A B, F = Π A B) ->
  beta_normal f -> not_lambda f -> replace sigma f ↠ᵝ lam C t ->
  exists a b B, a < r /\ b <= r /\
    @typ nat RankSorts m D C (𝓤 a) /\
    @typ nat RankSorts (S m) (D & C) B (𝓤 b) /\
    @typ nat RankSorts (S m) (D & C) t B.
Proof.
  intros HG HD HT HB TF [A [B EF]] Nf Lf RR; subst F.
  destruct (normal_function_head f Nf Lf G A B TF) as [i Hi].
  assert (HN : forall j, sigma i <> var j).
  { intros j E. assert (HJ : headed_by j (replace sigma f)).
    { eapply headed_replace; [exact Hi |rewrite E; apply headed_variable]. }
    pose proof (headed_reduction j _ _ HJ RR) as HH.
    eapply headed_not_lambda; [exact HH |reflexivity]. }
  destruct (HB i HN) as [r0 [Hr TI]].
  destruct (headed_type_rank i f Hi G (Π A B) r0 HG TF TI) as [q [Hq TQ]].
  assert (TQ' : @typ nat RankSorts m D (replace sigma (Π A B)) (𝓤 q)).
  { change (@typ nat RankSorts m D (replace sigma (Π A B)) (replace sigma (𝓤 q))).
    eapply rank_typing_replace; eassumption. }
  assert (TL : @typ nat RankSorts m D (lam C t) (replace sigma (Π A B))).
  { eapply subject_reduction'; [|exact HD|exact RR].
    eapply rank_typing_replace; eassumption. }
  destruct (λ_inversion RankSorts C (replace sigma (Π A B)) t TL)
    as [a [T [TC [TT ET]]]].
  assert (HDC : @wf nat RankSorts (S m) (D & C)) by (eapply wf_cons; eassumption).
  destruct (type_is_correct t T TT HDC) as [b TB].
  assert (TP : @typ nat RankSorts m D (Π C T) (𝓤 (Nat.max (S a) b))).
  { eapply typ_Π; [exact TC |exact TB|reflexivity]. }
  assert (Er : q = Nat.max (S a) b).
  { apply (@equiv_𝓤_inversion nat m q (Nat.max (S a) b)).
    eapply type_stability; [exact TQ'|exact TP|exact HD|exact ET]. }
  exists a, b, T; split; [pose proof (Nat.le_max_l (S a) b); lia |].
  split; [pose proof (Nat.le_max_r (S a) b); lia |auto].
Qed.

End NeutralCutRank.

Print Assumptions NeutralCutRank.headed_type_rank.
Print Assumptions NeutralCutRank.cut_headed_type_rank.
Print Assumptions NeutralCutRank.headed_replace.
Print Assumptions NeutralCutRank.headed_step.
Print Assumptions NeutralCutRank.headed_reduction.
Print Assumptions NeutralCutRank.headed_substituted_product_rank.
Print Assumptions NeutralCutRank.single_cut_lambda_head.
Print Assumptions NeutralCutRank.normal_function_head.
Print Assumptions NeutralCutRank.exposed_lambda_domain_rank.
Print Assumptions NeutralCutRank.bounded_substitution_extend.
Print Assumptions NeutralCutRank.bounded_exposed_lambda_domain_rank.
Check NeutralCutRank.headed_type_rank.
Check NeutralCutRank.headed_substituted_product_rank.
Check NeutralCutRank.exposed_lambda_domain_rank.
