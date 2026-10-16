From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing Inversions Preservation Ranks DefEq.
Require Import PTSrk.NormalizationComplexity.Greedy
  PTSrk.NormalizationComplexity.RedexRanks
  PTSrk.NormalizationComplexity.Morphisms
  PTSrk.NormalizationComplexity.Safety.

Theorem greedy_safe_descent {n} (t : Term nat n) : forall G T d,
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  RankSafe G t (S d) -> RankSafe G (greedy t) d.
Proof.
  induction t; intros G T d HG Ht HS; cbn [greedy RankSafe] in *; try exact I.
  - destruct (Π_inversion RankSorts t1 T t2 Ht)
      as [a [b [r [Hr [HA [HB Heq]]]]]]. destruct HS as [HSa HSb].
    assert (HGA : @wf nat RankSorts (S n) (G & t1)) by (eapply wf_cons; eassumption).
    split; [eapply IHt1; eassumption |].
    eapply safe_context_last_reduction; [exact HG | exact HA | apply greedy_sound | |].
    + eapply subject_reduction'; [exact HB | exact HGA | apply greedy_sound].
    + eapply IHt2; eassumption.
  - destruct (λ_inversion RankSorts t1 T t2 Ht) as [a [B [HA [HB Heq]]]].
    destruct HS as [HSa HSb].
    assert (HGA : @wf nat RankSorts (S n) (G & t1)) by (eapply wf_cons; eassumption).
    split; [eapply IHt1; eassumption |].
    eapply safe_context_last_reduction; [exact HG | exact HA | apply greedy_sound | |].
    + eapply subject_reduction'; [exact HB | exact HGA | apply greedy_sound].
    + eapply IHt2; eassumption.
  - destruct (app_inversion RankSorts t1 t2 T Ht) as [U [V [Hf [Hu Heq]]]].
    assert (Hbound : RedexBound G (app t1 t2) (S d)) by (apply safe_to_bound; exact HS).
    destruct HS as [HSf [HSu HH]].
    pose proof (IHt1 G (Π U V) d HG Hf HSf) as HSf'.
    pose proof (IHt2 G U d HG Hu HSu) as HSu'.
    assert (Hf' : @typ nat RankSorts n G (greedy t1) (Π U V)).
    { eapply subject_reduction'; [exact Hf | exact HG | apply greedy_sound]. }
    assert (Hu' : @typ nat RankSorts n G (greedy t2) U).
    { eapply subject_reduction'; [exact Hu | exact HG | apply greedy_sound]. }
    destruct (type_is_correct _ _ Hf HG) as [r Hprod].
    assert (HfRank : TypeRank G (greedy t1) r) by (exists (Π U V); auto).
    destruct (greedy t1) as [l | A' B' | i | A' b' | f' u'] eqn:Ef;
      cbn [RankSafe] in HSf' |- *;
      try (split; [exact HSf' | split; [exact HSu' | discriminate]]).
    assert (Hr : r <= S d).
    { eapply greedy_contracted_head_bound; [exact HG | exact Ht | exact Hbound | rewrite Ef; reflexivity |].
      rewrite Ef. exact HfRank. }
    destruct (application_argument_rank G (lam A' b') (greedy t2) U V r HG Hf' Hu' HfRank)
      as [q [Hq Hqr]].
    assert (Hqd : q <= d) by lia.
    destruct (λ_inversion RankSorts A' (Π U V) b' Hf') as [a [B [HA [HB HE]]]].
    apply equiv_Π_inversion in HE as [HUA HVB].
    assert (HuA : @typ nat RankSorts n G (greedy t2) A').
    { eapply typ_conv; [exact Hu' | exact HA | exact HUA]. }
    destruct HSf' as [HSA HSbody].
    replace d with (Nat.max d q) by lia.
    eapply safe_substitution; [exact HG | eapply wf_cons; eassumption | exact HuA | exact HB |
      exact Hq | exact HSu' | exact HSbody].
Qed.

Theorem greedy_strict_descent {n} G (t T : Term nat n) d :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  RedexBound G t (S d) -> RedexBound G (greedy t) d.
Proof.
  intros HG Ht HB. apply safe_to_bound. eapply greedy_safe_descent; try eassumption.
  eapply bound_to_safe; eassumption.
Qed.

Theorem bounded_rounds_normal {n} d G (t T : Term nat n) :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  RedexBound G t d -> normalb (rounds d t) = true.
Proof.
  revert t T. induction d; intros t T HG Ht HB; cbn [rounds].
  - eapply zero_bound_normal; eassumption.
  - eapply IHd; [exact HG | | eapply greedy_strict_descent; eassumption].
    eapply subject_reduction'; [exact Ht | exact HG | apply greedy_sound].
Qed.
