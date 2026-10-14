(** Propagate Cartesian-square absorption through the powerset hierarchy
    using disjoint tags. No GCH or cardinal classification premise is used. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From ZFC Require Import Sets Axioms Cartesian.
From PTSrkModel Require Import SetFunctions SetApplication SetBijections ProductEmbedding CardinalGrowth SubsetFunctions
  PowersetEmbedding CartesianMaps CountablePairing CountableCodes CodeUniverses
  CardinalHierarchy CodeHierarchyBounds.
Import CodeUniverses.CodeUniverses.

Definition binary_union X Y := Union (Paire X Y).
Lemma binary_union_membership z X Y : IN z (binary_union X Y) <-> IN z X \/ IN z Y.
Proof.
  split.
  - intro H. destruct (Union_IN _ _ H) as [Z [HZ Hz]].
    destruct (Paire_IN _ _ _ HZ) as [E | E];
      [left | right]; exact (IN_sound_right z Z _ E Hz).
  - intros [H | H]; unfold binary_union;
      [apply (IN_Union (Paire X Y) X z); [apply IN_Paire_left | exact H] |
       apply (IN_Union (Paire X Y) Y z); [apply IN_Paire_right | exact H]].
Qed.
Definition tagged_subsets a b X Y := binary_union (Prod X (Sing a)) (Prod Y (Sing b)).
Lemma tagged_pair a b X Y x t : IN (Couple x t) (tagged_subsets a b X Y) <->
  (IN x X /\ EQ t a) \/ (IN x Y /\ EQ t b).
Proof.
  unfold tagged_subsets. rewrite binary_union_membership. split.
  - intros [H | H].
    + destruct (Couple_Prod_IN _ _ _ _ H) as [Hx Ht].
      left; split; [exact Hx | apply IN_Sing_EQ; exact Ht].
    + destruct (Couple_Prod_IN _ _ _ _ H) as [Hx Ht].
      right; split; [exact Hx | apply IN_Sing_EQ; exact Ht].
  - intros [[Hx E] | [Hx E]].
    + left. apply Couple_IN_Prod; [exact Hx |].
      eapply IN_sound_left; [apply EQ_sym; exact E | apply IN_Sing].
    + right. apply Couple_IN_Prod; [exact Hx |].
      eapply IN_sound_left; [apply EQ_sym; exact E | apply IN_Sing].
Qed.
Lemma tagged_left a b X Y x : ~ EQ a b ->
  (IN (Couple x a) (tagged_subsets a b X Y) <-> IN x X).
Proof.
  intro Hneq. rewrite tagged_pair. split.
  - intros [[Hx _] | [_ E]]; [exact Hx | contradiction].
  - intro Hx; left; split; [exact Hx | apply EQ_refl].
Qed.
Lemma tagged_right a b X Y x : ~ EQ a b ->
  (IN (Couple x b) (tagged_subsets a b X Y) <-> IN x Y).
Proof.
  intro Hneq. rewrite tagged_pair. split.
  - intros [[_ E] | [Hx _]]; [exfalso; apply Hneq, EQ_sym; exact E | exact Hx].
  - intro Hx; right; split; [exact Hx | apply EQ_refl].
Qed.
Lemma tagged_extensional a b : binary_extensional (tagged_subsets a b).
Proof.
  intros X X' Y Y' EX EY. apply Union_sound.
  eapply EQ_tran; [apply Paire_sound_left | apply Paire_sound_right];
    apply cartesian_extensional; [exact EX | apply EQ_refl | exact EY | apply EQ_refl].
Qed.
Lemma tagged_injective a b X X' Y Y' : ~ EQ a b ->
  EQ (tagged_subsets a b X Y) (tagged_subsets a b X' Y') -> EQ X X' /\ EQ Y Y'.
Proof.
  intros Hneq E. split; apply INC_EQ; intros x Hx.
  - apply (tagged_left a b X' Y' x Hneq).
    apply (IN_sound_right _ _ _ E). apply (tagged_left a b X Y x Hneq); exact Hx.
  - apply (tagged_left a b X Y x Hneq).
    apply (IN_sound_right _ _ _ (EQ_sym _ _ E)). apply (tagged_left a b X' Y' x Hneq); exact Hx.
  - apply (tagged_right a b X' Y' x Hneq).
    apply (IN_sound_right _ _ _ E). apply (tagged_right a b X Y x Hneq); exact Hx.
  - apply (tagged_right a b X Y x Hneq).
    apply (IN_sound_right _ _ _ (EQ_sym _ _ E)). apply (tagged_right a b X' Y' x Hneq); exact Hx.
Qed.
Lemma singleton_subset A a : IN a A -> INC (Sing a) A.
Proof.
  intros Ha x Hx. exact (IN_sound_left a x A (EQ_sym _ _ (IN_Sing_EQ _ _ Hx)) Ha).
Qed.
Lemma tagged_bound A a b X Y : IN a A -> IN b A -> INC X A -> INC Y A ->
  INC (tagged_subsets a b X Y) (Prod A A).
Proof.
  intros Ha Hb HX HY e He. apply binary_union_membership in He as [He | He].
  - exact (cartesian_monotone X A (Sing a) A HX (singleton_subset A a Ha) e He).
  - exact (cartesian_monotone Y A (Sing b) A HY (singleton_subset A b Hb) e He).
Qed.
Theorem powerset_square_step A a b :
  IN a A -> IN b A -> ~ EQ a b -> embeds (Prod A A) A ->
  embeds (Prod (Power A) (Power A)) (Power A).
Proof.
  intros Ha Hb Hneq HA. eapply embeds_transitive; [| apply powerset_embeds; exact HA].
  exists (cartesian_graph (Power A) (Power A) (tagged_subsets a b)).
  apply cartesian_graph_injection.
  - apply tagged_extensional.
  - intros X Y HX HY. apply INC_IN_Power, tagged_bound;
      [exact Ha | exact Hb | apply IN_Power_INC; exact HX | apply IN_Power_INC; exact HY].
  - intros X X' Y Y' HX HX' HY HY' E. apply (tagged_injective a b); assumption.
Qed.

Theorem carrier_square_absorption i : embeds (Prod (carrier i) (carrier i)) (carrier i).
Proof.
  induction i; [apply countable_square_embeds |].
  apply (powerset_square_step (carrier i) (numeral 0) (numeral 1)).
  - apply (carrier_inclusion 0 i); [lia | apply numeral_in_omega].
  - apply (carrier_inclusion 0 i); [lia | apply numeral_in_omega].
  - intro E. apply numeral_injective in E; discriminate.
  - exact IHi.
Qed.
Theorem carrier_cartesian_bound i j :
  embeds (Prod (carrier i) (carrier j)) (carrier (Nat.max i j)).
Proof.
  eapply embeds_transitive; [| apply carrier_square_absorption].
  apply inclusion_embeds, cartesian_monotone; apply carrier_inclusion; lia.
Qed.
Theorem carrier_subset_exponent i :
  embeds (dependent_product (carrier i) (fun _ => Power (carrier i))) (Power (carrier i)).
Proof. apply square_absorption_subset_exponent, carrier_square_absorption. Qed.

Theorem carrier_mixed_subset_exponent m n :
  embeds (dependent_product (carrier m) (fun _ => Power (carrier n)))
    (carrier (S (Nat.max m n))).
Proof.
  eapply embeds_transitive; [apply subset_function_embeds |].
  apply powerset_embeds, carrier_cartesian_bound.
Qed.
Theorem carrier_function_bound m n :
  embeds (dependent_product (carrier m) (fun _ => carrier n))
    (carrier (Nat.max (S m) n)).
Proof.
  destruct n as [|n].
  - rewrite Nat.max_0_r.
    destruct (embeds_powerset (carrier 0)) as [f Hf].
    eapply embeds_transitive with
      (B := dependent_product (carrier m) (fun _ => Power (carrier 0))).
    + eapply dependent_product_embeds with (enc := fun _ => f).
      * intros x y E; apply EQ_refl.
      * intros x Hx; exact Hf.
    + replace (S m) with (S (Nat.max m 0)) by lia.
      apply carrier_mixed_subset_exponent.
  - replace (Nat.max (S m) (S n)) with (S (Nat.max m n)) by lia.
    apply carrier_mixed_subset_exponent.
Qed.

Lemma dependent_fiber_inclusion A B K :
  (forall x, IN x A -> INC (B x) K) ->
  INC (dependent_product A B) (dependent_product A (fun _ => K)).
Proof.
  intros HB g Hg. pose proof (dependent_product_elimination _ _ _ Hg) as [HT [HV HU]].
  apply bounded_function_member.
  - intros e He. destruct (dependent_product_pair A B g e Hg He) as [x [y [E [Hx Hxy]]]].
    apply (IN_sound_left _ e _ E). apply Couple_IN_Prod; [exact Hx |].
    apply (HB x Hx). exact (proj2 (HV x y Hxy)).
  - split; [exact HT |]. split; [| exact HU].
    intros x y Hxy. destruct (HV x y Hxy) as [Hx Hy]. split; [exact Hx |].
    exact (HB x Hx y Hy).
Qed.
Lemma bounded_subset_exponent A m n : INC A (carrier m) ->
  embeds (dependent_product A (fun _ => Power (carrier n)))
    (carrier (S (Nat.max m n))).
Proof.
  intro HA. eapply embeds_transitive; [apply subset_function_embeds |].
  apply powerset_embeds. eapply embeds_transitive; [| apply carrier_cartesian_bound].
  apply inclusion_embeds, cartesian_monotone; [exact HA | intros x Hx; exact Hx].
Qed.
Theorem bounded_dependent_exponent A B m n :
  INC A (carrier m) -> (forall x, IN x A -> INC (B x) (carrier n)) ->
  embeds (dependent_product A B) (carrier (Nat.max (S m) n)).
Proof.
  intros HA HB. eapply embeds_transitive.
  - apply inclusion_embeds. exact (dependent_fiber_inclusion A B (carrier n) HB).
  - destruct n as [|n].
    + rewrite Nat.max_0_r. destruct (embeds_powerset (carrier 0)) as [f Hf].
      eapply embeds_transitive with (B := dependent_product A (fun _ => Power (carrier 0))).
      * eapply dependent_product_embeds with (enc := fun _ => f).
        -- intros x y E; apply EQ_refl.
        -- intros x Hx; exact Hf.
      * replace (S m) with (S (Nat.max m 0)) by lia.
        apply bounded_subset_exponent; exact HA.
    + replace (Nat.max (S m) (S n)) with (S (Nat.max m n)) by lia.
      apply bounded_subset_exponent; exact HA.
Qed.
Theorem decoded_dependent_product_bound m n a b :
  IN a (U m) -> (forall x, IN x (decode a) -> IN (b x) (U n)) ->
  embeds (dependent_product (decode a) (fun x => decode (b x)))
    (carrier (Nat.max (S m) n)).
Proof.
  intros Ha Hb. apply bounded_dependent_exponent.
  - apply decoding_subset_bound; exact Ha.
  - intros x Hx. apply decoding_subset_bound, Hb; exact Hx.
Qed.

Print Assumptions bounded_dependent_exponent.
Print Assumptions decoded_dependent_product_bound.
Print Assumptions carrier_mixed_subset_exponent.
Print Assumptions carrier_function_bound.
Print Assumptions tagged_injective.
Print Assumptions powerset_square_step.
Print Assumptions carrier_square_absorption.
Print Assumptions carrier_cartesian_bound.
Print Assumptions carrier_subset_exponent.
Check carrier_cartesian_bound.
Check decoded_dependent_product_bound.
