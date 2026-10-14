(** Actual bijections, not just possibly repeating enumerations, between
    the code universes and a fixed countably infinite set. No choice is used.
    This does not construct the uncountable alephs or prove a GCH bound. *)
From Stdlib Require Import Arith.PeanoNat Arith.Compare_dec Lia.
From ZFC Require Import Sets Axioms Cartesian.
From PTSrkModel Require Import SetFunctions SetApplication SetBijections
  ProductEmbedding CodeUniverses.
Import CodeUniverses.CodeUniverses.

Definition omega_codes : Ens := sup nat numeral.
Lemma omega_membership x : IN x omega_codes <-> exists n, EQ x (numeral n).
Proof. split; intros [n E]; exists n; exact E. Qed.
Lemma numeral_in_omega n : IN (numeral n) omega_codes.
Proof. exists n; apply EQ_refl. Qed.

(** Put the i+1 permitted infinite codes first, then alternate the finite
    and sort codes. This avoids the repetitions of enumerate_universe. *)
Definition slot i c := match c with
  | infinite j => j | finite n => S i + 2*n | sort j => S i + S (2*j) end.
Lemma slot_injective i c d :
  Allowed i c -> Allowed i d -> slot i c = slot i d -> c = d.
Proof.
  destruct c, d; cbn [Allowed slot]; intros; try (f_equal; lia); lia.
Qed.
Lemma even_or_odd n : exists k, n = 2*k \/ n = S (2*k).
Proof.
  induction n as [|n [k [H|H]]].
  - exists 0; auto.
  - exists k; right; lia.
  - exists (S k); left; lia.
Qed.
Lemma slot_surjective i n : exists c, Allowed i c /\ slot i c = n.
Proof.
  destruct (le_dec n i) as [H|H].
  - exists (infinite n); split; [exact H | reflexivity].
  - destruct (even_or_odd (n-S i)) as [k [E|E]].
    + exists (finite k); cbn [Allowed slot]; split; [exact I | lia].
    + exists (sort k); cbn [Allowed slot]; split; [exact I | lia].
Qed.

Definition counting_graph i : Ens :=
  sup {c : Code | Allowed i c}
    (fun c => Couple (repr (proj1_sig c)) (numeral (slot i (proj1_sig c)))).
Lemma counting_graph_application i x y :
  application (counting_graph i) x y <->
  exists c, Allowed i c /\ EQ x (repr c) /\ EQ y (numeral (slot i c)).
Proof.
  split.
  - intros [[c Hc] E]. exists c; split; [exact Hc |].
    split; [exact (Couple_inj_left _ _ _ _ E) | exact (Couple_inj_right _ _ _ _ E)].
  - intros [c [Hc [Ex Ey]]]. exists (Specif.exist _ c Hc).
    eapply EQ_tran; [apply Couple_sound_left; exact Ex | apply Couple_sound_right; exact Ey].
Qed.
Lemma counting_graph_bound i : INC (counting_graph i) (Prod (U i) omega_codes).
Proof.
  intros e [[c Hc] E].
  apply (IN_sound_left (Couple (repr c) (numeral (slot i c))) e _ (EQ_sym _ _ E)).
  apply Couple_IN_Prod; [apply code_membership; exact Hc | apply numeral_in_omega].
Qed.
Lemma counting_graph_laws i : function_laws (U i) (fun _ => omega_codes) (counting_graph i).
Proof.
  split.
  - intros x Hx. apply universe_membership in Hx as [c [Hc E]].
    exists (numeral (slot i c)). apply counting_graph_application.
    exists c; split; [exact Hc |]. split; [exact E | apply EQ_refl].
  - split.
    + intros x y H. apply counting_graph_application in H as [c [Hc [Ex Ey]]].
      split.
      * apply universe_membership. exists c; auto.
      * apply omega_membership. exists (slot i c); exact Ey.
    + intros x y z H H'.
      apply counting_graph_application in H as [c [Hc [Ex Ey]]].
      apply counting_graph_application in H' as [d [Hd [Ex' Ez]]].
      assert (Ecd : c = d).
      { apply repr_injective. eapply EQ_tran; [apply EQ_sym; exact Ex | exact Ex']. }
      subst d. eapply EQ_tran; [exact Ey | apply EQ_sym; exact Ez].
Qed.
Theorem counting_bijection i : bijection (U i) omega_codes (counting_graph i).
Proof.
  split.
  - apply bounded_function_member; [apply counting_graph_bound | apply counting_graph_laws].
  - split.
    + intros x x' y H H'.
      apply counting_graph_application in H as [c [Hc [Ex Ey]]].
      apply counting_graph_application in H' as [d [Hd [Ex' Ey']]].
      assert (Eslot : slot i c = slot i d).
      { apply numeral_injective. eapply EQ_tran; [apply EQ_sym; exact Ey | exact Ey']. }
      pose proof (slot_injective i c d Hc Hd Eslot) as Ecd. subst d.
      eapply EQ_tran; [exact Ex | apply EQ_sym; exact Ex'].
    + intros y Hy. apply omega_membership in Hy as [n E].
      destruct (slot_surjective i n) as [c [Hc Ec]]. exists (repr c).
      apply counting_graph_application. exists c; split; [exact Hc |].
      split; [apply EQ_refl | rewrite Ec; exact E].
Qed.
Theorem universe_equinumerous_omega i : equinumerous (U i) omega_codes.
Proof. exists (counting_graph i); apply counting_bijection. Qed.
Theorem universes_equinumerous i j : equinumerous (U i) (U j).
Proof.
  eapply equinumerous_trans; [apply universe_equinumerous_omega |].
  apply equinumerous_sym, universe_equinumerous_omega.
Qed.
Theorem finite_carrier_embeds_omega n : embeds (finite_carrier n) omega_codes.
Proof.
  exists (graph (finite_carrier n) (fun x => x)). apply graph_injection.
  - intros x y E; exact E.
  - intros x Hx. apply finite_carrier_membership in Hx as [k [_ E]].
    apply omega_membership. exists k; exact E.
  - intros x y Hx Hy E; exact E.
Qed.
Theorem counting_forward i c : Allowed i c ->
  EQ (apply_set (counting_graph i) (repr c)) (numeral (slot i c)).
Proof.
  intro Hc. apply (function_value (U i) omega_codes).
  - exact (proj1 (counting_bijection i)).
  - apply counting_graph_application. exists c; split; [exact Hc |].
    split; apply EQ_refl.
Qed.
Theorem counting_roundtrip i x : IN x (U i) ->
  EQ (apply_set (inverse (U i) omega_codes (counting_graph i))
        (apply_set (counting_graph i) x)) x.
Proof. intro Hx. apply inverse_left; [apply counting_bijection | exact Hx]. Qed.

Lemma embeds_equal_domain A A' B : EQ A A' -> embeds A B -> embeds A' B.
Proof.
  intros E [f Hf]. exists (graph A' (apply_set f)). apply graph_injection.
  - intros x y Exy. apply apply_set_extensional; [apply EQ_refl | exact Exy].
  - intros x Hx. apply (apply_set_typed A (fun _ => B)); [exact (proj1 Hf) |].
    exact (IN_sound_right x A' A (EQ_sym _ _ E) Hx).
  - intros x y Hx Hy Exy. apply (injection_values A B f x y Hf).
    + exact (IN_sound_right x A' A (EQ_sym _ _ E) Hx).
    + exact (IN_sound_right y A' A (EQ_sym _ _ E) Hy).
    + exact Exy.
Qed.
Definition countable_zero (higher : nat -> Ens) n :=
  match n with 0 => omega_codes | S j => higher j end.
Theorem rank_zero_decoding_bound higher a :
  IN a (U 0) -> embeds (El (countable_zero higher) a) omega_codes.
Proof.
  intro Ha. apply universe_membership in Ha as [c [Hc E]].
  assert (Ev : EQ (El (countable_zero higher) a) (code_value (countable_zero higher) c)).
  { eapply EQ_tran; [apply decoding_extensional; exact E | apply decode_repr]. }
  eapply embeds_equal_domain; [apply EQ_sym; exact Ev |].
  destruct c as [n|j|j]; cbn [code_value].
  - apply finite_carrier_embeds_omega.
  - cbn [Allowed] in Hc. assert (j = 0) by lia. subst j; cbn [countable_zero].
    destruct (equinumerous_refl omega_codes) as [f [Hf [Hi Hs]]].
    exists f; split; assumption.
  - exists (counting_graph j). destruct (counting_bijection j) as [Hf [Hi Hs]].
    split; assumption.
Qed.

Print Assumptions slot_injective.
Print Assumptions slot_surjective.
Print Assumptions counting_bijection.
Print Assumptions universe_equinumerous_omega.
Print Assumptions universes_equinumerous.
Print Assumptions finite_carrier_embeds_omega.
Print Assumptions counting_forward.
Print Assumptions counting_roundtrip.
Print Assumptions embeds_equal_domain.
Print Assumptions rank_zero_decoding_bound.
Check counting_bijection.
Check counting_roundtrip.
Check rank_zero_decoding_bound.
