Require Import Stdlib.Program.Equality.
Require Import Stdlib.Relations.Relations.
Require Import Syntax.
Require Import AbstractRewriting.
Require Import Reduction.
Require Import Confluence.

Definition def_equiv L n: relation (Term L n) :=
  EquivClosure (step L n).
Infix "=ᵝ" := (def_equiv _ _)
  (at level 50, no associativity).

Theorem def_equiv_prop {L n} (t t': Term L n):
  t =ᵝ t' <-> exists u, t ↠ᵝ u /\ t' ↠ᵝ u.
Proof.
constructor; intro.
- induction H. exists x; repeat constructor.
  inversion H; subst; destruct IHRTC as [u []].
  + exists u. constructor; auto.
    apply rtc_step with (y := y); auto.
  + apply rtc_in in H1.
    apply (step_diamond _ _ _ H1) in H2.
    destruct H2 as [v []]. exists v. constructor. auto.
    apply rtc_trans with (y := u); auto.
- destruct H as [u []]. apply rtc_trans with (y := u).
  + apply rtc_map with (Q := step L n).
    intros. apply forward. auto. auto.
  + apply inv_rtc_inv, rtc_map with (Q := step L n).
    intros. apply backwards. auto. auto.
Qed.

Lemma equiv_𝓤_inversion {L n} ℓ ℓ':
  def_equiv L n (𝓤 ℓ) (𝓤 ℓ') -> ℓ = ℓ'.
Proof.
rewrite def_equiv_prop. intros [u [H H']].
inversion H; subst; try (inversion H0).
inversion H'. auto. inversion H0.
Qed.

Lemma equiv_Π_inversion {L n} (T T': Term L n)
  (U U': Term L (S n)):
  Π T U =ᵝ Π T' U' -> T =ᵝ T' /\ U =ᵝ U'.
Proof.
rewrite def_equiv_prop. intros [u [H1 H2]].
assert (H := H1). apply rtc_Π_repr in H.
destruct H as [T1 [U1 H]]. subst.
apply rtc_Π_inversion in H1, H2.
destruct H1 as [H1 H3]. destruct H2 as [H2 H4].
split; rewrite def_equiv_prop;
[exists T1 | exists U1]; auto.
Qed.

Lemma equiv_sub {L n} (f: Term L (S n))
  (t t': Term L n):
  t =ᵝ t' -> f ◁ t =ᵝ f ◁ t'.
Proof.
rewrite def_equiv_prop. intros [u [H H']].
rewrite def_equiv_prop. exists (f ◁ u).
constructor; apply rtc_sub; auto.
Qed.

Lemma rename_equiv {L m n}
  (f: Fin m -> Fin n) (t t': Term L m):
  t =ᵝ t' -> rename f t =ᵝ rename f t'.
Proof. intro. apply eq_unmap.
apply eq_map with (Q := step L m).
apply rename_step. assumption.
Qed.

Lemma replace_equiv {L m n}
  (f: Fin m -> Term L n) (t t': Term L m):
  t =ᵝ t' -> replace f t =ᵝ replace f t'.
Proof. intro. apply eq_unmap.
apply eq_map with (Q := step L m).
apply replace_step. assumption.
Qed.
