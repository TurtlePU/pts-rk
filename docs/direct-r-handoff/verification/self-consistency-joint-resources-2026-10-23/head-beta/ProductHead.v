From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Reduction DefEq AbstractRewriting.
From Interpretation_of_R Require Import DirectRKernel DirectREval.
Import Core.

Fixpoint product_head_step {n} (t : Term nat n) : option (Term nat n) :=
  match t with
  | Π A B => option_map (Π A) (product_head_step B)
  | _ => RkEval.head_step t
  end.
Lemma product_head_step_sound {n} (t u : Term nat n) :
  product_head_step t = Some u -> t →ᵝ u.
Proof.
  revert u; induction t; intros u H;
    try (exact (RkEval.head_step_sound _ _ H)).
  cbn [product_head_step] in H.
  destruct (product_head_step t2) as [b|] eqn:E; [|discriminate].
  injection H; intro; subst u; apply step_pi_right, IHt2; reflexivity.
Qed.
Lemma product_head_step_equiv {n} (t u : Term nat n) :
  product_head_step t = Some u -> u =ᵝ t.
Proof. intro H; symmetry; apply eq_in, product_head_step_sound, H. Qed.
Print Assumptions product_head_step_sound.
Print Assumptions product_head_step_equiv.
