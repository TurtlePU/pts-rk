(** Faithful finite-choice quotation in the ORIGINAL annotated syntax.
    Separation uses beta computation and confluence, without a model,
    a consistency premise, or any assumption about arbitrary inhabitants. *)
From PTSrk Require Import Syntax Reduction DefEq AbstractRewriting.
From PTSrk.Combinatory Require Import ChurchFinite FiniteHornChurch.
From PTSrk.SelfConsistency Require Import StructuralCodes.

Module FiniteSelectorSeparation.
Module CF := ChurchFinite.ChurchFinite.
Module FC := FiniteHornChurch.FiniteHornChurch.

Lemma fin_number_injective {k} (i j : Fin k) :
  fin_number i = fin_number j -> i = j.
Proof.
  intro H; pose proof (fin_roundtrip i) as E.
  rewrite H, fin_roundtrip in E; congruence.
Qed.

(** Dispatch to distinct sort LABELS is an untyped syntactic test.  No
    typing assertion about this separating test is needed or claimed. *)
Theorem selector_syntax_injective {n} r k (i j : Fin k) :
  @CF.selector n r k i = CF.selector r k j -> i = j.
Proof.
  intro H.
  pose proof (@CF.selector_dispatch_beta n r k i (𝓤 0)
    (fun z => 𝓤 (fin_number z))) as Hi.
  pose proof (@CF.selector_dispatch_beta n r k j (𝓤 0)
    (fun z => 𝓤 (fin_number z))) as Hj.
  rewrite H in Hi.
  pose proof (@FC.normal_outputs_equal n _ _ _ Hi Hj eq_refl eq_refl) as E.
  injection E as E; apply fin_number_injective; exact E.
Qed.

Theorem selector_equiv_injective {n} r k (i j : Fin k) :
  def_equiv nat n (CF.selector r k i) (CF.selector r k j) -> i = j.
Proof.
  intro H; apply (@selector_syntax_injective n r k i j).
  apply def_equiv_prop in H; destruct H as [w [Hi Hj]].
  transitivity w.
  - apply FC.normal_reduct_equal; [apply CF.selector_normal | exact Hi].
  - symmetry; apply FC.normal_reduct_equal; [apply CF.selector_normal | exact Hj].
Qed.

Theorem selector_equiv_iff {n} r k (i j : Fin k) :
  def_equiv nat n (CF.selector r k i) (CF.selector r k j) <-> i = j.
Proof.
  split; [apply selector_equiv_injective | intro H; subst j; reflexivity].
Qed.

End FiniteSelectorSeparation.
