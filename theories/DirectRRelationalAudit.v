(** Independent source/translation audit. Full deduction preservation remains
    open; the statements below do not claim that induction has been proved. *)
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DirectRCodes DirectRKernel
  DirectRRelationalSyntax DirectRRelationalTranslation DirectRRelationalAxioms DirectRRelationalGround.
Theorem relational_axiom_preservation : forall k n (Γ : Ctx nat n) env (A : Relational.formula k),
  Relational.axiom A -> exists p, @typ nat RankSorts n Γ p (RelationalTranslation.formula A env).
Proof. exact @RelationalAxioms.source_axiom_realized. Qed.
Check relational_axiom_preservation.
Print Relational.derives.
Check RelationalTranslation.formula_typed.
Check RelationalTranslation.term_admitted.
Check RelationalTranslation.instantiate_translation.
Check RelationalTranslation.universal_elimination.
Check RelationalGround.addition_true.
Check RelationalGround.addition_false.
Print Assumptions Relational.source_ex_falso.
Print Assumptions RelationalTranslation.term_typed.
Print Assumptions RelationalTranslation.term_admitted.
Print Assumptions RelationalTranslation.formula_typed.
Print Assumptions RelationalTranslation.formula_replace.
Print Assumptions RelationalTranslation.formula_rename.
Print Assumptions RelationalTranslation.formula_source_subst.
Print Assumptions RelationalTranslation.formula_source_rename.
Print Assumptions RelationalTranslation.instantiate_translation.
Print Assumptions RelationalTranslation.closed_term_translation.
Print Assumptions RelationalTranslation.implication_elimination.
Print Assumptions RelationalTranslation.universal_elimination.
Print Assumptions relational_axiom_preservation.
Print Assumptions RelationalGround.equality_true.
Print Assumptions RelationalGround.equality_false.
Print Assumptions RelationalGround.order_true.
Print Assumptions RelationalGround.order_false.
Print Assumptions RelationalGround.addition_true.
Print Assumptions RelationalGround.addition_false.
Print Assumptions RelationalGround.multiplication_true.
Print Assumptions RelationalGround.multiplication_false.
