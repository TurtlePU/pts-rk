#!/usr/bin/env python3
"""Positive controls and mutations of actual audit contracts; no proof edits."""
import unittest
from gates import additive_dune, additive_import, declaration_coverage, exact_inventory, closed_reports


class AuditGateTests(unittest.TestCase):
    old_dune = "(rocq.theory (name T) (modules Old) (theories Stdlib PTSrk))\n(alias (name audit) (deps Audit.vo))\n"
    new_dune = "(rocq.theory (name T) (modules Old New Focus) (theories Stdlib PTSrk))\n(alias (name audit) (deps Audit.vo))\n(alias (name focus) (deps Focus.vo))\n"
    sources = [("New", "Lemma alpha : True. Proof. exact I. Qed.\nTheorem beta : True. Proof. exact I. Qed.\n")]
    checks = "Check New.New.alpha.\nCheck New.New.beta.\nPrint Assumptions New.New.alpha.\nPrint Assumptions New.New.beta.\n"
    summary = "CONTEXT SUMMARY\n===============\n* Axioms:\n    inherited.axiom\n* Constants/Inductives relying on type-in-type: <none>\n* Constants/Inductives relying on unsafe (co)fixpoints: <none>\n* Inductives whose positivity is assumed: <none>\n"

    def test_registration_positive(self):
        additive_dune(self.old_dune, self.new_dune, ["New"], "Focus", "focus")

    def test_existing_module_deletion_rejected(self):
        with self.assertRaises(ValueError):
            additive_dune(self.old_dune, self.new_dune.replace("Old ", ""), ["New"], "Focus", "focus")

    def test_dependency_change_rejected(self):
        with self.assertRaises(ValueError):
            additive_dune(self.old_dune, self.new_dune.replace("Stdlib PTSrk", "Stdlib"), ["New"], "Focus", "focus")

    def test_duplicate_registration_rejected(self):
        with self.assertRaises(ValueError):
            additive_dune(self.old_dune, self.new_dune.replace("New Focus", "New New Focus"), ["New"], "Focus", "focus")

    def test_missing_alias_rejected(self):
        with self.assertRaises(ValueError):
            additive_dune(self.old_dune, self.new_dune.replace("(alias (name focus) (deps Focus.vo))", ""), ["New"], "Focus", "focus")

    def test_old_audit_positive(self):
        old = "Lemma old : True. Proof. exact I. Qed.\n"
        additive_import(old, "From PTSrk.SelfConsistency Require Import Focus.\n" + old, "Focus")

    def test_old_audit_body_change_rejected(self):
        with self.assertRaises(ValueError):
            additive_import("Lemma old : True.\n", "From PTSrk.SelfConsistency Require Import Focus.\nLemma old : False.\n", "Focus")

    def test_coverage_positive(self):
        self.assertEqual(len(declaration_coverage(self.sources, self.checks)), 2)

    def test_missing_print_rejected_even_with_extra_check(self):
        with self.assertRaises(ValueError):
            declaration_coverage(self.sources, self.checks.replace("Print Assumptions New.New.beta.\n", ""))

    def test_missing_check_rejected_even_with_all_prints(self):
        with self.assertRaises(ValueError):
            declaration_coverage(self.sources, self.checks.replace("Check New.New.beta.\n", ""))

    def test_duplicate_report_rejected(self):
        with self.assertRaises(ValueError):
            declaration_coverage(self.sources, self.checks + "Print Assumptions New.New.alpha.\n")

    def test_inventory_positive(self):
        exact_inventory("pristine banner\n" + self.summary, "different banner\n" + self.summary)

    def test_extra_axiom_rejected(self):
        with self.assertRaises(ValueError):
            exact_inventory(self.summary, self.summary.replace("inherited.axiom", "inherited.axiom\n    hidden.axiom"))

    def test_unsafe_flag_rejected(self):
        changed = self.summary.replace("unsafe (co)fixpoints: <none>", "unsafe (co)fixpoints: sneaky")
        with self.assertRaises(ValueError):
            exact_inventory(changed, changed)

    def test_duplicate_summary_rejected(self):
        with self.assertRaises(ValueError):
            exact_inventory(self.summary, self.summary + self.summary)

    def test_closed_count_positive(self):
        self.assertEqual(closed_reports("Closed under the global context\n" * 2, 2), 2)

    def test_missing_closed_report_rejected(self):
        with self.assertRaises(ValueError):
            closed_reports("Closed under the global context\n", 2)

    def test_extra_assumption_rejected(self):
        with self.assertRaises(ValueError):
            closed_reports("Closed under the global context\nAxioms:\n sneaky\n", 1)


if __name__ == "__main__":
    unittest.main(verbosity=2)
