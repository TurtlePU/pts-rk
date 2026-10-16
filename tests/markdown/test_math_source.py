"""Run with python3 -m unittest discover -s tests/markdown -p 'test_*.py'."""
import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools'))
from paper_math import formula, format_source, normalize_notation, math_layout


class MathSourceTests(unittest.TestCase):
    def test_requested_judgment(self):
        self.assertEqual(formula(r"Γ ⊢ t : T\quad⟺\quad ∃ T', r.\;(Γ⊢T:r) ∧ (T=_βT') ∧ (Γ⊢t⇒T')."),
                         r"Γ ⊢ t : T \quad ⟺ \quad ∃ T', r.\;(Γ ⊢ T : r) ∧ (T =_β T') ∧ (Γ ⊢ t ⇒ T').")

    def test_operator_scripts(self):
        self.assertEqual(formula(r't→ _ β ^ ∗u'), 't →_β^∗ u')
        self.assertEqual(formula(r'a≤^{+}b'), 'a ≤^{+} b')

    def test_nonbinary_scripts(self):
        self.assertEqual(formula('N^+ = S^∗'), 'N^+ = S^∗')
        self.assertEqual(formula('x^{a+b}'), 'x^{a + b}')

    def test_unary_minus(self):
        self.assertEqual(formula('(-x)+y_{j-1}'), '(-x) + y_{j - 1}')

    def test_commas_and_explicit_spacing(self):
        self.assertEqual(formula(r'(x ,y)\,z'), r'(x, y)\,z')

    def test_text_arguments(self):
        self.assertEqual(formula(r'a=\text{a:b, c}'), r'a = \text{a:b, c}')

    def test_notation(self):
        self.assertEqual(normalize_notation(r'\mathsf{rk}_r+\rk0+\mathcal{N}_{j+1}'),
                         r'\rk{r}+\rk{0}+ℕ_{j+1}')
        self.assertEqual(normalize_notation(r'\mathsf{rk}_{\max(r+1,s)}'),
                         r'\rk{\max(r+1,s)}')

    def test_preserve_listings(self):
        s = '```agda\nx=y\n```\n\n$x=y$\n'
        self.assertEqual(format_source(s), '```agda\nx=y\n```\n\n$x = y$\n')

    def test_offside_fence_boundary(self):
        s = ':::Lemma\n%mathpar\n  Γ⊢x:T\n:::\n'
        self.assertEqual(format_source(s), ':::Lemma\n%mathpar\n  Γ ⊢ x : T\n:::\n')
        self.assertEqual(format_source(format_source(s)), format_source(s))

    def test_align_row_break(self):
        self.assertEqual(formula(r'a→\\&b'), r'a → \\ & b')

    def test_environment_alignment(self):
        source = '\\left\\{\\begin{array}{l}\n        x \\\\\n        y\n    \\end{array}\\right.'
        expected = '\\left\\{\n\\begin{array}{l}\n  x \\\\\n  y\n\\end{array}\\right.'
        self.assertEqual(math_layout(source), expected)
        self.assertEqual(math_layout(expected), expected)

    def test_leading_row_break(self):
        self.assertEqual(math_layout('  \\\\ x'), '  \\\\\n  x')

    def test_fraction_arguments(self):
        source = '\\dfrac{x \\quad\n        y}{z}'
        expected = '\\dfrac{x \\quad\n       y}\n      {z}'
        self.assertEqual(math_layout(source), expected)
        self.assertEqual(math_layout(expected), expected)

    def test_short_fraction_numerator(self):
        source = '\\dfrac\n  {Γ, Δ ⊢ t : T}\n  {Γ, x : U, Δ ⊢ t : T}.'
        expected = '\\dfrac{Γ, Δ ⊢ t : T}\n      {Γ, x : U, Δ ⊢ t : T}.'
        self.assertEqual(math_layout(source), expected)
        self.assertEqual(math_layout(expected), expected)

    def test_long_fraction_premise_breaks(self):
        source = r"\dfrac{Γ, x : U, Δ ⊢ t : T \quad ⊢ Γ, x : U, Δ \quad U →_β U'}{Γ, x : U', Δ ⊢ t : T}"
        expected = ("\\dfrac{Γ, x : U, Δ ⊢ t : T \\quad\n"
                    "       ⊢ Γ, x : U, Δ \\quad\n"
                    "       U →_β U'}\n"
                    "      {Γ, x : U', Δ ⊢ t : T}")
        self.assertEqual(math_layout(source), expected)
        self.assertEqual(math_layout(expected), expected)

    def test_multiple_inference_premises(self):
        source = '\\inferrule[Rule]{A \\\\\n    B}{C}\n      condition'
        expected = '\\inferrule[Rule]\n  {A \\\\ B}\n  {C}\n      condition'
        self.assertEqual(math_layout(source), expected)
        self.assertEqual(math_layout(expected), expected)

    def test_short_inference_rules_unchanged(self):
        for source in ('\\inferrule{A}{B}', '\\inferrule{A}\n    {B}'):
            self.assertEqual(math_layout(source), source)

    def test_environment_set_continuations(self):
        source = '\\begin{array}{c}\n  S = \\{\n    a, b\n  \\}\n\\end{array}'
        self.assertEqual(math_layout(source), source)

    def test_tikzcd_cells_preserved(self):
        source = '%tikzcd\n  [ampersand replacement = \\&]\n    a \\&\n    b\n  \\\\\n    c \\&\n    d\n'
        self.assertEqual(format_source(source), source)


if __name__ == '__main__':
    unittest.main()
