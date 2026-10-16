"""Run with python3 -m unittest discover -s tests/markdown -p 'test_*.py'."""
import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools'))
from paper_math import formula, format_source, normalize_notation


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
                         r'\rk{r}+\rk{0}+\chNat{j+1}')
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


if __name__ == '__main__':
    unittest.main()
