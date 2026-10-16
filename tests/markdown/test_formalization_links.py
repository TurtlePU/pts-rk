import importlib.util
from pathlib import Path
import sys
import unittest

tools = Path(__file__).resolve().parents[2] / 'tools'
sys.path.insert(0, str(tools))
spec = importlib.util.spec_from_file_location('paper_check', tools / 'check-markdown-paper.py')
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)


class FormalizationTests(unittest.TestCase):
    def test_explicit_author_math_change_is_exact_and_unique(self):
        edit = dict(before='$x$ then $y$', after='$x$', math_change=True)
        self.assertEqual(check.approved_math_baseline(['$z$', '$x$', '$y$'], [edit]),
                         ['$z$', '$x$'])
        self.assertEqual(check.approved_math_baseline(['$x$', '$y$'],
                         [dict(before='$x$ then $y$', after='$x$')]), ['$x$', '$y$'])
        for fragments in (['$x$'], ['$x$', '$y$', '$x$', '$y$']):
            with self.assertRaises(ValueError):
                check.approved_math_baseline(fragments, [edit])

    def test_numeric_vertical_spacing_is_presentation_only(self):
        self.assertEqual(check.body_stream(r'Before\vspace{-1em}After'),
                         check.body_stream('BeforeAfter'))
        self.assertEqual(check.body_stream(r'Before\vspace{-.5em}After'),
                         check.body_stream('BeforeAfter'))
        self.assertNotEqual(check.body_stream(r'Before\vspace{important}After'),
                            check.body_stream('BeforeAfter'))

    def test_paper_metadata_order(self):
        import re
        source = (tools.parent / 'latex/paper-markdown.tex').read_text()
        header = source.split(':::Abstract', 1)[0]
        self.assertEqual(re.findall(r'(?m)^([a-z]+):', header),
                         ['title', 'author', 'formalization', 'date'])

    def expand(self, body, roots='  rocq-ai: https://example.org/theories/'):
        return check.expand_formalization_links('title: T\nformalization:\n' + roots +
                                                '\n\n:::Abstract' + body)

    def test_relative_anchor(self):
        self.assertEqual(self.expand(r'\formalized{rocq-ai:A.v\#L13}'),
                         r'\rocqformalised{https://example.org/theories/A.v\#L13}')

    def test_absolute_override(self):
        self.assertEqual(self.expand(r'\proof{rocq-ai:https://other.org/a}'),
                         r'\rocqproof{https://other.org/a}')

    def test_revision_alias(self):
        self.assertEqual(self.expand(r'\proof{rocq:A.v}',
                                    '  rocq: https://old.org/'),
                         r'\rocqproof{https://old.org/A.v}')

    def test_other_assistants(self):
        for assistant in ('agda', 'lean'):
            self.assertIn('\\' + assistant + 'proof{https://example.org/A}',
                          self.expand('\\proof{' + assistant + ':A}',
                                      '  ' + assistant + ': https://example.org/'))

    def test_invalid_links_fail_closed(self):
        for body in (r'\proof{unknown:A.v}', r'\formalized{rocq-ai:}',
                     r'\formalized{A.v}'):
            with self.assertRaises(ValueError):
                self.expand(body)

    def test_duplicate_roots_fail(self):
        with self.assertRaises(ValueError):
            self.expand('', '  rocq-ai: https://a.org/\n  rocq-ai: https://b.org/')

    def test_paper_preserves_all_badge_targets(self):
        root = tools.parent
        old = (root / 'latex/paper.tex').read_text()
        new = check.expand_formalization_links(check.native_tex(
            (root / 'latex/paper-markdown.tex').read_text()))
        import re
        pattern = r'\\rocq(formalised|proof)\{([^}]+)\}'
        self.assertEqual(re.findall(pattern, old), re.findall(pattern, new))
