"""Real false positives from the paper's DeepL/Grazie review."""
import importlib.util
from pathlib import Path
import re
import unittest

root = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('prose_review', root/'tools/prose-review/scripts/review.py')
review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review)


class PaperReviewFilteringTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        def inventory(name):
            return [s.strip() for s in (root/'tools/grazie'/name).read_text().splitlines()
                    if s.strip() and not s.startswith('#')]
        cls.names = inventory('protected-names.txt')
        terms = inventory('protected-terms.txt')
        cls.pattern = re.compile(review.TERMS+'|'+'|'.join(r'(?<!\w)'+re.escape(t)+r'(?!\w)' for t in terms), re.I)

    def test_real_name_and_terminology_rewrites_removed(self):
        for before, after in [
            ("Coquand's calculus.", "Copland's calculus."),
            ('The least sets.', 'The fewest sets.'),
            ('It holds iff this holds.', 'It holds if this holds.'),
            ('We strictify the hierarchy.', 'We stratify the hierarchy.'),
            ('It greedily applies redexes.', 'It applies redexes.'),
            ('A simply-typed value.', 'A simply typed value.'),
            ('Both yes-s hold.', 'Both yeses-s hold.'),
            ('The sorts are present.', 'The types are present.'),
        ]:
            with self.subTest(before=before):
                marked, _ = review.mark_changes(dict(source=before,input=before,output=after),self.pattern,review.EXCLUDED,self.names)
                self.assertIsNone(marked)

    def test_unchanged_surname_does_not_hide_legitimate_punctuation(self):
        before = "Levin's result is useful however."
        after = "Levin's result is useful, however."
        marked, reason = review.mark_changes(dict(source=before,input=before,output=after),self.pattern,review.EXCLUDED,self.names)
        self.assertEqual(reason,'retained')
        self.assertEqual(review.reject(marked),before)
