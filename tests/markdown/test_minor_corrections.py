import importlib.util
from pathlib import Path
import sys
import unittest

root=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(root/'tools/prose-review/scripts'))
import split_minor as minor
import review


class MinorCorrectionsTests(unittest.TestCase):
    def test_quoted_critic_preserves_source_and_accepted_text(self):
        marked = 'Thus `{++the ++}`result `{~~holds~>follows~~}`.'
        self.assertEqual(review.reject(marked), 'Thus result holds.')
        self.assertEqual(review.accept(marked), 'Thus the result follows.')
        self.assertEqual(review.quote_critic(marked), marked)

    def test_compact_report_attribution_and_checkboxes(self):
        self.assertEqual(review.provider_label(['Grazie cloud', 'Grazie IDE (local)', 'DeepL Write']),
                         'Grazie & DeepL Write')
        for name in ('MINOR_CORRECTIONS.md', 'WORDING_SUGGESTIONS.md'):
            report=(root/'latex'/name).read_text()
            self.assertNotIn('Grazie cloud',report)
            self.assertNotIn('Grazie local',report)
            self.assertNotIn('] Review',report)
            for block in report.split('\n## ')[1:]:
                self.assertRegex(block,r'^PTS-rk\.tex:\d+-\d+ · .+ · Suggested by ')
                self.assertRegex(block,r'\n\n- \[[ x]\] [^\n]*\S')
                for match in review.CRITIC.finditer(block):
                    self.assertEqual(block[match.start()-1], '`')
                    self.assertEqual(block[match.end()], '`')

    def test_only_commas_and_articles(self):
        for old,new in [('Thus','Thus,'),('','the '),('an','the'),('Situation','The situation'),('Levin,','Levin')]:
            self.assertTrue(minor.is_minor(old,new),(old,new))
        for old,new in [('iff','if'),('Thus','thus'),('normalisation','normalization'),('least','fewest'),('A $t$','The $t$')]:
            self.assertFalse(minor.is_minor(old,new),(old,new))

    def test_checked_report_exactly_restores_baseline(self):
        source='Title\n\nThe result holds.\n'
        report='# Minor corrections\n\n## Test · lines 3–3\n\n- [x] Implemented\n\n{++The ++}result holds.\n'
        self.assertEqual(minor.restore_minor(source,report),'Title\n\nresult holds.\n')

    def test_nonminor_report_cannot_bypass_content_check(self):
        report='# Minor corrections\n\n## Test · lines 1–1\n\n- [x] Implemented\n\n{~~least~>fewest~~} sets.\n'
        with self.assertRaises(ValueError):
            minor.restore_minor('fewest sets.\n',report)

    def test_stale_or_unimplemented_report_fails(self):
        report='# Minor corrections\n\n## Test · lines 1–1\n\n- [x] Implemented\n\n{++the ++}result.\n'
        with self.assertRaises(ValueError):
            minor.restore_minor('result.\n',report)

    def test_pending_excerpts_match_current_source(self):
        source=(root/'latex/PTS-rk.tex').read_text().splitlines()
        for header,marked in minor.passages((root/'latex/WORDING_SUGGESTIONS.md').read_text()):
            a,b=minor.line_range(header)
            self.assertEqual(review.reject(marked),'\n'.join(source[a-1:b]),header)

    def test_every_minor_passage_checked_and_present(self):
        source=(root/'latex/PTS-rk.tex').read_text()
        report=(root/'latex/MINOR_CORRECTIONS.md').read_text()
        self.assertNotIn('- [ ]',report)
        self.assertNotEqual(minor.restore_minor(source,report),source)
