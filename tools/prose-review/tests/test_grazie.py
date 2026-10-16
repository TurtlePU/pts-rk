import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location('grazie_normalize', Path(__file__).parents[1]/'scripts/grazie-normalize.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class GrazieTests(unittest.TestCase):
    def test_bold_projection(self):
        self.assertEqual(module.projection('A **closed** *term*.')[0], 'A closed term.')
    def fixture(self):
        record = dict(id='L1', input='- *We* 😀 has evidence.', source='- *We* 😀 has\nevidence.', line=1, end_line=2)
        manifest = dict(source_sha256='hash', records=[record])
        part = dict(type='Change', range=dict(start=6, endExclusive=9), text='have')
        sentence = dict(sentence='We 😀 has evidence.', problems=[dict(fixes=[dict(parts=[part])])])
        raw = dict(source_sha256='hash', records=[dict(id='L1', input=record['input'], status=200, body=dict(corrections=[sentence]))])
        return manifest, raw

    def test_markdown_and_utf16(self):
        manifest, raw = self.fixture()
        result = module.normalize(manifest, raw)
        self.assertEqual(result['records'][0]['output'], '- *We* 😀 have evidence.')
        self.assertEqual(result['records'][0]['source'], '- *We* 😀 has\nevidence.')

    def test_partial_response_rejected(self):
        manifest, raw = self.fixture()
        raw['records'][0]['body']['corrections'][0]['sentence'] = 'has evidence.'
        with self.assertRaises(ValueError):
            module.normalize(manifest, raw)

    def test_changed_input_rejected(self):
        manifest, raw = self.fixture()
        raw['records'][0]['input'] += ' extra'
        with self.assertRaises(ValueError):
            module.normalize(manifest, raw)

    def test_unverified_status_rejected(self):
        manifest, raw = self.fixture()
        raw['records'][0]['status'] = 429
        with self.assertRaises(ValueError):
            module.normalize(manifest, raw)

    def test_display_parts_not_edits(self):
        manifest, raw = self.fixture()
        parts = raw['records'][0]['body']['corrections'][0]['problems'][0]['fixes'][0]['parts']
        parts.insert(0, dict(type='Context', text='We'))
        parts.append(dict(type='Skip'))
        self.assertEqual(module.normalize(manifest, raw)['records'][0]['output'], '- *We* 😀 have evidence.')

    def test_fix_spanning_placeholder_rejected(self):
        text = 'PROTECTED1X1 are countable.'
        manifest = dict(source_sha256='hash', records=[dict(id='L1', input=text)])
        part = dict(type='Change', range=dict(start=0,endExclusive=len(text)), text='PROTECTED1X1 is countable.')
        raw = dict(source_sha256='hash', records=[dict(id='L1',input=text,status=200,
                   body=dict(corrections=[dict(sentence=text,problems=[dict(fixes=[dict(parts=[part])])])]))])
        result = module.normalize(manifest,raw)
        self.assertEqual(result['records'], [])
        self.assertEqual(result['skipped'][0]['reason'], 'protected-fix-span')
