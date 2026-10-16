import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest

spec=importlib.util.spec_from_file_location('review',Path(__file__).parents[1]/'scripts/review.py')
review=importlib.util.module_from_spec(spec);spec.loader.exec_module(review)
TERMS=review.re.compile(review.TERMS,review.re.I)


class ReviewTests(unittest.TestCase):
    def test_surname_correction_rejected(self):
        raw = "Coquand's calculus is useful."
        result = review.mark_changes(dict(source=raw,input=raw,output="Copland's calculus is useful."),TERMS,review.EXCLUDED,names=['Coquand'])
        self.assertEqual(result,(None,'proper-name'))

    def test_name_identity_preserved_with_possessive_and_punctuation(self):
        raw = "Coquand's result is useful however."
        marked,status = review.mark_changes(dict(source=raw,input=raw,output="Coquand's result is useful, however."),TERMS,review.EXCLUDED,names=['Coquand'])
        self.assertEqual(status,'retained')
        self.assertEqual(review.reject(marked),raw)

    def test_combine_disjoint_edits(self):
        combined = review.combine_disjoint('{~~We~>They~~} use info.', 'We use {~~info.~>information.~~}')
        self.assertEqual(review.reject(combined), 'We use info.')
        self.assertEqual(review.accept(combined), 'They use information.')

    def test_conflicting_alternatives_not_combined(self):
        self.assertIsNone(review.combine_disjoint('{~~We~>They~~} use info.', '{~~We~>You~~} use info.'))

    def marked(self,source,before,after):
        return review.mark_changes(dict(source=source,input=before,output=after),TERMS,review.EXCLUDED)

    def test_source_flow_and_reject(self):
        raw='We need necessary info\nto explain the result.'
        marked,status=self.marked(raw,raw.replace('\n',' '),'We need necessary information to explain the result.')
        self.assertEqual(status,'retained')
        self.assertEqual(review.reject(marked),raw)
        self.assertIn('\nto explain',marked)
        self.assertIn('{~~info~>information~~}',marked)

    def test_multiline_replacement_roundtrip(self):
        raw='One can\nvery easily see this.'
        marked,_=self.marked(raw,'One can very easily see this.','It is straightforward to see this.')
        self.assertEqual(review.reject(marked),raw)
        self.assertEqual(' '.join(review.accept(marked).split()),'It is straightforward to see this.')

    def test_shorter_replacement_does_not_create_a_critic_block_boundary(self):
        self.assertNotIn('\n\n',review.flow('Briefly','Several words\non three\nlines'))

    def test_oxford_only_edits_removed(self):
        self.assertEqual(self.marked('Normalization is formalized.','Normalization is formalized.','Normalisation is formalised.')[1],'no-safe-prose-edits')

    def test_not_every_is_word_is_a_variant(self):
        self.assertEqual(review.oxford('formalism, organism, characteristic, NORMALISATION'),
                         'formalism, organism, characteristic, NORMALIZATION')

    def test_no_invented_spelling_correction(self):
        raw='Specialising is useful.'
        self.assertEqual(self.marked(raw,raw,raw)[1],'no-safe-prose-edits')
        self.assertEqual(self.marked(raw,raw,'Specializing is useful.')[1],'no-safe-prose-edits')

    def test_other_oxford_variant_edits_removed(self):
        raw='We summarized behavior that we modeled.'
        self.assertEqual(self.marked(raw,raw,'We summarised behaviour that we modelled.')[1],'no-safe-prose-edits')

    def test_case_change_connected_to_insertion_is_retained(self):
        marked,_=self.marked('Characterization matters.','Characterization matters.','The characterization matters.')
        self.assertEqual(review.accept(marked),'The characterization matters.')
        self.assertEqual(review.reject(marked),'Characterization matters.')

    def test_technical_synonyms_rejected(self):
        for before,after in [('A total system.','A fully defined system.'),('It is inhabited.','It is occupied.'),('A full interpretation.','A complete interpretation.'),('All inputs work.','Some inputs work.')]:
            self.assertEqual(self.marked(before,before,after)[1],'technical-terminology')

    def test_partial_connected_rewrite_not_kept(self):
        raw='An old phrase for $x$ works.'
        self.assertIsNone(self.marked(raw,'An old phrase for MATH1X1 works.','An improved phrase (MATH1X1) works.')[0])

    def test_term_change_rejects_whole_passage(self):
        self.assertEqual(self.marked('The sorts are clearly useful.','The sorts are clearly useful.','These types are useful.')[1],'technical-terminology')

    def test_false_positive_removed(self):
        self.assertIsNone(self.marked('A redex reduces.','A redex reduces.','A FedEx reduces.')[0])

    def test_missing_placeholder(self):
        self.assertEqual(self.marked('Use $x$ here.','Use MATH1X1 here.','Use it here.')[1],'protected-content')

    def test_macro_and_code_not_changed(self):
        raw='The info for $x$ and %name{A} is here.'
        marked,_=self.marked(raw,'The info for PROTECTED1X1 and PROTECTED1X2 is here.','The information for PROTECTED1X1 and PROTECTED1X2 is here.')
        self.assertEqual(review.reject(marked),raw)
        self.assertIn('$x$ and %name{A}',marked)

    def test_insert_and_delete(self):
        for before,after in [('Turns out here.','It turns out here.'),('This is very clear.','This is clear.')]:
            marked,_=self.marked(before,before,after)
            self.assertEqual(review.reject(marked),before)
            self.assertEqual(' '.join(review.accept(marked).split()),after)

    def test_protect_suffix_and_punctuation(self):
        plain,mapping=review.protect('A $Π$-former [@key]) %foo{a {b}}.',4)
        self.assertEqual(plain,'A PROTECTED4X1-former PROTECTED4X2) PROTECTED4X3.')
        self.assertEqual(mapping['PROTECTED4X3'],'%foo{a {b}}')

    def test_other_math_and_macro_forms(self):
        text=r'A \(x + y\), $$z^2$$, \foo [a] {b}, \verb|code| and [site](https://example.org).'
        plain,mapping=review.protect(text,1)
        for literal in ('x + y','z^2','https://example.org','code'):
            self.assertNotIn(literal,plain)
        self.assertEqual(len(mapping),5)

    def test_comments_not_submitted(self):
        plain,mapping=review.protect('A sentence. % private note\nNext sentence.',1)
        self.assertEqual(plain,'A sentence. Next sentence.')

    def test_skip_raw_code_and_metadata(self):
        s='---\ntitle: Secret\n---\n# Text\n\nA useful\nparagraph.\n\n%mathpar\n  x = y\n\n```coq\nProof.\n```\n'
        records=review.prepare(s)['records']
        self.assertEqual(len(records),1)
        self.assertEqual(records[0]['source'],'A useful\nparagraph.')
        self.assertEqual(records[0]['input'],'A useful paragraph.')

    def test_plain_markdown(self):
        self.assertEqual(len(review.prepare('A paragraph.\n')['records']),1)

    def test_quoted_code_fences(self):
        source='# Header\n\n> ```text\n> $not prose$\n> ```\n\nA sentence.\n'
        records=review.prepare(source)['records']
        self.assertEqual([r['source'] for r in records],['A sentence.'])

    def test_stale_hash(self):
        with tempfile.TemporaryDirectory() as d:
            with self.assertRaises(ValueError):review.render('new',dict(source_sha256=review.digest('old')),Path(d)/'r.md')

    def rendered(self, source, records):
        with tempfile.TemporaryDirectory() as d:
            target = Path(d) / 'review.md'
            counts = review.render(source, dict(source_sha256=review.digest(source), records=records), target)
            return target.read_text(), counts

    def suggestion(self, provider, output, line=1, source='The info is here.'):
        return dict(id=provider, provider=provider, source=source, input=source,
                    output=output, line=line, end_line=line)

    def test_identical_provider_suggestions_collapsed(self):
        raw = 'The info is here.'
        records = [self.suggestion(p, 'The information is here.') for p in ('DeepL Write', 'Grazie cloud')]
        report, counts = self.rendered(raw, records)
        self.assertEqual(report.count('## '), 1)
        self.assertIn('Suggested by Grazie & DeepL Write', report)
        self.assertEqual(counts['duplicates-collapsed'], 1)
        self.assertIn('{~~info~>information~~}', report)

    def test_different_rewrites_remain_alternatives(self):
        records = [self.suggestion('DeepL', 'The information is here.'),
                   self.suggestion('Grazie', 'The details are here.')]
        report, counts = self.rendered('The info is here.', records)
        self.assertEqual(report.count('## '), 2)
        self.assertEqual(counts['duplicates-collapsed'], 0)

    def test_same_words_at_distinct_locations_not_collapsed(self):
        raw = 'The info is here.\n\nThe info is here.'
        report, _ = self.rendered(raw, [self.suggestion('A', 'The information is here.'),
                                        self.suggestion('B', 'The information is here.', line=3)])
        self.assertEqual(report.count('## '), 2)

    def test_different_placeholder_ids_same_correction_collapsed(self):
        raw = 'The info for $x$ is here.'
        records = [dict(id=p,provider=p,source=raw,line=1,end_line=1,
                        input=f'The info for {key} is here.',
                        output=f'The information for {key} is here.', mapping={key:'$x$'})
                   for p,key in [('DeepL','MATH1X1'),('Grazie','PROTECTED9X2')]]
        report, _ = self.rendered(raw, records)
        self.assertEqual(report.count('## '), 1)
        self.assertIn('Suggested by Grazie & DeepL Write', report)

    def test_merge_preserves_evidence_and_rejects_stale_provider(self):
        first=dict(source_sha256='a', records=[{'id':'x','provider':'DeepL'}])
        second=dict(source_sha256='a', records=[{'id':'x','provider':'Grazie'}])
        self.assertEqual(len(review.merge_results([first,second])['records']),2)
        self.assertEqual(len(first['records']),1)
        with self.assertRaises(ValueError):
            review.merge_results([first,dict(source_sha256='b',records=[])])

    def test_forged_record_source(self):
        raw='A sentence.'
        data=dict(source_sha256=review.digest(raw),records=[dict(id='x',line=1,end_line=1,source='Other text.',note='A note',provider='test')])
        with tempfile.TemporaryDirectory() as d:
            with self.assertRaises(ValueError):review.render(raw,data,Path(d)/'r.md')

    def test_legacy_paragraph_restructuring_is_not_guessed(self):
        raw='One.\n\nTwo.'
        data=dict(source_sha256=review.digest(raw),results=[dict(batch=1,status='returned',output='Combined.',paragraphs=[dict(line=1,end_line=1,input='One.'),dict(line=3,end_line=3,input='Two.')])])
        result=review.import_legacy(raw,data,None)
        self.assertEqual(result['records'],[])
        self.assertEqual(result['omitted_batches'],[1])

    def test_no_critic_across_paragraphs(self):
        old='One.\n\nTwo.'
        # Production records are paragraphs, not batches; fail closed if mixed.
        marked,_=self.marked(old,'One. Two.','Some other phrasing.')
        self.assertTrue(marked is None or '\n\n' not in next(iter(review.CRITIC.finditer(marked))).group())


if __name__=='__main__':unittest.main()
