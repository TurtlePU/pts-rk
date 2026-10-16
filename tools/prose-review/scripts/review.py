#!/usr/bin/env python3
"""Prepare protected prose, collect service results, and render CriticMarkup."""
import argparse
import collections
import difflib
import hashlib
import json
from pathlib import Path
import re
import shlex
import subprocess

TERMS = r'\b(?:sorts?|types?|terms?|ranks?|axioms?|redex(?:es)?|PTS(?:-rk)?|Rocq|Coq|STLC|GCH|BZC|ZFC|TOWER|ELEMENTARY|normalization|normalizing|conversion|convertibility|cumulativity|hierarchy|cardinals?|universes?|inhabitants?|selectors?|telescopes?|total|functional|full|faithful|inhabited|atomic|strong|weak|normal|definitional|reflexive|transitive|symmetric|dependent|applications?|abstractions?|substitution|invariant|tests?|ground|uniform|representable|elementary|bounded|interpretation|interprets|proofs?|propositions?|provable|sound|consistent|consistency|convertible|functions?|all|every|any|only|some|each|unique|arbitrary|not|never)\b'
KEY = re.compile(r'(?:MATH|REF|PROTECTED)\d+X\d+')
EXCLUDED = {'fedex', 'fedexes'}
VARIANTS = ('normalis', 'formalis', 'realis', 'specialis', 'generalis',
            'totalis', 'diagonalis', 'characteris', 'organis', 'recognis',
            'minimis', 'maximis', 'optimis', 'initialis')
CRITIC = re.compile(r'\{~~([\s\S]*?)~>([\s\S]*?)~~\}|\{\+\+([\s\S]*?)\+\+\}|\{--([\s\S]*?)--\}|\{>>[\s\S]*?<<\}')


def load(path):
    return json.loads(Path(path).read_text())


def save(path, data):
    Path(path).write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')


def digest(source):
    return hashlib.sha256(source.encode()).hexdigest()


def argument(text, start):
    while start < len(text) and text[start].isspace():
        start += 1
    if start == len(text) or text[start] != '{':
        return start
    depth, i = 1, start + 1
    while i < len(text):
        if text[i] == '\\':
            i += 2
            continue
        depth += (text[i] == '{') - (text[i] == '}')
        i += 1
        if not depth:
            return i
    raise ValueError('Unclosed macro argument')


def protect(raw, line):
    mapping, pieces, i = {}, [], 0
    while i < len(raw):
        start = i
        if raw.startswith(('$$', r'\('),i):
            delimiter='$$' if raw.startswith('$$',i) else r'\)'
            end=raw.find(delimiter,i+2)
            if end<0:raise ValueError('Unclosed math delimiter')
            i=end+2
        elif raw[i] == '$':
            m = re.search(r'(?<!\\)\$', raw[i+1:])
            if not m:
                raise ValueError('Unclosed inline math')
            i += m.end() + 1
        elif raw[i] == '`':
            marker = re.match(r'`+', raw[i:])[0]
            end = raw.find(marker, i + len(marker))
            if end < 0:
                raise ValueError('Unclosed code span')
            i = end + len(marker)
        elif raw[i] in '%\\':
            if raw[i]=='%' and i+1<len(raw) and raw[i+1].isspace():
                i=raw.find('\n',i)
                if i<0:i=len(raw)
                continue
            m = re.match(r'[%\\](?:[A-Za-z]+|.)', raw[i:])
            i += len(m[0])
            if m[0] in (r'\verb',r'\lstinline'):
                if i<len(raw) and raw[i]=='*':i+=1
                if i==len(raw):raise ValueError('Missing verbatim delimiter')
                end=raw.find(raw[i],i+1)
                if end<0:raise ValueError('Unclosed verbatim span')
                i=end+1
            else:
                while i < len(raw):
                    j=i
                    while j<len(raw) and raw[j].isspace():j+=1
                    if j<len(raw) and raw[j]=='{':i=argument(raw,j)
                    elif j<len(raw) and raw[j]=='[':
                        end=raw.find(']',j)
                        if end<0:raise ValueError('Unclosed macro option')
                        i=end+1
                    else:break
        elif raw[i]=='[' and re.match(r'\[[^\]]+\]\(',raw[i:]):
            end=raw.find(')',i)
            if end<0:raise ValueError('Unclosed Markdown link')
            i=end+1
        elif raw.startswith(('[@', '<#', '<http', 'https://', 'http://'), i):
            if raw[i] == '[':
                end = raw.find(']', i)
            elif raw[i] == '<':
                end = raw.find('>', i)
            else:
                end = i + len(re.match(r'\S+', raw[i:])[0]) - 1
            if end < i:
                raise ValueError('Unclosed reference')
            i = end + 1
        else:
            pieces.append(raw[i]); i += 1
            continue
        key = f'PROTECTED{line}X{len(mapping)+1}'
        mapping[key] = raw[start:i]
        pieces.append(key)
    return re.sub(r'\s+', ' ', ''.join(pieces)).strip(), mapping


def prepare(source):
    lines = source.splitlines(keepends=True)
    records, i, fence = [], 0, None
    metadata = source.lstrip().startswith(('---', '\\documentclass'))
    while i < len(lines):
        value = lines[i].strip()
        if metadata:
            if value.startswith(':::') or re.match(r'^# ', value):
                metadata = False
            else:
                i += 1; continue
        code_value=re.sub(r'^>\s?', '', value)
        if code_value.startswith('```'):
            fence = None if fence else re.match(r'`+', code_value)[0]
            i += 1; continue
        if fence:
            i += 1; continue
        if re.match(r'^%(?:mathpar|align\*?|gather\*?|multline\*?|tikzcd|bnf)\s*$', value):
            indent = len(lines[i])-len(lines[i].lstrip()); i += 1
            while i < len(lines) and (not lines[i].strip() or len(lines[i])-len(lines[i].lstrip()) > indent):
                i += 1
            continue
        if value.startswith(('\\[', '\\begin{')):
            end = '\\]' if value.startswith('\\[') else '\\end{' + re.match(r'\\begin\{([^}]+)\}', value)[1] + '}'
            while i < len(lines):
                done = end in lines[i]; i += 1
                if done: break
            continue
        if not value or value.startswith((':::', '#', '%printbibliography')):
            i += 1; continue
        if lines[i][0].isspace():
            i += 1; continue
        start = i; i += 1
        while i < len(lines) and lines[i].strip() and not lines[i].startswith((':::', '#', '%', '\\[', '\\begin', '```', '- ', '> ')):
            i += 1
        raw = ''.join(lines[start:i]).rstrip('\n')
        prose, mapping = protect(raw, start+1)
        records.append(dict(id=f'L{start+1}', line=start+1, end_line=i,
                            source=raw, input=prose, mapping=mapping))
    return dict(source_sha256=digest(source), records=records)


def oxford(text):
    for stem in VARIANTS:
        text = re.sub(r'\b'+stem+r'(?:e[ds]?|ing|ation(?:s|al(?:ly)?)?|able|ability|ers?)\b',
                      lambda m: m[0][:len(stem)-1]+('Z' if m[0][len(stem)-1].isupper() else 'z')+m[0][len(stem):], text, flags=re.I)
    return text


def unquote_critic(markup):
    return re.sub(r'`(' + CRITIC.pattern + r')`', lambda m: m[1], markup)


def quote_critic(markup):
    return CRITIC.sub(lambda m: '`' + m[0] + '`', unquote_critic(markup))


def provider_label(providers):
    names = {'Grazie' if 'grazie' in p.lower() else
             'DeepL Write' if p.lower().startswith('deepl') else p for p in providers}
    return ' & '.join(sorted(names, key=lambda p: (p != 'Grazie', p)))


def reject(markup):
    markup = unquote_critic(markup)
    return CRITIC.sub(lambda m: m[1] if m[1] is not None else (m[4] or ''), markup)


def accept(markup):
    markup = unquote_critic(markup)
    return CRITIC.sub(lambda m: m[2] if m[1] is not None else (m[3] or ''), markup)


def flow(text, old):
    """Retain old-side newlines; use the same row word counts on the new side."""
    words = text.split()
    counts = [len(row.split()) for row in old.split('\n')]
    rows = []
    for count in counts[:-1]:
        rows.append(' '.join(words[:count])); words = words[count:]
    rows.append(' '.join(words))
    return '\n'.join(row for row in rows if row)


def mark_changes(record, term_pattern, excluded, names=()):
    raw, before = record['source'], record['input']
    if re.search(r'\n\s*\n',raw):return None, 'multiple-blocks'
    after = record['output']
    vocabulary={w.lower():w for w in re.findall(r'[A-Za-z]+',before)}
    def spelling_key(word):
        return oxford({'modeled':'modelled','modeling':'modelling',
                       'behavior':'behaviour','behaviors':'behaviours'}.get(word.lower(),word.lower()))
    def variant_key(word):
        return re.sub(r'is(ation(?:s|al(?:ly)?)?|e[ds]?|ing)\b',r'iz\1',spelling_key(word),flags=re.I)
    spellings={variant_key(word):word for word in vocabulary.values()}
    def keep_spelling(m):
        word=m[0]
        original=spellings.get(variant_key(word))
        if original and original.lower()!=word.lower():return original
        return word
    after=re.sub(r'[A-Za-z]+',keep_spelling,after)
    if names:
        name_pattern = re.compile('|'.join(r'(?<!\w)'+re.escape(n)+r'(?!\w)' for n in sorted(names,key=len,reverse=True)), re.I)
        identities = lambda s: [m[0].casefold() for m in name_pattern.finditer(s)]
        if identities(before) != identities(after):
            return None, 'proper-name'
    if any(marker in raw+after for marker in ('{~~', '{++', '{--', '{>>', '~>', '~~}')):
        return None, 'existing-critic-syntax'
    if any(w.lower() in excluded for w in re.findall(r'\b[\w-]+\b', after)):
        return None, 'excluded-word'
    counts = lambda s: collections.Counter(KEY.findall(s))
    if counts(before) != counts(after):
        return None, 'protected-content'
    concepts = lambda s: [m[0].lower() for m in term_pattern.finditer(oxford(s))]
    if concepts(before) != concepts(after):
        return None, 'technical-terminology'
    words = list(re.finditer(r'\S+', before))
    raw_words = list(re.finditer(r'\S+', raw))
    b, a, r = [m[0] for m in words], after.split(), [m[0] for m in raw_words]
    mapping = {}
    for block in difflib.SequenceMatcher(None, b, r, autojunk=False).get_matching_blocks():
        mapping.update((block.a+n, block.b+n) for n in range(block.size))
    edits = []
    changes=[change for change in difflib.SequenceMatcher(None,b,a,autojunk=False).get_opcodes() if change[0]!='equal']
    if all(' '.join(b[i:j]).casefold()==' '.join(a[k:l]).casefold() for _,i,j,k,l in changes):return None,'no-safe-prose-edits'
    for op, i, j, k, l in changes:
        old, new = ' '.join(b[i:j]), ' '.join(a[k:l])
        if KEY.search(old+' '+new) or term_pattern.search(old+' '+new): return None, 'technical-edit-span'
        if i == j:
            if i not in mapping: return None, 'ambiguous-source-edit'
            offset = raw_words[mapping[i]].start()
            edits.append((offset, offset, '{++'+new+' ++}'))
            continue
        if any(t not in mapping for t in range(i, j)): return None, 'ambiguous-source-edit'
        positions = [mapping[t] for t in range(i, j)]
        if positions != list(range(positions[0], positions[0]+j-i)): return None, 'ambiguous-source-edit'
        start, end = raw_words[positions[0]].start(), raw_words[positions[-1]].end()
        old_raw = raw[start:end]
        if any(c in old_raw+new for c in ('$', '\\', '%', '`', '*', '[@', '<#')): return None, 'protected-source-span'
        if new:
            markup = '{~~'+old_raw+'~>'+flow(new, old_raw)+'~~}'
        else:
            markup = '{--'+old_raw+'--}'
        edits.append((start, end, markup))
    if not edits: return None, 'no-safe-prose-edits'
    marked = raw
    for start, end, markup in sorted(edits, reverse=True):
        marked = marked[:start]+markup+marked[end:]
    if reject(marked) != raw:
        raise ValueError('CriticMarkup rejection changed source')
    return marked, 'retained'


def import_legacy(source, deepl, grazie):
    if digest(source) != deepl['source_sha256']:
        raise ValueError('Stale source hash')
    lines, records, omitted = source.splitlines(keepends=True), [], []
    for batch in deepl['results']:
        outputs = re.split(r'\n\s*\n', batch['output'].strip())
        if batch['status'] != 'returned' or len(outputs) != len(batch['paragraphs']):
            omitted.append(batch['batch']); continue
        for p, output in zip(batch['paragraphs'], outputs):
            raw = ''.join(lines[p['line']-1:p['end_line']]).rstrip('\n')
            records.append(dict(id=f"D{batch['batch']:02}-L{p['line']}",
                                provider='DeepL Write', line=p['line'], end_line=p['end_line'],
                                source=raw, input=p['input'], output=output))
    if grazie:
        for p in grazie['paragraphs']:
            for f in p['findings']:
                if not f['rule'].startswith('Style.'): continue
                # Exact source lines are supplied by the matched DeepL manifest.
                match = next((r for r in records if r['line'] == p['line']), None)
                if match:
                    records.append(dict(id='G-L'+str(p['line']), provider='Grazie local',
                                        line=p['line'], end_line=match['end_line'], source=match['source'],
                                        note='Consider splitting this long sentence.'))
    return dict(source_sha256=digest(source), records=records, omitted_batches=omitted,
                unavailable=['Grazie cloud: authenticated collection pending.'])


def combine_disjoint(first, second):
    """Combine independent edits only; conflicting alternatives remain separate."""
    if reject(first) != reject(second):
        return None
    def edits(marked):
        offset, previous, found = 0, 0, []
        for m in CRITIC.finditer(marked):
            offset += m.start()-previous
            old = reject(m[0])
            found.append((offset, offset+len(old), m[0]))
            offset += len(old)
            previous = m.end()
        return found
    left, right = edits(first), edits(second)
    for a, b, markup in right:
        if (a, b, markup) in left:
            continue
        if any(max(a,c) < min(b,d) or a == c or (a == b and c < a < d) or
               (c == d and a < c < b) for c,d,_ in left):
            return None
        left.append((a,b,markup))
    result = reject(first)
    for a,b,markup in sorted(left, reverse=True):
        result = result[:a]+markup+result[b:]
    return result


def render(source, data, output, terms=(), excluded=(), names=()):
    if data['source_sha256'] != digest(source):
        raise ValueError('Stale source hash')
    pattern = re.compile(TERMS+'|'+ '|'.join(r'(?<!\w)'+re.escape(t)+r'(?!\w)' for t in terms), re.I) if terms else re.compile(TERMS,re.I)
    report = ['# Wording suggestions', '', 'For discussion; no edits applied.', '',
              '[CriticMarkup](https://fletcher.github.io/MultiMarkdown-6/syntax/critic.html): `{~~old~>new~~}`, `{++addition++}`, `{--deletion--}`.', '']
    for status in data.get('unavailable',[]):report.extend([status,''])
    audit = collections.Counter()
    lines=source.splitlines(keepends=True)
    passages = {}
    for record in data['records']:
        if not (1<=record['line']<=record['end_line']<=len(lines)) or record['source']!=''.join(lines[record['line']-1:record['end_line']]).rstrip('\n'):
            raise ValueError('Record does not match the source lines: '+record['id'])
        if 'note' in record:
            marked = record['source']+'{>>'+record['note']+'<<}'
            if reject(marked) != record['source']: raise ValueError('Invalid comment')
            reason = 'retained-note'
        else:
            marked, reason = mark_changes(record,pattern,EXCLUDED|set(excluded),names)
        audit[reason] += 1
        if not marked: continue
        # Compare restored source edits, not service-specific placeholder IDs.
        # Do not collapse merely similar rewrites or different source locations.
        key = (record['line'], record['end_line'], marked)
        if key in passages:
            passage = passages[key]
            if record['provider'] not in passage['providers']:
                passage['providers'].append(record['provider'])
            audit['duplicates-collapsed'] += 1
        else:
            passages[key] = dict(record, providers=[record['provider']], marked=marked)
    compact = []
    for record in passages.values():
        combined = False
        for previous in compact:
            # Keep provider attributions exact; never invent cross-provider hybrids.
            if (record['line'],record['end_line'],record['providers']) != (previous['line'],previous['end_line'],previous['providers']):
                continue
            marked = combine_disjoint(previous['marked'],record['marked'])
            if marked is not None:
                previous['marked'] = marked
                audit['independent-edits-combined'] += 1
                combined = True
                break
        if not combined:
            compact.append(dict(record))
    for record in sorted(compact, key=lambda r: (r['line'],r['end_line'])):
        providers = provider_label(record['providers'])
        marked = record['marked']
        report += [f"## PTS-rk.tex:{record['line']}-{record['end_line']} · {record['id']} · Suggested by {providers}", '',
                   '- [ ] ' + quote_critic(marked), '']
    Path(output).write_text('\n'.join(report))
    save(str(output)+'.audit.json',dict(source_sha256=data['source_sha256'], counts=audit,
                                      omitted_batches=data.get('omitted_batches',[])))
    return audit


def merge_results(results):
    """Combine immutable provider records; collapse only after filtering."""
    if not results:
        raise ValueError('No provider results')
    digest = results[0]['source_sha256']
    if any(data['source_sha256'] != digest for data in results):
        raise ValueError('Provider results refer to different source snapshots')
    return dict(source_sha256=digest,
                records=[record for data in results for record in data['records']],
                unavailable=list(dict.fromkeys(status for data in results
                                               for status in data.get('unavailable', []))),
                omitted_batches=list(dict.fromkeys(batch for data in results
                                                   for batch in data.get('omitted_batches', []))))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    sub=parser.add_subparsers(dest='action',required=True)
    p=sub.add_parser('prepare');p.add_argument('source',type=Path);p.add_argument('--output',required=True)
    p=sub.add_parser('collect');p.add_argument('--manifest',required=True);p.add_argument('--provider',required=True);p.add_argument('--command',required=True);p.add_argument('--output',required=True)
    p=sub.add_parser('import-legacy');p.add_argument('--source',type=Path,required=True);p.add_argument('--deepl',required=True);p.add_argument('--grazie');p.add_argument('--output',required=True)
    p=sub.add_parser('render');p.add_argument('--source',type=Path,required=True);p.add_argument('--results',required=True);p.add_argument('--output',required=True);p.add_argument('--terms',type=Path);p.add_argument('--exclude',type=Path);p.add_argument('--names',type=Path)
    p=sub.add_parser('merge');p.add_argument('results',nargs='+');p.add_argument('--output',required=True)
    args=parser.parse_args()
    if hasattr(args,'source') and args.source.resolve()==Path(args.output).resolve():
        raise ValueError('Output must not overwrite the source document')
    if args.action=='prepare':save(args.output,prepare(args.source.read_text()))
    elif args.action=='merge':
        if any(Path(p).resolve()==Path(args.output).resolve() for p in args.results):
            raise ValueError('Merge output must not overwrite provider evidence')
        save(args.output,merge_results([load(p) for p in args.results]))
    elif args.action=='import-legacy':save(args.output,import_legacy(args.source.read_text(),load(args.deepl),load(args.grazie) if args.grazie else None))
    elif args.action=='collect':
        manifest=load(args.manifest)
        run=subprocess.run(shlex.split(args.command),input=json.dumps(manifest),text=True,capture_output=True,timeout=600)
        if run.returncode:raise SystemExit('Service adapter failed; no report generated')
        data=json.loads(run.stdout)
        if data['source_sha256']!=manifest['source_sha256'] or data['provider']!=args.provider:raise ValueError('Adapter provenance mismatch')
        originals={r['id']:r for r in manifest['records']}
        seen=set()
        for r in data['records']:
            if r['id'] in seen or r['id'] not in originals or r['input']!=originals[r['id']]['input']:raise ValueError('Mismatched service result')
            seen.add(r['id']);r.update({k:v for k,v in originals[r['id']].items() if k!='input'});r['provider']=args.provider
        if seen!=set(originals):raise ValueError('Incomplete service coverage')
        save(args.output,data)
    else:
        read=lambda p:[s.strip() for s in p.read_text().splitlines() if s.strip() and not s.startswith('#')] if p else []
        print(dict(render(args.source.read_text(),load(args.results),args.output,read(args.terms),read(args.exclude),read(args.names))))


if __name__=='__main__':main()
