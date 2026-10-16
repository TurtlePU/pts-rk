#!/usr/bin/env python3
"""Normalize observed Grazie cloud corrections; no network/authentication access."""
import argparse
import json
import re
from pathlib import Path


def projection(text):
    removed = set()
    if text.startswith(('- ', '* ')):
        removed.update((0, 1))
    for m in re.finditer(r'\*{1,2}([^*]+)\*{1,2}', text):
        removed.update(range(m.start(), m.start(1)))
        removed.update(range(m.end(1), m.end()))
    indices = [i for i in range(len(text)) if i not in removed]
    return ''.join(text[i] for i in indices), indices


def utf16_offset(text, offset):
    if not isinstance(offset, int) or offset < 0:
        raise ValueError('Invalid UTF-16 offset')
    encoded = text.encode('utf-16-le')
    if offset*2 > len(encoded):
        raise ValueError('Offset outside sentence')
    return len(encoded[:offset*2].decode('utf-16-le'))


def normalize(manifest, raw):
    if raw['source_sha256'] != manifest['source_sha256']:
        raise ValueError('Stale cloud evidence')
    originals = {r['id']: r for r in manifest['records']}
    records, skipped = [], []
    for result in raw['records']:
        original = originals[result['id']]
        if result['input'] != original['input'] or result['status'] != 200:
            raise ValueError('Unverified input or failed response')
        text = original['input']
        plain, indices = projection(text)
        sentences = result['body']['corrections']
        if ' '.join(' '.join(s['sentence'] for s in sentences).split()) != ' '.join(plain.split()):
            raise ValueError('Incomplete sentence coverage')
        cursor = 0
        for si, sentence in enumerate(sentences):
            content = sentence['sentence']
            start = plain.find(content.strip(), cursor)
            if start < 0:
                raise ValueError('Ambiguous sentence alignment')
            # Offsets refer to the complete sentence, including leading spacing.
            start -= len(content)-len(content.lstrip())
            cursor = start + len(content.rstrip())
            for pi, problem in enumerate(sentence['problems']):
                key = f"{original['id']}-S{si+1}-P{pi+1}"
                fixes = problem.get('fixes', [])
                if not fixes:
                    skipped.append(dict(id=key, reason='no-replacement', problem=problem))
                    continue
                edits = []
                for part in fixes[0]['parts']:
                    if part['type'] in ('Context', 'Skip'):
                        continue  # Display context, not a replacement operation.
                    if part['type'] != 'Change':
                        raise ValueError('Unknown Grazie fix part: '+part['type'])
                    a = start + utf16_offset(content, part['range']['start'])
                    b = start + utf16_offset(content, part['range']['endExclusive'])
                    if not 0 <= a <= b <= len(indices):
                        raise ValueError('Replacement outside input')
                    oa = indices[a] if a < len(indices) else len(text)
                    ob = indices[b-1]+1 if b > a else oa
                    if text[oa:ob] != plain[a:b]:
                        raise ValueError('Replacement crosses Markdown syntax')
                    edits.append((oa, ob, part['text']))
                edits.sort()
                if any(re.search(r'(?:MATH|REF|PROTECTED)\d+X\d+',text[a:b]+replacement)
                       for a,b,replacement in edits):
                    skipped.append(dict(id=key,reason='protected-fix-span',problem=problem))
                    continue
                if any(edits[i][1] > edits[i+1][0] for i in range(len(edits)-1)):
                    raise ValueError('Overlapping replacement parts')
                output = text
                for a, b, replacement in reversed(edits):
                    output = output[:a]+replacement+output[b:]
                records.append(dict(original, id=key, provider='Grazie cloud', output=output,
                                    rule=problem.get('info'), message=problem.get('message')))
    return dict(source_sha256=manifest['source_sha256'], records=records,
                skipped=skipped, checked_records=len(raw['records']), status=raw.get('status'))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('manifest', type=Path)
    p.add_argument('raw', type=Path)
    p.add_argument('output', type=Path)
    args = p.parse_args()
    if args.output.exists():
        p.error('Refusing to overwrite normalized evidence')
    data = normalize(json.loads(args.manifest.read_text()), json.loads(args.raw.read_text()))
    args.output.write_text(json.dumps(data, ensure_ascii=False, indent=2)+'\n')


if __name__ == '__main__':
    main()
