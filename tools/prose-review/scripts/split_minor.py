#!/usr/bin/env python3
"""Split reviewed comma/article edits; emit an inspectable apply_patch patch."""
import difflib
import re
from pathlib import Path
import review


def is_minor(old, new):
    if old == new or any(c in old+new for c in '$\\%`'):
        return False
    articles = lambda s: re.findall(r'\b(?:the|an|a)\b',s,re.I)
    if old.count(',') == new.count(',') and articles(old) == articles(new):
        return False
    def base(s):
        return re.sub(r'\s+',' ',re.sub(r'\b(?:the|an|a)\b','',s.replace(',',''),flags=re.I)).strip().casefold()
    return base(old) == base(new)


def passages(report, checked=False):
    separator = '\n\n- [x] Implemented\n\n' if checked else '\n\n- [ ] Review\n\n'
    for block in report.split('\n## ')[1:]:
        if separator in block:
            header, marked = block.split(separator,1)
        else:
            header, marked = block.split('\n\n- [' + ('x' if checked else ' ') + '] ',1)
        yield header, review.unquote_critic(marked.rstrip('\n'))


def line_range(header):
    match = re.search(r'(?:lines |PTS-rk\.tex:)(\d+)[–-](\d+)', header)
    if not match:
        raise ValueError('Missing source range: ' + header)
    return tuple(map(int, match.groups()))


def report_entry(header, marked, checked=False):
    if not header.startswith('PTS-rk.tex:'):
        identifier, providers, _ = header.split(' · ')
        first, last = line_range(header)
        header = f'PTS-rk.tex:{first}-{last} · {identifier} · Suggested by {review.provider_label(providers.split(" + "))}'
    return ['## ' + header, '', '- [' + ('x' if checked else ' ') + '] ' + review.quote_critic(marked), '']


def edits(marked, offset=0):
    previous=0
    for m in review.CRITIC.finditer(marked):
        offset += m.start()-previous
        old,new = review.reject(m[0]), review.accept(m[0])
        yield offset,offset+len(old),old,new,m[0]
        offset += len(old)
        previous=m.end()


def overlaps(a,b):
    return a[0] == b[0] or max(a[0],b[0]) < min(a[1],b[1]) or (a[0]==a[1] and b[0]<a[0]<b[1]) or (b[0]==b[1] and a[0]<b[0]<a[1])


def replace(text, changes, base=0, markup=False):
    for a,b,old,new,marked in sorted(changes,key=lambda e:(e[0],e[1]),reverse=True):
        assert text[a-base:b-base] == old
        text=text[:a-base]+(marked if markup else new)+text[b-base:]
    return text


def critic(before,after):
    a=list(re.finditer(r'\S+',before));b=after.split();changes=[]
    for op,i,j,k,l in difflib.SequenceMatcher(None,[m[0] for m in a],b,autojunk=False).get_opcodes():
        if op=='equal':continue
        start=a[i].start() if i<len(a) else len(before)
        end=a[j-1].end() if j>i else start
        old=before[start:end];new=' '.join(b[k:l])
        marked=('{~~'+old+'~>'+review.flow(new,old)+'~~}' if old and new else
                '{--'+old+'--}' if old else '{++'+new+' ++}')
        changes.append((start,end,old,new,marked))
    result=replace(before,changes,markup=True)
    assert review.reject(result)==before
    return result


def restore_minor(source,report):
    """Undo only checked, exact-context comma/article edits for baseline checking."""
    for header,marked in passages(report,checked=True):
        changes=list(edits(marked))
        if not changes or any(not is_minor(old,new) for _,_,old,new,_ in changes):
            raise ValueError('Non-minor edit in checked minor report: '+header)
        before,after=review.reject(marked),review.accept(marked)
        first,last=line_range(header)
        lines=source.splitlines(keepends=True)
        begin=sum(map(len,lines[:first-1]));end=sum(map(len,lines[:last]))-1
        if source[begin:end]!=after or before.count('\n')!=after.count('\n'):
            raise ValueError('Missing/misaligned implemented minor excerpt: '+header)
        source=source[:begin]+before+source[end:]
    return source


def split(source,report):
    lines=source.splitlines(keepends=True);offsets=[0]
    for line in lines:offsets.append(offsets[-1]+len(line))
    blocks=[];selected=[];conflicts=[]
    for header,marked in passages(report):
        first,last=line_range(header)
        begin,end=offsets[first-1],offsets[last]-1
        raw=review.reject(marked)
        assert source[begin:end]==raw,header
        changes=list(edits(marked,begin))
        blocks.append((header,begin,end,raw,changes))
        for change in changes:
            if not is_minor(change[2],change[3]):continue
            a,b,old,new,marked=change
            if not new and old.casefold() in ('a','an','the') and a>0 and source[a-1]==' ':
                change=(a-1,b,' '+old,new,'{-- '+old+'--}')
            matches=[p for p in selected if overlaps(change,p)]
            if matches:
                if any(p[:4]!=change[:4] for p in matches):conflicts.append((header,change,matches))
                continue
            selected.append(change)
    updated=replace(source,selected)
    minor=['# Minor corrections','','Comma and article corrections implemented in the Markdown paper. Broader wording remains pending.','','Where services disagreed, the definite article is retained for the previously identified assumption and closure.','']
    seen=set()
    for header,begin,end,raw,changes in blocks:
        key=(begin,end)
        if key in seen:continue
        chosen=[p for p in selected if begin<=p[0] and p[1]<=end]
        if not chosen:continue
        seen.add(key)
        minor+=report_entry(header,replace(raw,chosen,begin,markup=True),checked=True)
    minor='\n'.join(minor)
    assert restore_minor(updated,minor)==source
    pending=['# Wording suggestions','','For discussion; no edits applied from this report. Comma/article-only edits are recorded as implemented in MINOR_CORRECTIONS.md.','','[CriticMarkup](https://fletcher.github.io/MultiMarkdown-6/syntax/critic.html).','']
    seen=set()
    for header,begin,end,raw,changes in blocks:
        remaining=[c for c in changes if not is_minor(c[2],c[3])]
        if not remaining:continue
        applied=[c for c in selected if begin<=c[0] and c[1]<=end]
        before=replace(raw,applied,begin)
        independent=[c for c in applied if not any(overlaps(c,p) for p in remaining)]
        after=replace(raw,remaining+independent,begin)
        marked=critic(before,after)
        if '{>>' in ''.join(c[4] for c in remaining):
            # Preserve service comments without inventing a replacement for them.
            marked += ''.join(c[4] for c in remaining if c[4].startswith('{>>'))
        if marked==before:continue
        key=(begin,end,marked)
        if key in seen:continue
        seen.add(key)
        pending+=report_entry(header,marked)
    return updated,minor,'\n'.join(pending),len(selected),conflicts


def main():
    root=Path(__file__).resolve().parents[3]
    if (root/'latex/MINOR_CORRECTIONS.md').exists():
        raise SystemExit('Checked minor report already exists; refusing to overwrite correction history')
    source=root/'latex/PTS-rk.tex';wording=root/'latex/WORDING_SUGGESTIONS.md'
    updated,minor,pending,count,conflicts=split(source.read_text(),wording.read_text())
    files={source:updated,root/'latex/MINOR_CORRECTIONS.md':minor,wording:pending}
    patch=['*** Begin Patch']
    for path,after in files.items():
        if path.exists():
            patch+=['*** Update File: '+str(path)]
            diff=list(difflib.unified_diff(path.read_text().splitlines(),after.splitlines(),n=3))
            patch.extend('@@' if line.startswith('@@') else line for line in diff[2:])
        else:
            patch+=['*** Add File: '+str(path)]+['+'+line for line in after.splitlines()]
    patch+=['*** End Patch']
    print('\n'.join(patch))


if __name__=='__main__':main()
