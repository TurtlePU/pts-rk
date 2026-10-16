"""Presentation-only notation and whitespace normalization for the paper.

Literal listings, metadata, prose, text-macro arguments and TeX spacing commands
are not mathematics to rewrite. Script arguments are consumed before binary
operators are spaced, so e.g. →_β^∗ and N^+ remain attached.
"""
import re
import textwrap


def argument(s, i):
    while i < len(s) and s[i].isspace():
        i += 1
    if i == len(s):
        raise ValueError('Missing TeX argument')
    if s[i] != '{':
        m = re.match(r'\\(?:[A-Za-z]+|.)|.', s[i:])
        return m[0], i + len(m[0]), False
    start, depth = i + 1, 1
    i += 1
    while i < len(s):
        if s[i] == '\\':
            m = re.match(r'\\(?:[A-Za-z]+|.)', s[i:])
            i += len(m[0])
            continue
        if s[i] == '{':
            depth += 1
        elif s[i] == '}':
            depth -= 1
            if not depth:
                return s[start:i], i + 1, True
        i += 1
    raise ValueError('Unclosed TeX argument')


def normalize_notation(s):
    pattern = re.compile(r'\\mathsf\{rk\}\s*_|\\mathcal\{N\}\s*_|\\rk(?![A-Za-z])|\\chNat(?![A-Za-z])')
    out, end = [], 0
    for m in pattern.finditer(s):
        if m.start() < end:
            continue
        value, stop, _ = argument(s, m.end())
        name = 'chNat' if 'N' in m[0] else 'rk'
        out.extend((s[end:m.start()], '\\' + name + '{' + normalize_notation(value) + '}'))
        end = stop
    out.append(s[end:])
    return ''.join(out)


OPS = set('=:+-−×∪∩∧∨↔⇔→⇒↦⊢∈∉≤≥≠⊆⊂≡≜⋅⊔<>⇉↝∘≔↑⟶⟺≃⊬&')
BINARY = {'ac', 'oc', 'iffc', 'colon', 'mid', 'sim', 'simeq', 'cong', 'approx'}
SPACING = {'quad', 'qquad'}
TEXT = {'text', 'textrm', 'textsf', 'textsc', 'texttt', 'mathrm', 'mathsf',
        'mathcal', 'mathtt', 'operatorname', 'label', 'tag', 'begin', 'end'}


def formula(s):
    out, i = '', 0
    while i < len(s):
        c, name = s[i], ''
        j = i + 1
        if c == '\\':
            m = re.match(r'\\([A-Za-z]+|.)', s[i:], re.S)
            token, name = m[0], m[1]
            j = i + len(token)
            if name in TEXT:
                k = j
                while k < len(s) and s[k] in ' \t':
                    k += 1
                if k < len(s) and s[k] == '{':
                    _, j, _ = argument(s, k)
                    token = s[i:j]
        elif c == '{':
            value, j, _ = argument(s, i)
            token = '{' + formula(value) + '}'
        elif c in '_^':
            value, j, braced = argument(s, j)
            token = c + ('{' + formula(value) + '}' if braced else value)
            out = out.rstrip(' \t') + token
            i = j
            continue
        else:
            token = c
        if c in OPS or name in BINARY or name in SPACING:
            # The operator plus all its scripts is one source token.
            while True:
                k = j
                while k < len(s) and s[k].isspace():
                    k += 1
                if k == len(s) or s[k] not in '_^':
                    break
                value, j, braced = argument(s, k + 1)
                token += s[k] + ('{' + formula(value) + '}' if braced else value)
            unary = c in '+-−' and (not out.strip() or out.rstrip()[-1] in '([{,:=→⇒')
            line = out.rsplit('\n', 1)[-1]
            out = out.rstrip(' \t') if line.strip() else out
            out += ('' if unary or not line.strip() else ' ') + token
            if not unary:
                out += ' '
            i = j
            while i < len(s) and s[i] in ' \t':
                i += 1
            continue
        if c == ',':
            out = out.rstrip(' \t') + ', '
            i = j
            while i < len(s) and s[i] in ' \t':
                i += 1
            continue
        if c in ' \t':
            line = out.rsplit('\n', 1)[-1]
            if not line.strip() or not out.endswith(' '):
                out += c
        else:
            out += token
        i = j
    return '\n'.join(line.rstrip() for line in out.split('\n')).strip()


def format_source(s):
    # Keep literal Coq, Agda and quoted prompt listings byte-for-byte.
    parts = re.split(r'(?m)^((?:> )?```[^\n]*\n[\s\S]*?^(?:> )?```[^\n]*$)', s)
    for n in range(0, len(parts), 2):
        text = normalize_notation(parts[n])
        text = re.sub(r'(?<!\\)\$(?:\\.|[^$])*\$',
                      lambda m: '$' + formula(m[0][1:-1]) + '$', text)
        text = re.sub(r'\\\[([\s\S]*?)\\\]',
                      lambda m: '\\[\n' + textwrap.indent(formula(textwrap.dedent(m[1])), '    ') + '\n  \\]', text)
        lines, out, i = text.splitlines(keepends=True), [], 0
        while i < len(lines):
            m = re.match(r'^( *)%(mathpar|align\*?|gather\*?|multline\*?|tikzcd)\s*$', lines[i])
            if not m:
                out.append(lines[i]); i += 1
                continue
            base = len(m[1])
            out.append(lines[i]); i += 1
            body = []
            while i < len(lines) and (not lines[i].strip() or len(lines[i])-len(lines[i].lstrip()) > base):
                body.append(lines[i]); i += 1
            out.append(textwrap.indent(formula(textwrap.dedent(''.join(body))), ' ' * (base + 2)) + '\n')
            if body and not body[-1].strip():
                out.append('\n')
        parts[n] = ''.join(out)
    return ''.join(parts)
